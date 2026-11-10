import EgglogSemantics.Proofs.Congruence.Target
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Representatives
import EgglogSemantics.Proofs.SemanticCong
import EgglogSemantics.Proofs.SourceMeaning

/-! The simulation relation between a source state and its compiled state, the canonical
(rebuilt) form of a compiled state, and the reading of source terms at a canonical state:
every key has one live edge, to the representative of its source class. -/

namespace Egglog.Congruence

/-- `d` is the compiled image of `src`: a diagonal union-find whose rows, read as
equations, generate exactly the source congruence; the keys are the source terms;
edges go down the term order; a stale row has a strictly smaller replacement; and the
live rows alone already generate every row. -/
structure Rel (src d : Database) : Prop where
  diag : d.Diag
  ufOnly : UfOnly d
  finite : d.eqs.Finite
  marks : ∀ t ∈ d.subsumed, ∃ k p q, t = ufRowT k p ∧ Row d k p ∧ Row d k q ∧ Row d p q ∧
    Term.blt q p = true
  down : ∀ k p, Row d k p → p = k ∨ Term.blt p k = true
  selfLoop : ∀ k p, Row d k p → Row d k k ∧ Row d p p
  keys : Keys d = src.terms
  avoids : ∀ t ∈ src.terms, ¬ Term.Mentions ufName t
  cong : ∀ a b, Cong src a b ↔ Cong (view d) a b
  liveCong : ∀ k p, Row d k p → Cong (liveView d) k p
  srcSubsumed : src.subsumed = ∅

/-- The rebuild fixpoint: one live edge per key, to a root, and congruent applications
share their root. -/
structure Canon (d : Database) : Prop where
  unique : ∀ k p q, Edge d k p → Edge d k q → p = q
  root : ∀ k p, Edge d k p → Edge d p p
  congr : ∀ f as bs rs y z, Term.app f as ∈ d.live → Term.app f bs ∈ d.live →
    List.Forall₂ (Edge d) as rs → List.Forall₂ (Edge d) bs rs →
    Edge d (.app f as) y → Edge d (.app f bs) z → y = z

/-- The term order as a strict order, for well-founded arguments over finite sets. -/
instance bltIsStrictOrder : IsStrictOrder Term (fun s t => Term.blt s t = true) where
  irrefl := fun t => by simp
  trans := fun a b c => Term.blt_trans a b c

namespace Rel

variable {src d : Database} (h : Rel src d)
include h

theorem parent_mem_keys {k p : Term} (hr : Row d k p) : p ∈ Keys d :=
  ⟨p, (h.selfLoop k p hr).2⟩

theorem key_mem_src {k : Term} (hk : k ∈ Keys d) : k ∈ src.terms := h.keys ▸ hk

theorem mem_keys_of_src {k : Term} (hk : k ∈ src.terms) : k ∈ Keys d := h.keys ▸ hk

theorem endsFree : EndsFree d := fun k p hr =>
  ⟨h.avoids k (h.key_mem_src hr.mem_keys), h.avoids p (h.key_mem_src (h.parent_mem_keys hr))⟩

theorem marks_uf : ∀ t ∈ d.subsumed, ∃ k p, t = ufRowT k p := fun t ht =>
  let ⟨k, p, _, he, _⟩ := h.marks t ht
  ⟨k, p, he⟩

theorem edge_iff {k p : Term} : Edge d k p ↔ Row d k p ∧ ufRowT k p ∉ d.subsumed :=
  Congruence.edge_iff h.diag h.ufOnly h.endsFree

theorem row_of_edge {k p : Term} (he : Edge d k p) : Row d k p := (h.edge_iff.mp he).1

theorem edge_of_row {k p : Term} (hr : Row d k p) (hn : ufRowT k p ∉ d.subsumed) :
    Edge d k p := h.edge_iff.mpr ⟨hr, hn⟩

theorem key_of_edge {k p : Term} (he : Edge d k p) : k ∈ Keys d := (h.row_of_edge he).mem_keys

theorem parent_of_edge {k p : Term} (he : Edge d k p) : p ∈ Keys d :=
  h.parent_mem_keys (h.row_of_edge he)

theorem terms_finite : d.terms.Finite := Database.finite_terms h.finite

theorem keys_finite : (Keys d).Finite := h.terms_finite.subset (Keys.subset_terms d)

theorem src_terms_finite : src.terms.Finite := h.keys ▸ h.keys_finite

theorem src_hasReps : src.HasReps := Database.hasReps_of_finite_terms h.src_terms_finite

theorem keys_subterm {k s : Term} (hk : k ∈ Keys d) (hs : s ∈ k.subterms) : s ∈ Keys d :=
  h.mem_keys_of_src (src.subtermClosed k (h.key_mem_src hk) hs)

/-- A row relates congruent source terms. -/
theorem row_cong {k p : Term} (hr : Row d k p) : Cong src k p :=
  (h.cong k p).mpr (.direct hr)

theorem edge_cong {k p : Term} (he : Edge d k p) : Cong src k p := h.row_cong (h.row_of_edge he)

theorem cong_self_of_key {k : Term} (hk : k ∈ Keys d) : Cong src k k :=
  Database.toCong (h.key_mem_src hk)

/-- The live rows generate the source congruence as well. -/
theorem liveCong_iff (a b : Term) : Cong src a b ↔ Cong (liveView d) a b := by
  rw [h.cong]
  constructor
  · exact fun hab => Cong.replay (D := view d) (E := liveView d)
      (fun q hq => h.liveCong q.1 q.2 hq) hab
  · exact Cong.mono_eqs (liveView_subset_view h.diag h.ufOnly h.endsFree)

/-- Every held term is a union-find row or a source term. -/
theorem mem_terms_iff {t : Term} :
    t ∈ d.terms ↔ (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ t ∈ src.terms := by
  rw [Congruence.mem_terms_iff h.ufOnly (fun k p hr => (h.selfLoop k p hr).2)]
  apply or_congr_right
  constructor
  · rintro ⟨k, hk, hs⟩
    exact h.key_mem_src (h.keys_subterm hk hs)
  · intro ht
    exact ⟨t, h.mem_keys_of_src ht, Term.self_mem_subterms t⟩

theorem src_mem_terms {t : Term} (ht : t ∈ src.terms) : t ∈ d.terms :=
  h.mem_terms_iff.mpr (Or.inr ht)

theorem src_mem_reps {t : Term} (ht : t ∈ src.terms) : t ∈ d.reps :=
  mem_reps_of_diag h.diag (h.src_mem_terms ht)

theorem app_live_iff {f : FnName} (hf : f ≠ ufName) {ts : List Term} :
    Term.app f ts ∈ d.live ↔ Term.app f ts ∈ src.terms := by
  rw [Congruence.app_live_iff h.diag h.marks_uf hf, h.mem_terms_iff]
  constructor
  · rintro (⟨k, p, _, he⟩ | ht)
    · exact (hf (Term.app.inj he).1).elim
    · exact ht
  · exact Or.inr

theorem lit_live_iff {l : Lit} : Term.lit l ∈ d.live ↔ Term.lit l ∈ src.terms := by
  rw [Congruence.lit_live_iff h.diag, h.mem_terms_iff]
  constructor
  · rintro (⟨k, p, _, he⟩ | ht)
    · cases he
    · exact ht
  · exact Or.inr

/-- The head of a key is a source name. -/
theorem key_ne_uf {f : FnName} {ts : List Term} (hk : Term.app f ts ∈ Keys d) : f ≠ ufName := by
  rintro rfl
  exact h.avoids _ (h.key_mem_src hk) (Term.mentions_head _ _)

theorem app_live_of_edge {f : FnName} {ts : List Term} {e : Term}
    (he : Edge d (.app f ts) e) : Term.app f ts ∈ d.live :=
  (h.app_live_iff (h.key_ne_uf (h.key_of_edge he))).mpr (h.key_mem_src (h.key_of_edge he))

theorem app_mem_src_of_mem_terms {f : FnName} (hf : f ≠ ufName) {ts : List Term}
    (ht : Term.app f ts ∈ d.terms) : Term.app f ts ∈ src.terms := by
  rcases h.mem_terms_iff.mp ht with ⟨k, p, _, he⟩ | ht
  · exact (hf (Term.app.inj he).1).elim
  · exact ht

/-- The least parent of a key is live. -/
theorem least_parent {k : Term} (hk : k ∈ Keys d) :
    ∃ p, Edge d k p ∧ ∀ q, Row d k q → p = q ∨ Term.blt p q = true := by
  classical
  let S : Set Term := {p | Row d k p}
  have hS : S.Finite := h.keys_finite.subset fun p hp => h.parent_mem_keys hp
  obtain ⟨p₀, hp₀⟩ := hk
  obtain ⟨p, hp, hmin⟩ := (Set.wellFoundedOn_iff.mp
    (hS.wellFoundedOn (r := fun s t => Term.blt s t = true))).has_min S ⟨p₀, hp₀⟩
  refine ⟨p, h.edge_of_row hp fun hs => ?_, fun q hq => ?_⟩
  · obtain ⟨k', p', q, heq, _, hkq, _, hlt⟩ := h.marks _ hs
    obtain ⟨rfl, rfl⟩ : k' = k ∧ p' = p := by
      have := Term.app.inj heq
      simp only [List.cons.injEq, and_true] at this
      exact ⟨this.2.1.symm, this.2.2.symm⟩
    exact hmin q hkq ⟨hlt, hkq, hp⟩
  · by_cases hpq : p = q
    · exact Or.inl hpq
    · rcases Term.blt_total p q hpq with hlt | hlt
      · exact Or.inr hlt
      · exact (hmin q hq ⟨hlt, hq, hp⟩).elim

theorem exists_edge {k : Term} (hk : k ∈ Keys d) : ∃ p, Edge d k p :=
  let ⟨p, hp, _⟩ := h.least_parent hk
  ⟨p, hp⟩

theorem edge_down {k p : Term} (he : Edge d k p) : p = k ∨ Term.blt p k = true :=
  h.down k p (h.row_of_edge he)

/-- A literal's only edge is its self-loop. -/
theorem edge_lit {l : Lit} {p : Term} (hw : src.WF) (he : Edge d (.lit l) p) : p = Term.lit l := by
  have hc := h.edge_cong he
  exact (InferredFacts.infers_eq_of_isLit hw (InferredFacts.congr_iff_infers.mp hc)
    (Or.inl rfl)).symm

end Rel

/-! ### Roots at a canonical state -/

/-- The live parent of a key, and the term itself for a non-key. -/
noncomputable def root (d : Database) (k : Term) : Term :=
  open Classical in
  if hk : ∃ p, Edge d k p then hk.choose else k

theorem reprList_root_of_keys {d : Database} : ∀ {as : List Term},
    (∀ a ∈ as, Repr d a (root d a)) → ReprList d as (as.map (root d))
  | [], _ => .nil
  | a :: as, hr => .cons (hr a (by simp))
      (reprList_root_of_keys (fun b hb => hr b (by simp [hb])))

namespace Rel

variable {src d : Database} (h : Rel src d) (hc : Canon d)
include h hc

omit hc in
theorem edge_root {k : Term} (hk : k ∈ Keys d) : Edge d k (root d k) := by
  have hex : ∃ p, Edge d k p := h.exists_edge hk
  unfold root
  rw [dif_pos hex]
  exact hex.choose_spec

theorem root_eq {k p : Term} (he : Edge d k p) : root d k = p :=
  hc.unique k _ p (h.edge_root (h.key_of_edge he)) he

omit hc in
theorem root_mem_keys {k : Term} (hk : k ∈ Keys d) : root d k ∈ Keys d :=
  h.parent_of_edge (h.edge_root hk)

theorem edge_root_root {k : Term} (hk : k ∈ Keys d) :
    Edge d (root d k) (root d k) := hc.root _ _ (h.edge_root hk)

theorem root_root {k : Term} (hk : k ∈ Keys d) : root d (root d k) = root d k :=
  h.root_eq hc (h.edge_root_root hc hk)

omit hc in
theorem root_lit (hw : src.WF) (l : Lit) (hk : Term.lit l ∈ Keys d) :
    root d (.lit l) = .lit l :=
  h.edge_lit hw (h.edge_root hk)

omit hc in
/-- A key is read to its root. -/
theorem repr_root (hw : src.WF) : ∀ {k : Term}, k ∈ Keys d → Repr d k (root d k) := by
  intro k
  induction k using Term.recTerm with
  | lit l =>
    intro hk
    rw [h.root_lit hw l hk]
    exact .lit
  | app f args ih =>
    intro hk
    have hargs : ∀ a ∈ args, a ∈ Keys d := fun a ha =>
      h.keys_subterm hk (Term.arg_subterms ha a.self_mem_subterms)
    refine .app (reprList_root_of_keys fun a ha => ih a ha (hargs a ha))
      (Keys.subset_terms d hk) ?_ (h.edge_root hk)
    exact List.forall₂_map_self fun a ha => h.edge_root (hargs a ha)

/-- Readings are unique at a canonical state. -/
theorem repr_unique : ∀ {t e : Term}, Repr d t e → ∀ e', Repr d t e' → e = e' := by
  intro t e ht
  induction ht using Repr.rec (motive_2 := fun as rs _ => ∀ rs', ReprList d as rs' → rs = rs')
    with
  | lit => intro e' h'; cases h'; rfl
  | @app f as bs rs e hl hb hedges he ih =>
    intro e' h'
    cases h' with
    | @app _ _ bs' rs' _ hl' hb' hedges' he' =>
      obtain rfl := ih _ hl'
      exact hc.congr f bs bs' rs e e' (h.app_live_of_edge he) (h.app_live_of_edge he')
        hedges hedges' he he'
  | nil => rename_i rs' h'; cases h'; rfl
  | cons _ _ ih ihs =>
    rename_i rs' h'
    cases h' with
    | cons h₁ hs₁ => rw [ih _ h₁, ihs _ hs₁]

theorem reprList_unique : ∀ {as rs rs' : List Term}, ReprList d as rs → ReprList d as rs' →
    rs = rs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons hr hs, .cons hr' hs' => by
      rw [h.repr_unique hc hr _ hr', reprList_unique hs hs']

omit h hc in
theorem reprList_mem : ∀ {as rs : List Term}, ReprList d as rs → ∀ {a : Term}, a ∈ as →
    ∃ e, Repr d a e
  | _ :: _, _, .cons hr hs, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨_, hr⟩
      · exact reprList_mem hs ha

/-- Congruent source terms read to one id. -/
theorem cong_repr (hw : src.WF) {a b : Term} (hab : Cong src a b) :
    ∃ e, Repr d a e ∧ Repr d b e := by
  have hl := (h.liveCong_iff a b).mp hab
  clear hab
  induction hl using Cong.rec
    (motive_2 := fun as bs _ => ∃ rs, ReprList d as rs ∧ ReprList d bs rs) with
  | @direct a b hq =>
    have he : Edge d a b := hq
    refine ⟨b, ?_, ?_⟩
    · have := h.repr_root hw (h.key_of_edge he)
      rwa [h.root_eq hc he] at this
    · have := h.repr_root hw (h.parent_of_edge he)
      rwa [h.root_eq hc (hc.root _ _ he)] at this
  | child _ hs ih =>
    obtain ⟨e, he, _⟩ := ih
    cases he with
    | app hl _ _ _ =>
      obtain ⟨e', he'⟩ := reprList_mem hl hs
      exact ⟨e', he', he'⟩
  | symm _ ih =>
    obtain ⟨e, h₁, h₂⟩ := ih
    exact ⟨e, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e, h₁, h₂⟩ := ih₁
    obtain ⟨e', h₃, h₄⟩ := ih₂
    obtain rfl := h.repr_unique hc h₂ _ h₃
    exact ⟨e, h₁, h₄⟩
  | @congr f as bs _ _ ih₁ ih₂ =>
    obtain ⟨e, he, _⟩ := ih₁
    obtain ⟨rs, hl₁, hl₂⟩ := ih₂
    cases he with
    | @app _ _ cs rs₀ _ hl hb hedges he' =>
      obtain rfl := h.reprList_unique hc hl hl₁
      exact ⟨e, .app hl₁ hb hedges he', .app hl₂ hb hedges he'⟩
  | nil => exact ⟨[], .nil, .nil⟩
  | cons _ _ ih ihs =>
    obtain ⟨e, h₁, h₂⟩ := ih
    obtain ⟨rs, hs₁, hs₂⟩ := ihs
    exact ⟨e :: rs, .cons h₁ hs₁, .cons h₂ hs₂⟩

/-- Congruent keys share their root. -/
theorem root_eq_of_cong (hw : src.WF) {a b : Term} (ha : a ∈ Keys d) (hb : b ∈ Keys d)
    (hab : Cong src a b) : root d a = root d b := by
  obtain ⟨e, h₁, h₂⟩ := h.cong_repr hc hw hab
  rw [h.repr_unique hc (h.repr_root hw ha) _ h₁, h.repr_unique hc (h.repr_root hw hb) _ h₂]

/-- The live edge of a key goes to the representative of its source class. -/
theorem edge_iff_rep (hw : src.WF) {k p : Term} (hk : k ∈ Keys d) :
    Edge d k p ↔ p ∈ src.reps ∧ Cong src k p := by
  constructor
  · intro he
    refine ⟨⟨h.key_mem_src (h.parent_of_edge he), fun s hs hsp hlt => ?_⟩, h.edge_cong he⟩
    have hroot : root d s = p := by
      rw [h.root_eq_of_cong hc hw (h.mem_keys_of_src hs) (h.parent_of_edge he) hsp]
      exact h.root_eq hc (hc.root _ _ he)
    have hes : Edge d s p := hroot ▸ h.edge_root (h.mem_keys_of_src hs)
    rcases h.edge_down hes with rfl | hps
    · simp at hlt
    · rw [Term.blt_asymm _ _ hps] at hlt
      exact Bool.false_ne_true hlt
  · rintro ⟨hp, hkp⟩
    have he := h.edge_root hk
    have hr : root d k ∈ src.reps ∧ Cong src k (root d k) :=
      ⟨⟨h.key_mem_src (h.parent_of_edge he), fun s hs hsp hlt => ?_⟩, h.edge_cong he⟩
    · have := Database.reps_eq_of_cong hr.1 hp (hr.2.symm.trans hkp)
      rwa [this] at he
    · have hroot : root d s = root d k := by
        rw [h.root_eq_of_cong hc hw (h.mem_keys_of_src hs) (h.parent_of_edge he) hsp]
        exact h.root_root hc hk
      have hes : Edge d s (root d k) := hroot ▸ h.edge_root (h.mem_keys_of_src hs)
      rcases h.edge_down hes with heq | hps
      · rw [heq] at hlt; simp at hlt
      · rw [Term.blt_asymm _ _ hps] at hlt
        exact Bool.false_ne_true hlt

end Rel

/-! ### The empty states -/

/-- Nothing is congruent in a state without equations. -/
theorem cong_empty_eqs {d : Database} (hd : d.eqs = ∅) {a b : Term} (h : Cong d a b) : False := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct hp => rw [hd] at hp; exact hp
  | child _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

theorem keys_empty : Keys Database.empty = ∅ := by
  ext k
  constructor
  · rintro ⟨p, hp⟩
    exact hp
  · intro h
    exact h.elim

/-- The empty states are related. -/
theorem rel_empty : Rel Database.empty Database.empty where
  diag := fun _ hq => hq.elim
  ufOnly := fun _ hq => hq.elim
  finite := Set.finite_empty
  marks := fun _ ht => ht.elim
  down := fun _ _ hr => hr.elim
  selfLoop := fun _ _ hr => hr.elim
  keys := by rw [keys_empty, Database.empty_terms]
  avoids := by intro t ht; rw [Database.empty_terms] at ht; exact ht.elim
  cong := fun a b => ⟨fun h => (cong_empty_eqs rfl h).elim, fun h => (cong_empty_eqs rfl h).elim⟩
  liveCong := fun _ _ hr => hr.elim
  srcSubsumed := rfl

/-- The empty state is canonical. -/
theorem canon_empty : Canon Database.empty where
  unique := fun _ _ _ he _ => (cong_empty_eqs rfl he.1).elim
  root := fun _ _ he => (cong_empty_eqs rfl he.1).elim
  congr := fun _ _ _ _ _ _ _ _ _ _ he _ => (cong_empty_eqs rfl he.1).elim

end Egglog.Congruence
