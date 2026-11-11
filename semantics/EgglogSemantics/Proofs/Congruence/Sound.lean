import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Atoms

/-! Soundness of the compiled queries: whenever the atoms of a flattened source pattern
match in a reading of the compiled state, the source pattern matches, with its ids
congruent to the source values. The reading is any database whose live edges and live
applications are sound for the source: the compiled state itself, and the compiled state
with subsumption forgotten, which the final check sees. -/

namespace Egglog.Congruence

/-- A database whose live rows and live applications are sound for the source. -/
structure Reads (src D : Database) : Prop where
  diag : D.Diag
  edge : ∀ k p, Edge D k p → Cong src k p ∧ k ∈ src.terms ∧ p ∈ src.terms
  app : ∀ f ts, f ≠ ufName → Term.app f ts ∈ D.live → Term.app f ts ∈ src.terms
  lit : ∀ l, Term.lit l ∈ D.live → Term.lit l ∈ src.terms

theorem Rel.reads {src d : Database} (h : Rel src d) : Reads src d where
  diag := h.diag
  edge := fun _ _ he => ⟨h.edge_cong he, h.key_mem_src (h.key_of_edge he),
    h.key_mem_src (h.parent_of_edge he)⟩
  app := fun _ _ hf hl => (h.app_live_iff hf).mp hl
  lit := fun _ hl => h.lit_live_iff.mp hl

/-- With subsumption forgotten every row is live; rows are still sound. -/
theorem Rel.reads_forget {src d : Database} (h : Rel src d) : Reads src d.forgetSubsumed where
  diag := h.diag.forgetSubsumed
  edge := by
    intro k p he
    have hmem : ufRowT k p ∈ d.terms := by
      have : ufRowT k p ∈ d.forgetSubsumed.live := he
      rw [Database.live_forgetSubsumed] at this
      exact ((Cong.iff_eq_and_mem_of_diag h.diag).mp this).2
    have hr : Row d k p := (uf_mem_terms_iff h.ufOnly h.endsFree).mp hmem
    exact ⟨h.row_cong hr, h.key_mem_src hr.mem_keys, h.key_mem_src (h.parent_mem_keys hr)⟩
  app := by
    intro f ts hf hl
    rw [Database.live_forgetSubsumed] at hl
    exact h.app_mem_src_of_mem_terms hf ((Cong.iff_eq_and_mem_of_diag h.diag).mp hl).2
  lit := by
    intro l hl
    rw [Database.live_forgetSubsumed] at hl
    have hmem := ((Cong.iff_eq_and_mem_of_diag h.diag).mp hl).2
    rcases h.mem_terms_iff.mp hmem with ⟨_, _, _, heq⟩ | ht
    · cases heq
    · exact ht

theorem evalList_of_forall₂ {σ : Env} : ∀ {es : List Expr} {ts : List Term},
    List.Forall₂ (fun e t => e.eval σ = some t) es ts → Expr.evalList es σ = some ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      rw [Expr.evalList_cons, h, Option.bind_some, evalList_of_forall₂ hs, Option.map_some]

/-- A source expression's names are source names. -/
def SrcNames (e : Expr) : Prop := ∀ g ∈ e.fns, g ≠ ufName

theorem srcNames_app {f : FnName} {args : List Expr} (h : SrcNames (.app f args)) :
    f ≠ ufName ∧ ∀ g ∈ Expr.fnsList args, g ≠ ufName :=
  ⟨h f (by simp [Expr.fns]), fun g hg => h g (by simp [Expr.fns, hg])⟩

theorem srcNames_cons {e : Expr} {es : List Expr} (h : ∀ g ∈ Expr.fnsList (e :: es), g ≠ ufName) :
    SrcNames e ∧ ∀ g ∈ Expr.fnsList es, g ≠ ufName :=
  ⟨fun g hg => h g (by simp [Expr.fnsList, hg]), fun g hg => h g (by simp [Expr.fnsList, hg])⟩

variable {src D : Database}

mutual

/-- If the atoms of a flattened expression match, the expression evaluates in the source
and its id is congruent to the value. -/
theorem sound_expr (hr : Reads src D) : ∀ (e : Expr) (n : Nat) {σ' σ : Env},
    e.OrderingFree → SrcNames e →
    (∀ v ∈ e.vars, Env.lookup v σ' = Env.lookup v σ) →
    (∀ v t, Env.lookup v σ = some t → t ∈ src.terms) →
    (∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches D p σ') →
    Expr.Matches D σ' (encodeQueryExprWith {} e n).1 →
    ∀ {i : Term}, (encodeQueryExprWith {} e n).1.eval σ' = some i →
    ∃ t, e.eval σ = some t ∧ Cong src t i
  | .lit l, n, σ', σ, _, _, _, _, _, hx, i, hi => by
      rw [flat_lit] at hx hi
      simp only [Expr.eval_lit, Option.some.injEq] at hi
      subst hi
      refine ⟨.lit l, rfl, Database.toCong (hr.lit l ?_)⟩
      cases hx with
      | lit hl => exact hl
  | .var v, n, σ', σ, _, _, hag, hσ, _, _, i, hi => by
      rw [flat_var] at hi
      simp only [Expr.eval_var] at hi
      rw [hag v (by simp)] at hi
      exact ⟨i, hi, Database.toCong (hσ v i hi)⟩
  | .min _ _, _, _, _, ho, _, _, _, _, _, _, _ => (Expr.not_orderingFree_min ho).elim
  | .app f args, n, σ', σ, ho, hnames, hag, hσ, hm, _, i, hi => by
      rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hlen := flatArgs_length args n
      rw [hflat] at hlen
      simp only at hlen
      rw [flat_app hflat] at hm hi
      simp only at hm hi
      obtain ⟨hf, hfns⟩ := srcNames_app hnames
      -- The application atom.
      have hA := hm (.expr (.app f (freshArgs next args.length))) (by simp)
      obtain ⟨as, _, has, hliveA⟩ := matches_app_iff.mp hA
      have hasrc : Term.app f as ∈ src.terms := hr.app f as hf hliveA
      -- The root atom.
      have hY := hm (.expr (ufRow (.app f (freshArgs next args.length))
        (.var (freshVar (next + args.length))))) (by simp)
      obtain ⟨ta, i', _, _, hta, hi', hey⟩ := matches_uf_iff.mp hY
      obtain rfl : ta = Term.app f as := by
        rw [Expr.eval_app_ctor, has] at hta
        exact (Option.some.inj hta).symm
      simp only [Expr.eval_var] at hi hi'
      obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
      -- The children.
      have hargs := sound_args hr args n (Expr.orderingFree_app ho) hfns (by simpa using hag) hσ
        (by
          intro p hp
          rw [hflat] at hp
          exact hm p (List.mem_append_left _ (List.mem_append_left _ hp)))
      rw [hflat] at hargs
      simp only at hargs
      have hasLen : as.length = args.length := by
        rw [Expr.evalList_length has, freshArgs_length]
      have hpoint : ∀ (j : Nat) (hj : j < args.length),
          ∃ t, args[j].eval σ = some t ∧ Cong src t (as[j]'(by omega)) := by
        intro j hj
        have hZ := hm (.expr (ufRow ((freshArgs next args.length)[j]'(by
          rw [freshArgs_length]; exact hj)) (xs[j]'(by omega)))) (by
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_cons_of_mem
          refine List.mem_map.mpr ⟨((freshArgs next args.length)[j]'(by
            rw [freshArgs_length]; exact hj), xs[j]'(by omega)), ?_, rfl⟩
          rw [List.mem_iff_getElem]
          refine ⟨j, by rw [List.length_zip, freshArgs_length, hlen, Nat.min_self]; exact hj, ?_⟩
          rw [List.getElem_zip])
        obtain ⟨a, ij, _, hxm, ha, hij, hedge⟩ := matches_uf_iff.mp hZ
        obtain ⟨a', ha', hev⟩ := Expr.getElem?_of_evalList has j
          (by rw [List.getElem?_eq_getElem (by rw [freshArgs_length]; exact hj)])
        rw [List.getElem?_eq_getElem (by omega)] at ha'
        obtain rfl : a' = as[j]'(by omega) := (Option.some.inj ha').symm
        obtain rfl : a = as[j]'(by omega) := Option.some.inj (ha.symm.trans hev)
        obtain ⟨t, ht, hti⟩ := (List.forall₂_iff_get.mp hargs).2 j hj (by omega) hxm hij
        exact ⟨t, ht, hti.trans (hr.edge _ _ hedge).1.symm⟩
      choose ts hts using fun j : Fin args.length => hpoint j j.2
      let tl : List Term := List.ofFn ts
      have htl : List.Forall₂ (fun e t => e.eval σ = some t) args tl := by
        rw [List.forall₂_iff_get]
        refine ⟨by simp [tl], fun j hj₁ hj₂ => ?_⟩
        simp only [List.get_eq_getElem, tl, List.getElem_ofFn]
        exact (hts ⟨j, hj₁⟩).1
      have hcl : CongList src tl as := by
        rw [CongList.forall₂, List.forall₂_iff_get]
        refine ⟨by simp [tl, hasLen], fun j hj₁ hj₂ => ?_⟩
        simp only [List.get_eq_getElem, tl, List.getElem_ofFn]
        exact (hts ⟨j, by simpa [tl] using hj₁⟩).2
      refine ⟨.app f tl, ?_, ?_⟩
      · rw [Expr.eval_app_ctor, evalList_of_forall₂ htl]; rfl
      · exact ((Cong.congr (Database.toCong hasrc) hcl.symm).symm.trans
          (hr.edge _ _ hey).1)

theorem sound_args (hr : Reads src D) : ∀ (es : List Expr) (n : Nat) {σ' σ : Env},
    Expr.OrderingFreeList es → (∀ g ∈ Expr.fnsList es, g ≠ ufName) →
    (∀ v ∈ Expr.varsList es, Env.lookup v σ' = Env.lookup v σ) →
    (∀ v t, Env.lookup v σ = some t → t ∈ src.terms) →
    (∀ p ∈ (encodeQueryArgsWith {} es n).2.1, Matches D p σ') →
    List.Forall₂ (fun e x => Expr.Matches D σ' x → ∀ {i : Term}, x.eval σ' = some i →
      ∃ t, e.eval σ = some t ∧ Cong src t i) es (encodeQueryArgsWith {} es n).1
  | [], _, _, _, _, _, _, _, _ => by rw [flatArgs_nil]; exact .nil
  | e :: es, n, σ', σ, ho, hnames, hag, hσ, hm => by
      obtain ⟨hoe, hoes⟩ := Expr.orderingFreeList_cons ho
      obtain ⟨hne, hnes⟩ := srcNames_cons hnames
      rcases h₁ : encodeQueryExprWith {} e n with ⟨x, ps, next⟩
      rcases h₂ : encodeQueryArgsWith {} es next with ⟨xs, qs, last⟩
      rw [flatArgs_cons h₁ h₂] at hm ⊢
      simp only at hm ⊢
      refine .cons ?_ ?_
      · intro hx i hi
        have := sound_expr hr e n hoe hne (fun v hv => hag v (by simp [hv])) hσ
          (fun p hp => hm p (List.mem_append_left _ (by rw [h₁] at hp; exact hp)))
        rw [h₁] at this
        exact this hx hi
      · have := sound_args hr es next hoes hnes (fun v hv => hag v (by simp [hv])) hσ
          (fun p hp => hm p (List.mem_append_right _ (by rw [h₂] at hp; exact hp)))
        rw [h₂] at this
        exact this

end

/-- An expression whose flattening matched also matches in the source, as its atom. -/
theorem sound_expr_matches (hr : Reads src D) (hX : src.subsumed = ∅) {e : Expr} {n : Nat}
    {σ' σ : Env} (ho : e.OrderingFree) (hnames : SrcNames e)
    (hag : ∀ v ∈ e.vars, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ p ∈ (encodeQueryExprWith {} e n).2.1, Matches D p σ')
    (hx : Expr.Matches D σ' (encodeQueryExprWith {} e n).1) :
    ∃ t i, e.eval σ = some t ∧ (encodeQueryExprWith {} e n).1.eval σ' = some i ∧
      Cong src t i ∧ Expr.Matches src σ e := by
  obtain ⟨i, hi⟩ := hx.eval_exists
  obtain ⟨t, ht, hti⟩ := sound_expr hr e n ho hnames hag hσ hm hx hi
  exact ⟨t, i, ht, hi, hti, (Expr.Matches.of_eval hX ho ht (hti.trans hti.symm)).2⟩

/-- If a compiled pattern's atoms match, the source pattern matches. -/
theorem sound_pattern (hr : Reads src D) (hX : src.subsumed = ∅) {p : Pattern} (n : Nat)
    (ho : p.OrderingFree) (hmono : p.monotoneB = true) (hsc : p.Scoped)
    (hnames : ∀ e, (p = .expr e ∨ ∃ e', p = .eq e e' ∨ p = .eq e' e) → SrcNames e)
    {σ' σ : Env} (hag : ∀ v ∈ p.vars, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ q ∈ (encodePatternWith {} p n).1, Matches D q σ') : Matches src p σ := by
  cases p with
  | expr e =>
    rw [pattern_expr] at hm
    simp only at hm
    cases e with
    | app f args =>
      rcases hflat : encodeQueryArgsWith {} args n with ⟨xs, ps, next⟩
      have hY := hm (.expr (ufRow (.app f (freshArgs next args.length))
        (.var (freshVar (next + args.length))))) (by rw [flat_app hflat]; simp)
      obtain ⟨_, i, _, hxm, _, _, _⟩ := matches_uf_iff.mp hY
      have hx : Expr.Matches D σ' (encodeQueryExprWith {} (.app f args) n).1 := by
        rw [flat_app hflat]; exact hxm
      obtain ⟨t, i, ht, _, _, hmatch⟩ := sound_expr_matches hr hX ho
        (hnames _ (Or.inl rfl)) hag hσ hm hx
      exact .atom hmatch
    | lit _ => exact hsc.elim
    | var _ => exact hsc.elim
    | min _ _ => exact hsc.elim
  | eq l r =>
    rcases h₁ : encodeQueryExprWith {} l n with ⟨x₁, ps, next⟩
    rcases h₂ : encodeQueryExprWith {} r next with ⟨x₂, qs, last⟩
    rw [pattern_eq h₁ h₂] at hm
    have hE := hm (.eq x₁ x₂) (by simp)
    obtain ⟨i₁, i₂, hm₁, hm₂, hi₁, hi₂, hc⟩ := matches_eq_iff.mp hE
    have hag₁ : ∀ v ∈ l.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    have hag₂ : ∀ v ∈ r.vars, Env.lookup v σ' = Env.lookup v σ := fun v hv =>
      hag v (by simp [Pattern.vars, hv])
    obtain ⟨t₁, i₁', ht₁, hi₁', hc₁, hl⟩ := sound_expr_matches hr hX ho.1
      (hnames l (Or.inr ⟨r, Or.inl rfl⟩)) hag₁ hσ
      (fun q hq => hm q (by rw [h₁] at hq; simp [hq])) (by rw [h₁]; exact hm₁)
    obtain ⟨t₂, i₂', ht₂, hi₂', hc₂, hrm⟩ := sound_expr_matches hr hX ho.2
      (hnames r (Or.inr ⟨l, Or.inr rfl⟩)) hag₂ hσ
      (fun q hq => hm q (by rw [h₂] at hq; simp [hq])) (by rw [h₂]; exact hm₂)
    rw [h₁] at hi₁'
    rw [h₂] at hi₂'
    simp only at hi₁' hi₂'
    obtain rfl : i₁ = i₁' := Option.some.inj (hi₁.symm.trans hi₁')
    obtain rfl : i₂ = i₂' := Option.some.inj (hi₂.symm.trans hi₂')
    have heq : i₁ = i₂ := hc.eq_of_diag hr.diag
    subst heq
    exact .equal hl hrm ht₁ ht₂ (hc₁.trans hc₂.symm)
  | ne l r => simp [Pattern.monotoneB] at hmono

/-- If a compiled query's atoms match, every source pattern matches. -/
theorem sound_query (hr : Reads src D) (hX : src.subsumed = ∅) {q : Query} (n : Nat)
    (ho : ∀ p ∈ q, p.OrderingFree) (hmono : ∀ p ∈ q, p.monotoneB = true)
    (hsc : ∀ p ∈ q, p.Scoped)
    (hnames : ∀ p ∈ q, ∀ e, (p = .expr e ∨ ∃ e', p = .eq e e' ∨ p = .eq e' e) → SrcNames e)
    {σ' σ : Env} (hag : ∀ v ∈ Query.vars q, Env.lookup v σ' = Env.lookup v σ)
    (hσ : ∀ v t, Env.lookup v σ = some t → t ∈ src.terms)
    (hm : ∀ p ∈ (encodeQueryWith {} q n).1, Matches D p σ') : ∀ p ∈ q, Matches src p σ := by
  induction q generalizing n with
  | nil => simp
  | cons p ps ih =>
    rcases h₁ : encodePatternWith {} p n with ⟨qs, next⟩
    rcases h₂ : encodeQueryWith {} ps next with ⟨rest, last⟩
    rw [query_cons h₁ h₂] at hm
    simp only at hm
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact sound_pattern hr hX n (ho _ (by simp)) (hmono _ (by simp)) (hsc _ (by simp))
        (hnames _ (by simp)) (fun v hv => hag v (by simp [hv])) hσ
        (fun q hq => hm q (by rw [h₁] at hq; exact List.mem_append_left _ hq))
    · exact ih next (fun p hp => ho p (by simp [hp])) (fun p hp => hmono p (by simp [hp]))
        (fun p hp => hsc p (by simp [hp])) (fun p hp => hnames p (by simp [hp]))
        (fun v hv => hag v (by simp [hv]))
        (fun q hq => hm q (by rw [h₂] at hq; exact List.mem_append_right _ hq)) p' hp'

end Egglog.Congruence
