import EgglogSemantics.Congruence.Read
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Subsume
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Source.Arity

/-! The compiled state read as a union-find. A row is an asserted `@UF(k, p)`, live or
stale; `Edge` (from `Read.lean`) is the live row. The facts here hold on every diagonal
target state whose equations are union-find rows over source-shaped terms. -/

namespace Egglog.Congruence

/-- The union-find row `@UF(k, p)` as a term. -/
abbrev ufRowT (k p : Term) : Term := .app ufName [k, p]

theorem ufRowT_inj {k p k' p' : Term} (h : ufRowT k p = ufRowT k' p') : k = k' ∧ p = p' := by
  have := Term.app.inj h
  simp only [List.cons.injEq, and_true] at this
  exact this.2

/-- The row `@UF(k, p)` is asserted, live or stale. -/
def Row (d : Database) (k p : Term) : Prop := (ufRowT k p, ufRowT k p) ∈ d.eqs

/-- The keys of the union-find: the terms with a row. -/
def Keys (d : Database) : Set Term := {k | ∃ p, Row d k p}

/-- Every equation is the reflexive pair of a union-find row. -/
def UfOnly (d : Database) : Prop := ∀ q ∈ d.eqs, ∃ k p, q = (ufRowT k p, ufRowT k p)

/-- No endpoint of a row applies the union-find name. -/
def EndsFree (d : Database) : Prop :=
  ∀ k p, Row d k p → ¬ Term.Mentions ufName k ∧ ¬ Term.Mentions ufName p

/-- The rows read as equations. -/
def view (d : Database) : Database := ⟨{q | Row d q.1 q.2}, ∅⟩

/-- The live rows read as equations. -/
def liveView (d : Database) : Database := ⟨{q | Edge d q.1 q.2}, ∅⟩

theorem Row.mem_terms {d : Database} {k p : Term} (h : Row d k p) : ufRowT k p ∈ d.terms :=
  ⟨_, h, Or.inl (Term.self_mem_subterms _)⟩

theorem Row.key_mem_terms {d : Database} {k p : Term} (h : Row d k p) : k ∈ d.terms :=
  ⟨_, h, Or.inl (.arg (by simp) (.refl _))⟩

theorem Row.mem_keys {d : Database} {k p : Term} (h : Row d k p) : k ∈ Keys d := ⟨p, h⟩

theorem Row.mono {d e : Database} (h : d.eqs ⊆ e.eqs) {k p : Term} (hr : Row d k p) :
    Row e k p := h hr

theorem Keys.mono {d e : Database} (h : d.eqs ⊆ e.eqs) : Keys d ⊆ Keys e :=
  fun _ ⟨p, hr⟩ => ⟨p, hr.mono h⟩

theorem Keys.subset_terms (d : Database) : Keys d ⊆ d.terms :=
  fun _ ⟨_, hr⟩ => hr.key_mem_terms

@[simp] theorem view_eqs (d : Database) : (view d).eqs = {q | Row d q.1 q.2} := rfl
@[simp] theorem view_subsumed (d : Database) : (view d).subsumed = ∅ := rfl
@[simp] theorem liveView_eqs (d : Database) : (liveView d).eqs = {q | Edge d q.1 q.2} := rfl
@[simp] theorem liveView_subsumed (d : Database) : (liveView d).subsumed = ∅ := rfl

theorem view_mono {d e : Database} (h : d.eqs ⊆ e.eqs) : (view d).eqs ⊆ (view e).eqs :=
  fun _ hq => hq.mono h

/-- A row is an equation of the view. -/
theorem Row.cong_view {d : Database} {k p : Term} (hr : Row d k p) : Cong (view d) k p :=
  .direct hr

/-- A live row is an equation of the live view. -/
theorem Edge.cong_liveView {d : Database} {k p : Term} (he : Edge d k p) :
    Cong (liveView d) k p := .direct he

/-- A term that is the row's own head is the row: a union-find row never sits inside a
source-shaped endpoint. -/
theorem uf_mem_terms_iff {d : Database} (hu : UfOnly d) (hf : EndsFree d) {k p : Term} :
    ufRowT k p ∈ d.terms ↔ Row d k p := by
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨k', p', rfl⟩ := hu q hq
    have hrow : Row d k' p' := hq
    have inside : ∀ {t : Term}, ufRowT k p ∈ t.subterms → t = k' ∨ t = p' → False := by
      intro t ht hkp
      have hm : Term.Mentions ufName t := ⟨[k, p], ht⟩
      rcases hkp with rfl | rfl
      · exact (hf _ _ hrow).1 hm
      · exact (hf _ _ hrow).2 hm
    have main : ufRowT k p ∈ (ufRowT k' p').subterms → Row d k p := by
      intro h
      rw [Term.subterms_app] at h
      rcases Set.mem_insert_iff.mp h with h | h
      · obtain ⟨rfl, rfl⟩ : k = k' ∧ p = p' := by
          have := Term.app.inj h
          simp only [List.cons.injEq, and_true] at this
          exact this.2
        exact hrow
      · obtain ⟨t, ht, hs⟩ := Set.mem_iUnion₂.mp h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        exact (inside hs ht).elim
    exact hs.elim main main
  · exact Row.mem_terms

/-- Every held term is a row or a subterm of a key. -/
theorem mem_terms_iff {d : Database} (hu : UfOnly d)
    (hself : ∀ k p, Row d k p → Row d p p) {t : Term} :
    t ∈ d.terms ↔ (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
  constructor
  · rintro ⟨q, hq, hs⟩
    obtain ⟨k, p, rfl⟩ := hu q hq
    have hrow : Row d k p := hq
    have main : t ∈ (ufRowT k p).subterms →
        (∃ k p, Row d k p ∧ t = ufRowT k p) ∨ ∃ k ∈ Keys d, t ∈ k.subterms := by
      intro h
      rw [Term.subterms_app] at h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · exact Or.inl ⟨k, p, hrow, rfl⟩
      · obtain ⟨u, hu', hs'⟩ := Set.mem_iUnion₂.mp h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
        rcases hu' with rfl | rfl
        · exact Or.inr ⟨u, hrow.mem_keys, hs'⟩
        · exact Or.inr ⟨u, (hself _ _ hrow).mem_keys, hs'⟩
    exact hs.elim main main
  · rintro (⟨k, p, hr, rfl⟩ | ⟨k, ⟨p, hr⟩, hs⟩)
    · exact hr.mem_terms
    · exact ⟨_, hr, Or.inl (.arg (by simp) hs)⟩

/-- A live row is an asserted row that is not marked. -/
theorem edge_iff {d : Database} (hd : d.Diag) (hu : UfOnly d) (hf : EndsFree d) {k p : Term} :
    Edge d k p ↔ Row d k p ∧ ufRowT k p ∉ d.subsumed := by
  unfold Edge Database.live
  simp only [Set.mem_setOf_eq, Cong.iff_eq_and_mem_of_diag hd, true_and,
    uf_mem_terms_iff hu hf]
  constructor
  · rintro ⟨hr, hn⟩
    refine ⟨hr, fun hs => hn ⟨_, hs, Database.SameRow.self_app (Database.toCong hr.mem_terms)⟩⟩
  · rintro ⟨hr, hn⟩
    refine ⟨hr, ?_⟩
    rintro ⟨u, hu', hs⟩
    rw [← hs.eq_of_diag hd] at hu'
    exact hn hu'

theorem Edge.row {d : Database} (hd : d.Diag) (hu : UfOnly d) (hf : EndsFree d) {k p : Term}
    (h : Edge d k p) : Row d k p := ((edge_iff hd hu hf).mp h).1

theorem Edge.of_row {d : Database} (hd : d.Diag) (hu : UfOnly d) (hf : EndsFree d)
    {k p : Term} (hr : Row d k p) (hn : ufRowT k p ∉ d.subsumed) : Edge d k p :=
  (edge_iff hd hu hf).mpr ⟨hr, hn⟩

/-- Live rows persist when rows grow and nothing new is marked. -/
theorem Edge.mono {d e : Database} (hd : d.Diag) (hu : UfOnly d) (hf : EndsFree d)
    (he : e.Diag) (hue : UfOnly e) (hfe : EndsFree e)
    (heqs : d.eqs ⊆ e.eqs) (hsub : e.subsumed ⊆ d.subsumed) {k p : Term} (h : Edge d k p) :
    Edge e k p := by
  rw [edge_iff hd hu hf] at h
  exact Edge.of_row he hue hfe (h.1.mono heqs) (fun hs => h.2 (hsub hs))

/-- The live-row equations are among the row equations. -/
theorem liveView_subset_view {d : Database} (hd : d.Diag) (hu : UfOnly d) (hf : EndsFree d) :
    (liveView d).eqs ⊆ (view d).eqs := fun _ hq => Edge.row hd hu hf hq

/-- An application of a source name is live exactly when it is held, since only
union-find rows are ever marked. -/
theorem app_live_iff {d : Database} (hd : d.Diag)
    (hmarks : ∀ t ∈ d.subsumed, ∃ k p, t = ufRowT k p) {f : FnName} (hf : f ≠ ufName)
    {ts : List Term} : Term.app f ts ∈ d.live ↔ Term.app f ts ∈ d.terms := by
  unfold Database.live
  simp only [Set.mem_setOf_eq, Cong.iff_eq_and_mem_of_diag hd, true_and]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨u, hu, hs⟩
    obtain ⟨k, p, rfl⟩ := hmarks u hu
    have := hs.eq_of_diag hd
    exact hf (Term.app.inj this).1

/-- A literal is live exactly when it is held. -/
theorem lit_live_iff {d : Database} (hd : d.Diag) {l : Lit} :
    Term.lit l ∈ d.live ↔ Term.lit l ∈ d.terms := by
  unfold Database.live
  simp only [Set.mem_setOf_eq, Cong.iff_eq_and_mem_of_diag hd, true_and]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨u, _, f, as, bs, hl, _, _⟩
    cases hl

/-- Representatives of a diagonal state are all of its terms. -/
theorem mem_reps_of_diag {d : Database} (hd : d.Diag) {t : Term} (ht : t ∈ d.terms) :
    t ∈ d.reps := by
  rw [hd.reps_eq_terms]; exact ht

/-- The union-find name is generated. -/
theorem atPrefix_ufName : "@".isPrefixOf ufName = true := by
  rw [ufName, String.isPrefixOf, String.startsWith_string_iff,
    show ("@").toList = ['@'] from by decide, show ("@UF").toList = ['@', 'U', 'F'] from by decide]
  exact ⟨['U', 'F'], rfl⟩

/-- A source-shaped term never applies the union-find name. -/
theorem not_mentions_uf_of_ctorsIn {P : Program} (hdom : P.Fragment) {t : Term}
    (ht : Term.CtorsIn P t) : ¬ Term.Mentions ufName t := by
  rintro ⟨args, hs⟩
  have hmem : (ufName, args.length) ∈ P.ctors := ht ufName args hs
  exact noAt_of_mem_ctors hdom hmem atPrefix_ufName

end Egglog.Congruence
