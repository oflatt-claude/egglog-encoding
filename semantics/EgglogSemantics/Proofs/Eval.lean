import EgglogSemantics.Spec.Eval
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Congruence

namespace Egglog

variable {oldVars newVars : List Var}

/-! ### The terms depend on `eqs` alone

`Database.terms` is `{t | Cong db t t}` and `Cong` reads `eqs`, so an update to `sig`,
`env` or `rules` leaves the terms alone — and, at an environment whose values the database
holds, leaves `WF` alone too. Every field update the semantics performs is one of these. -/

@[simp] theorem Database.terms_setEnv {db : Database} {σ : Env} :
    ({ db with env := σ } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

@[simp] theorem Database.terms_setEnvRules {db : Database} {σ : Env} {R : Set Rule} :
    ({ db with env := σ, rules := R } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

theorem Database.terms_setSig {db : Database} {s : Signature} :
    ({ db with sig := s } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

theorem Database.terms_setRules {db : Database} {R : Set Rule} :
    ({ db with rules := R } : Database).terms = db.terms := terms_eq_of_eqs_eq rfl

/-- `WF` reads `eqs` and `env` only: a database agreeing in both is well formed too. -/
theorem Database.WF.congr {d₁ d₂ : Database} (hw : d₁.WF) (heqs : d₁.eqs = d₂.eqs)
    (henv : d₁.env = d₂.env) : d₂.WF := by
  have ht : d₁.terms = d₂.terms := Database.terms_eq_of_eqs_eq heqs
  refine ⟨fun b hb => ?_, fun p hp => ?_⟩
  · rw [← ht]
    exact hw.envInTerms b (by rw [henv]; exact hb)
  · exact hw.litsIsolated p (by rw [heqs]; exact hp)

/-- A table write adds values and inserts a row without changing the value invariants. -/
theorem Database.WF.putEntry {db : Database} (hw : db.WF) (e : Entry) :
    (db.putEntry e).WF := hw.addTerm e.atom

/-- Stored facts are values or well-formed function atoms. -/
def Term.Stored (sig : Signature) (t : Term) : Prop :=
  t.IsValue sig ∨ ∃ row : Entry, row.Valid sig ∧ t = row.atom

theorem Term.Stored.subterm {sig : Signature} {s t : Term}
    (ht : t.Stored sig) (hs : s ∈ t.subterms) : s.Stored sig := by
  rcases ht with ht | ⟨row, hr, rfl⟩
  · exact Or.inl (ht.subterm hs)
  · rw [Entry.atom, Term.subterms_app, Set.mem_insert_iff] at hs
    rcases hs with hs | hs
    · exact Or.inr ⟨row, hr, hs⟩
    · obtain ⟨t, ht, hs⟩ := Set.mem_iUnion₂.mp hs
      exact Or.inl ((hr.column_values t ht).subterm hs)

theorem Database.StoreOk.empty : Database.empty.StoreOk := by
  constructor <;> simp [Database.entries, Database.empty]

theorem Database.StoreOk.term {db : Database} (h : db.StoreOk) {t : Term}
    (ht : t ∈ db.terms) : t.Stored db.sig := by
  obtain ⟨p, hp, ht | ht⟩ := Database.mem_terms_iff.mp ht
  · rcases h.typed p hp with hv | ⟨row, hr, rfl⟩
    · exact Or.inl (hv.1.subterm ht)
    · exact Term.Stored.subterm (Or.inr ⟨row, hr, rfl⟩) ht
  · rcases h.typed p hp with hv | ⟨row, hr, rfl⟩
    · exact Or.inl (hv.2.subterm ht)
    · exact Term.Stored.subterm (Or.inr ⟨row, hr, rfl⟩) ht

/-- A typed table atom cannot occur properly inside another stored fact. -/
theorem Database.StoreOk.entry_of_held_atom {db : Database} (h : db.StoreOk)
    {row : Entry} (hr : row.Valid db.sig) (ht : row.atom ∈ db.terms) :
    row ∈ db.entries := by
  refine ⟨hr, ?_⟩
  obtain ⟨p, hp, ht | ht⟩ := Database.mem_terms_iff.mp ht
  · rcases h.typed p hp with hv | ⟨other, ho, rfl⟩
    · exact (hr.atom_not_value (hv.1.subterm ht)).elim
    · obtain rfl := hr.atom_subterm ho ht
      exact hp
  · rcases h.typed p hp with hv | ⟨other, ho, rfl⟩
    · exact (hr.atom_not_value (hv.2.subterm ht)).elim
    · obtain rfl := hr.atom_subterm ho ht
      exact hp

theorem Database.StoreOk.congr {d₁ d₂ : Database} (h : d₁.StoreOk)
    (hs : d₂.sig = d₁.sig) (he : d₂.eqs = d₁.eqs)
    (hv : ∀ b ∈ d₂.env, b.2.IsValue d₂.sig) : d₂.StoreOk := by
  have hr : d₂.entries = d₁.entries := by simp only [Database.entries, hs, he]
  refine ⟨?_, ?_, ?_, hv⟩
  · intro row hm
    simpa only [hs] using h.declared row (hr ▸ hm)
  · intro row hm t ht
    rw [Database.terms_eq_of_eqs_eq he]
    exact h.columns row (hr ▸ hm) t ht
  · intro p hp
    simpa only [hs] using h.typed p (he ▸ hp)

theorem Database.StoreOk.addTerm {db : Database} (h : db.StoreOk) (t : Term)
    (ht : t.Stored db.sig) : (db.addTerm t).StoreOk := by
  refine ⟨?_, ?_, ?_, h.envValues⟩
  · intro row hr
    obtain ⟨d, hd, hm, _⟩ := hr.1
    exact ⟨d, hd, hm⟩
  · intro row hr s hs
    exact Cong.subterm (.assert hr.2) (Term.arg_subterms hs (.refl _))
  · intro p hp
    rcases hp with rfl | hp
    · rcases ht with hv | ⟨row, hr, rfl⟩
      · exact Or.inl ⟨hv, hv⟩
      · exact Or.inr ⟨row, hr, rfl⟩
    · exact h.typed p hp

theorem Database.StoreOk.addEq {db : Database} (h : db.StoreOk) (a b : Term)
    (ha : a.IsValue db.sig) (hb : b.IsValue db.sig) : (db.addEq a b).StoreOk := by
  refine ⟨?_, ?_, ?_, h.envValues⟩
  · intro row hr
    obtain ⟨d, hd, hm, _⟩ := hr.1
    exact ⟨d, hd, hm⟩
  · intro row hr t ht
    exact Cong.subterm (.assert hr.2) (Term.arg_subterms ht (.refl _))
  · intro p hp
    rcases hp with rfl | hp
    · exact Or.inl ⟨ha, hb⟩
    · exact h.typed p hp

theorem Database.StoreOk.putEntry {db : Database} (h : db.StoreOk) (row : Entry)
    (hr : row.Valid db.sig) : (db.putEntry row).StoreOk :=
  h.addTerm row.atom (Or.inr ⟨row, hr, rfl⟩)

/-- Erasure retains every proper subterm of the removed atom through its columns. -/
theorem Database.mem_terms_eraseEntry_of_ne {db : Database} {row : Entry} {t : Term}
    (hne : t ≠ row.atom) (ht : t ∈ db.terms) :
    t ∈ (db.eraseEntry row).terms := by
  obtain ⟨p, hp, hs⟩ := Database.mem_terms_iff.mp ht
  by_cases he : p = (row.atom, row.atom)
  · subst p
    have hs : t ∈ row.atom.subterms := hs.elim id id
    rw [Entry.atom, Term.subterms_app, Set.mem_insert_iff] at hs
    rcases hs with hs | hs
    · exact (hne hs).elim
    · obtain ⟨v, hv, hs⟩ := Set.mem_iUnion₂.mp hs
      apply Cong.subterm (s := t) (t := v) _ hs
      apply Cong.assert
      rw [Database.eraseEntry_eqs]
      exact Or.inr ⟨v, hv, rfl⟩
  · apply Database.mem_terms_iff.mpr
    refine ⟨p, ?_, hs⟩
    rw [Database.eraseEntry_eqs]
    exact Or.inl ⟨hp, he⟩

/-- Deleting a valid row atom cannot remove a held value. -/
theorem Database.mem_terms_eraseEntry_of_value {db : Database} {row : Entry} {t : Term}
    (hr : row.Valid db.sig) (hv : t.IsValue db.sig) (ht : t ∈ db.terms) :
    t ∈ (db.eraseEntry row).terms :=
  Database.mem_terms_eraseEntry_of_ne (fun he => hr.atom_not_value (he ▸ hv)) ht

/-- Erasing a row with existing columns introduces no new terms. -/
theorem Database.terms_eraseEntry_subset {db : Database} {row : Entry}
    (hc : ∀ t ∈ row.columns, t ∈ db.terms) : (db.eraseEntry row).terms ⊆ db.terms := by
  intro t ht
  obtain ⟨p, hp, hs⟩ := Database.mem_terms_iff.mp ht
  rw [Database.eraseEntry_eqs] at hp
  rcases hp with hp | ⟨v, hv, rfl⟩
  · exact Database.mem_terms_iff.mpr ⟨p, hp.1, hs⟩
  · exact Cong.subterm (hc v hv) (hs.elim id id)

theorem Database.StoreOk.eraseEntry {db : Database} (h : db.StoreOk) (row : Entry)
    (hr : row.Valid db.sig) : (db.eraseEntry row).StoreOk := by
  refine ⟨?_, ?_, ?_, by simpa using h.envValues⟩
  · intro r hm
    obtain ⟨dc, hd, hm, _⟩ := hm.1
    exact ⟨dc, hd, hm⟩
  · intro r hm t ht
    exact Cong.subterm (.assert hm.2) (Term.arg_subterms ht (.refl _))
  · intro p hp
    rw [Database.eraseEntry_eqs] at hp
    rcases hp with hp | ⟨v, hv, rfl⟩
    · simpa only [Database.eraseEntry_sig] using h.typed p hp.1
    · exact Or.inl ⟨hr.column_values v hv, hr.column_values v hv⟩

theorem Database.StoreOk.addTerms {db : Database} (h : db.StoreOk) (ts : List Term)
    (ht : ∀ t ∈ ts, t.Stored db.sig) : (db.addTerms ts).StoreOk := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih =>
    exact ih (h.addTerm t (ht t (by simp))) (fun u hu => ht u (by simp [hu]))

theorem Database.StoreOk.setEnv {db : Database} (h : db.StoreOk) {σ : Env}
    (hv : ∀ b ∈ σ, b.2.IsValue db.sig) :
    ({db with env := σ} : Database).StoreOk := h.congr rfl rfl hv

theorem Database.StoreOk.terms_eraseEntry {db : Database} (h : db.StoreOk)
    {row : Entry} (hr : row.Valid db.sig) :
    (db.eraseEntry row).terms = (db.terms \ {row.atom}) ∪
      {s | ∃ t ∈ row.columns, s ∈ t.subterms} := by
  have hgone : row.atom ∉ (db.eraseEntry row).terms := by
    intro ht
    have he := (h.eraseEntry row hr).entry_of_held_atom
      (by simpa only [Database.eraseEntry_sig] using hr) ht
    rw [Database.eraseEntry_entries hr] at he
    exact he.2 rfl
  ext t
  constructor
  · intro ht
    obtain ⟨p, hp, hs⟩ := Database.mem_terms_iff.mp ht
    rw [Database.eraseEntry_eqs] at hp
    rcases hp with hp | ⟨v, hv, rfl⟩
    · refine Or.inl ⟨Database.mem_terms_iff.mpr ⟨p, hp.1, hs⟩, ?_⟩
      intro he
      apply hgone
      exact he ▸ Database.mem_terms_iff.mpr ⟨p,
        Database.eraseEntry_eqs ▸ Or.inl hp, hs⟩
    · exact Or.inr ⟨v, hv, hs.elim id id⟩
  · rintro (⟨ht, hn⟩ | ⟨v, hv, hs⟩)
    · exact Database.mem_terms_eraseEntry_of_ne hn ht
    · apply Cong.subterm (t := v) _ hs
      exact .assert (Database.eraseEntry_eqs ▸ Or.inr ⟨v, hv, rfl⟩)

/-- Actual row deletion removes just that atom; its value columns remain held. -/
theorem Database.StoreOk.terms_eraseEntry_of_mem {db : Database} (h : db.StoreOk)
    {row : Entry} (hr : row ∈ db.entries) :
    (db.eraseEntry row).terms = db.terms \ {row.atom} := by
  rw [h.terms_eraseEntry hr.1]
  apply Set.union_eq_left.mpr
  rintro t ⟨v, hv, ht⟩
  refine ⟨Cong.subterm (h.columns row hr v hv) ht, ?_⟩
  intro he
  exact hr.1.atom_not_value (he ▸ (hr.1.column_values v hv).subterm ht)

theorem Database.WF.eraseEntry {db : Database} (hw : db.WF)
    (hs : db.StoreOk) (row : Entry) (hr : row.Valid db.sig) :
    (db.eraseEntry row).WF := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [Database.eraseEntry_env] at hb
    exact Database.mem_terms_eraseEntry_of_value hr (hs.envValues b hb) (hw.envInTerms b hb)
  · intro p hp
    rw [Database.eraseEntry_eqs] at hp
    rcases hp with hp | ⟨v, _, rfl⟩
    · exact hw.litsIsolated p hp.1
    · exact fun _ => rfl

/-- Replacing the environment by one whose values the database holds keeps `WF`. -/
theorem Database.WF.setEnv {db : Database} (hw : db.WF) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) : Database.WF { db with env := σ } where
  envInTerms b hb := by simpa using hσ b hb
  litsIsolated := hw.litsIsolated

/-- `WF.setEnv` at the one environment the semantics imposes: the globals extended by a
rule-local substitution. -/
theorem Database.WF.appendEnv {db : Database} (hw : db.WF) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) : Database.WF { db with env := σ ++ db.env } :=
  hw.setEnv fun b hb => (List.mem_append.mp hb).elim (hσ b) (hw.envInTerms b)

/-- Each argument of an application the database holds is a term the database holds:
`WF.subtermClosed` at depth one. -/
theorem Database.mem_terms_of_arg {db : Database} (hwf : db.WF) {f : FnName}
    {args : List Term} (h : Term.app f args ∈ db.terms) {t : Term} (ht : t ∈ args) :
    t ∈ db.terms :=
  hwf.subtermClosed _ h
    (Term.mem_subterms.mpr (Term.IsSubterm.arg ht (Term.IsSubterm.refl t)))

/-- `Term.least` answers with one of its operands. -/
theorem Term.least_eq_or (s t : Term) : Term.least s t = s ∨ Term.least s t = t := by
  unfold Term.least
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

namespace Expr
@[simp] theorem eval_lit {sig : Signature} {l : Lit} {σ : Env} :
    (Expr.lit l).eval sig σ = some (.lit l) := rfl

@[simp] theorem eval_var {sig : Signature} {v : Var} {σ : Env} :
    (Expr.var v).eval sig σ = (Env.lookup v σ).filter (Term.isValue sig) := rfl

/-- The building case, which is the only one the constructor fragment ever takes. -/
@[simp] theorem eval_app_ctor {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hc : sig.IsCtor f) :
    (Expr.app f args).eval sig σ = (Expr.evalList sig args σ).map (Term.app f) := by
  simp only [Expr.eval, if_pos hc]

/-- The choosing case: the smaller of the two operands in the term order. -/
@[simp] theorem eval_min {sig : Signature} {a b : Expr} {σ : Env} :
    (Expr.min a b).eval sig σ =
      (a.eval sig σ).bind fun x => (b.eval sig σ).map (Term.least x) := rfl

/-- **The stuck case**, all of it: anything that is not a *declared* constructor has no
rule. It covers the two lookups — a `:merge` and a `:no-merge` function — and, since
declaration is required, the name nobody declared. -/
theorem eval_app_not_ctor {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hc : ¬ sig.IsCtor f) :
    (Expr.app f args).eval sig σ = none := by
  simp only [Expr.eval, if_neg hc]

/-- The reading case, which has no rule: an application of a merge function is a lookup,
and `Impl/Check.lean`'s `noLookup` rejects one in every position this is called from. -/
theorem eval_app_merge {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    {body : List Action} {res : List Expr}
    (hc : sig.mergeOf f = some (MergeSpec.merge oldVars newVars body res)) :
    (Expr.app f args).eval sig σ = none :=
  eval_app_not_ctor (Signature.not_isCtor hc)

/-- The undeclared case, spelled out: a name the signature does not mention builds
nothing. -/
theorem eval_app_undeclared {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hc : sig f = none) :
    (Expr.app f args).eval sig σ = none :=
  eval_app_not_ctor (Signature.not_isCtor_of_none hc)

@[simp] theorem evalList_nil {sig : Signature} {σ : Env} :
    Expr.evalList sig [] σ = some [] := rfl

@[simp] theorem evalList_cons {sig : Signature} {e : Expr} {es : List Expr} {σ : Env} :
    Expr.evalList sig (e :: es) σ =
      (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·) := rfl

/-- `Expr.evalList` is length-preserving, which is how a `set`'s declared column widths
become the *term* widths `MergeStep.collide` asks about. -/
theorem evalList_length {sig : Signature} {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.evalList sig es σ = some ts) : ts.length = es.length := by
  induction es generalizing ts with
  | nil => rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ rfl
  | cons e es ih =>
    rw [Expr.evalList_cons] at h
    obtain ⟨t, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    simp [ih hus]

mutual

theorem eval_isValue {sig : Signature} {σ : Env} {e : Expr} {t : Term}
    (h : e.eval sig σ = some t) : t.IsValue sig := by
  match e with
  | .lit l => cases Option.some.inj h; exact .lit sig l
  | .var _ => exact (Option.filter_eq_some_iff.mp h).2
  | .app f args =>
    by_cases hc : sig.IsCtor f
    · rw [eval_app_ctor hc] at h
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .app hc (evalList_isValue hts)
    · simp [eval_app_not_ctor hc] at h
  | .min a b =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (eval_isValue hx).least (eval_isValue hy)

theorem evalList_isValue {sig : Signature} {σ : Env} {es : List Expr} {ts : List Term}
    (h : evalList sig es σ = some ts) : ∀ t ∈ ts, t.IsValue sig := by
  match es with
  | [] => cases Option.some.inj h; simp
  | e :: es =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact eval_isValue ht
    · exact evalList_isValue hu s hs

end

/-- **A variable that is one of the evaluated expressions is bound.** `Expr.evalList`
succeeding is the only way a query atom's key columns can be read, so this is how matching an
atom witnesses that its key variables have values. -/
theorem lookup_isSome_of_mem_evalList {sig : Signature} {ρ : Env} {v : Var}
    {es : List Expr} {ts : List Term} (h : Expr.evalList sig es ρ = some ts)
    (hv : Expr.var v ∈ es) : (Env.lookup v ρ).isSome := by
  induction es generalizing ts with
  | nil => simp at hv
  | cons e es ih =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h'⟩ := h
    obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp h'
    rcases List.mem_cons.mp hv with rfl | hv'
    · rw [Expr.eval_var] at ht
      rw [(Option.filter_eq_some_iff.mp ht).1]
      rfl
    · exact ih hus hv'

end Expr
/-! ### Evaluation stays inside the constructor fragment

The condition on a single term, and the fact that `Expr.eval` only ever produces such
terms. It lives here rather than with the invariant that reads it because it is a fact
about `Expr.eval` and nothing else; `Proofs/Merge.lean`'s `FDatabase.Inv` needs it. -/

/-- A term built only from constructor applications: the condition the operations that
*insert* a term have to be given. -/
def Term.CtorTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → sig.IsCtor f

/-- A literal mentions no application. -/
theorem Term.ctorTerm_lit {sig : Signature} {l : Lit} : Term.CtorTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

mutual

/-- **Evaluation only ever builds constructor terms.**

Each branch that produces a term stays inside the constructor fragment: the building
branch's head is a *declared* constructor by the guard the evaluator just tested, and
`min` returns one of its operands. Nothing reads a row, so no case has to place a
recorded output back in `terms`. This is what `FDatabase.Inv.execAction` needs. -/
theorem Expr.eval_ctorTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm sig b.2) {e : Expr} {t : Term}
    (hs : e.eval sig σ = some t) : Term.CtorTerm sig t := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at hs
    subst hs; exact Term.ctorTerm_lit
  | .var v =>
    rw [Expr.eval_var] at hs
    exact hσ (v, t) (Env.mem_of_lookup (Option.filter_eq_some_iff.mp hs).1)
  | .app f args =>
    by_cases hu : sig.IsCtor f
    · rw [Expr.eval_app_ctor hu, Option.map_eq_some_iff] at hs
      obtain ⟨ts, hts, rfl⟩ := hs
      have hts' := Expr.evalList_ctorTerm hσ hts
      intro g bs hsub
      rw [Term.subterms_app] at hsub
      rcases Set.mem_insert_iff.mp hsub with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
        exact hu
      · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
        exact hts' x hx g bs hxs
    · rw [Expr.eval_app_not_ctor hu] at hs; exact absurd hs (by simp)
  | .min a b =>
    rw [Expr.eval_min, Option.bind_eq_some_iff] at hs
    obtain ⟨x, hx, hmap⟩ := hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
    rcases Term.least_eq_or x y with h | h <;> rw [h]
    · exact Expr.eval_ctorTerm hσ hx
    · exact Expr.eval_ctorTerm hσ hy

theorem Expr.evalList_ctorTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm sig b.2) {es : List Expr} {ts : List Term}
    (hs : Expr.evalList sig es σ = some ts) : ∀ t ∈ ts, Term.CtorTerm sig t := by
  match es with
  | [] =>
    rw [Expr.evalList_nil, Option.some_inj] at hs
    subst hs; simp
  | e :: es =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨t, ht, hmap⟩ := hs
    obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hmap
    subst heq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Expr.eval_ctorTerm hσ ht
    · exact Expr.evalList_ctorTerm hσ hrest x hx

end

/-! ### Evaluation builds terms of the declared width

`Term.CtorTerm`'s width twin: it reads a head's *column counts* where that reads its kind,
and it is `Database.DeclaredTerms` on a single term. The check that supplies the counts is
`Expr.WidthOk`. -/

/-- `Database.DeclaredTerms` on a single term: the condition the operations that *insert* a
term have to be given. -/
def Term.DeclaredTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → ∃ d, sig f = some d ∧ as.length = d.entryWidth

/-- A literal mentions no application. -/
theorem Term.declaredTerm_lit {sig : Signature} {l : Lit} :
    Term.DeclaredTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

mutual

/-- **A width-checked expression evaluates to a term of the declared width.** The building
branch's head is a declared constructor, whose `entryWidth` is its `arity`, and `WidthOk`
supplies the argument count; `min` returns one of its operands. -/
theorem Expr.eval_declaredTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.DeclaredTerm sig b.2) {e : Expr} {t : Term}
    (hw : e.WidthOk sig) (hs : e.eval sig σ = some t) : Term.DeclaredTerm sig t := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at hs
    subst hs; exact Term.declaredTerm_lit
  | .var v =>
    rw [Expr.eval_var] at hs
    exact hσ (v, t) (Env.mem_of_lookup (Option.filter_eq_some_iff.mp hs).1)
  | .app f args =>
    by_cases hu : sig.IsCtor f
    · rw [Expr.eval_app_ctor hu, Option.map_eq_some_iff] at hs
      obtain ⟨ts, hts, rfl⟩ := hs
      have hts' := Expr.evalList_declaredTerm hσ hw.2 hts
      obtain ⟨d, hd, hdm⟩ := hu
      intro g bs hsub
      rw [Term.subterms_app] at hsub
      rcases Set.mem_insert_iff.mp hsub with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
        refine ⟨d, hd, ?_⟩
        rw [Expr.evalList_length hts, hw.1 d hd, FnDecl.entryWidth, if_pos]
        simp [hdm]
      · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
        exact hts' x hx g bs hxs
    · rw [Expr.eval_app_not_ctor hu] at hs; exact absurd hs (by simp)
  | .min a b =>
    rw [Expr.eval_min, Option.bind_eq_some_iff] at hs
    obtain ⟨x, hx, hmap⟩ := hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
    rcases Term.least_eq_or x y with h | h <;> rw [h]
    · exact Expr.eval_declaredTerm hσ hw.1 hx
    · exact Expr.eval_declaredTerm hσ hw.2 hy

theorem Expr.evalList_declaredTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.DeclaredTerm sig b.2) {es : List Expr} {ts : List Term}
    (hw : Expr.WidthOkList es sig) (hs : Expr.evalList sig es σ = some ts) :
    ∀ t ∈ ts, Term.DeclaredTerm sig t := by
  match es with
  | [] =>
    rw [Expr.evalList_nil, Option.some_inj] at hs
    subst hs; simp
  | e :: es =>
    rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨t, ht, hmap⟩ := hs
    obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hmap
    subst heq
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Expr.eval_declaredTerm hσ hw.1 ht
    · exact Expr.evalList_declaredTerm hσ hw.2 hrest x hx

end

/-! ### `DeclaredTerms`, term by term

`Database.DeclaredTerms` and `Term.DeclaredTerm` are the same condition read of a state and
of a term. `WF.subtermClosed` moves it in one direction, and the two `add` operations move
it back. -/

theorem Database.declaredTerm_of_mem {db : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {t : Term} (ht : t ∈ db.terms) : Term.DeclaredTerm db.sig t := fun f as hsub =>
  hdt f as (hwf.subtermClosed t ht hsub)

theorem Database.env_declaredTerm {db : Database} (hwf : db.WF) (hdt : db.DeclaredTerms) :
    ∀ b ∈ db.env, Term.DeclaredTerm db.sig b.2 :=
  fun b hb => Database.declaredTerm_of_mem hwf hdt (hwf.envInTerms b hb)

theorem Database.declaredTerms_addTerm {db : Database} (hdt : db.DeclaredTerms) {t : Term}
    (ht : Term.DeclaredTerm db.sig t) : (db.addTerm t).DeclaredTerms := by
  intro f as hmem
  rw [Database.addTerm_terms] at hmem
  rcases hmem with h | h
  · exact hdt f as h
  · exact ht f as h

theorem Database.declaredTerms_addEq {db : Database} (hdt : db.DeclaredTerms) {a b : Term}
    (ha : Term.DeclaredTerm db.sig a) (hb : Term.DeclaredTerm db.sig b) :
    (db.addEq a b).DeclaredTerms := by
  intro f as hmem
  rw [Database.addEq_terms] at hmem
  rcases hmem with (h | h) | h
  · exact hdt f as h
  · exact ha f as h
  · exact hb f as h

theorem Database.declaredTerms_putEntry {db : Database} (hdt : db.DeclaredTerms)
    {e : Entry} (he : e.Valid db.sig)
    (hc : ∀ t ∈ e.columns, Term.DeclaredTerm db.sig t) :
    (db.putEntry e).DeclaredTerms := by
  apply Database.declaredTerms_addTerm hdt
  intro f args ht
  rw [Entry.atom, Term.subterms_app, Set.mem_insert_iff] at ht
  rcases ht with heq | ht
  · obtain ⟨rfl, rfl⟩ := Term.app.inj heq
    obtain ⟨decl, hd, hm, hk, hv, _⟩ := he
    exact ⟨decl, hd, by simp [Entry.columns, FnDecl.entryWidth, hk, hv, hm]⟩
  · obtain ⟨t, hm, ht⟩ := Set.mem_iUnion₂.mp ht
    exact hc t hm f args ht

theorem Database.empty_declaredTerms : Database.empty.DeclaredTerms := by
  intro f as hmem
  rw [Database.empty_terms] at hmem
  exact absurd hmem (by simp)

mutual

/-- Evaluation reads the environment only through `lookup`, so environments that
agree are interchangeable. This is what lets `Env.UnionAll`'s duplicate bindings be
ignored. -/
theorem Expr.eval_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (e : Expr) :
    e.eval sig σ₁ = e.eval sig σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => simp only [Expr.eval, h v]
  | .app f args => simp only [Expr.eval, Expr.evalList_agree h args]
  | .min a b => simp only [Expr.eval, Expr.eval_agree h a, Expr.eval_agree h b]

theorem Expr.evalList_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂)
    (es : List Expr) : Expr.evalList sig es σ₁ = Expr.evalList sig es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons, Expr.eval_agree h e, Expr.evalList_agree h es]

end

mutual

/-- **Evaluation depends only on the variables the expression mentions.** The partial form of
`Expr.eval_agree`: the two environments need agree nowhere else, so a substitution may be
extended or narrowed away from `e.vars` freely.

`Env.Agree` is the total case, and total agreement is more than a caller usually has — one
atom of a joined query is matched under its own substitution and read under the union, and
those agree only on that atom's own variables. -/
theorem Expr.eval_agreeOn {sig : Signature} {σ₁ σ₂ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, Env.lookup v σ₁ = Env.lookup v σ₂) :
    e.eval sig σ₁ = e.eval sig σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => simp only [Expr.eval, h v (by simp)]
  | .app f args => simp only [Expr.eval, Expr.evalList_agreeOn args (by simpa using h)]
  | .min a b =>
    simp only [Expr.eval, Expr.eval_agreeOn a (fun v hv => h v (by simp [hv])),
      Expr.eval_agreeOn b (fun v hv => h v (by simp [hv]))]

@[inherit_doc Expr.eval_agreeOn]
theorem Expr.evalList_agreeOn {sig : Signature} {σ₁ σ₂ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, Env.lookup v σ₁ = Env.lookup v σ₂) :
    Expr.evalList sig es σ₁ = Expr.evalList sig es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons,
      Expr.eval_agreeOn e (fun v hv => h v (List.mem_union_iff.mpr (Or.inl hv))),
      Expr.evalList_agreeOn es (fun v hv => h v (List.mem_union_iff.mpr (Or.inr hv)))]

end

mutual

/-- Evaluation gets stuck on an unbound variable and on a lookup; an expression with
neither evaluates. The two conditions are exactly `Expr.Scoped` and `Expr.Evaluable`
(`Spec/Scope.lean`). -/
theorem Expr.eval_isSome {sig : Signature} {σ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, v ∈ Env.dom σ)
    (hf : ∀ f ∈ e.fns, sig.IsCtor f)
    (hv : ∀ b ∈ σ, b.2.IsValue sig) :
    ∃ t, e.eval sig σ = some t := by
  match e with
  | .lit l => exact ⟨.lit l, rfl⟩
  | .var v =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (Env.lookup_isSome_iff_mem_dom.mpr (h v (by simp)))
    exact ⟨t, Option.filter_eq_some_iff.mpr ⟨ht, hv (v, t) (Env.mem_of_lookup ht)⟩⟩
  | .app f args =>
    have hc := hf f (by simp)
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (by simpa using h)
      (fun g hg => hf g (by simp [hg])) hv
    exact ⟨.app f ts, by rw [Expr.eval_app_ctor hc, hts, Option.map_some]⟩
  | .min a b =>
    obtain ⟨x, hx⟩ := Expr.eval_isSome a (fun v hv => h v (by simp [hv]))
      (fun g hg => hf g (by simp [hg])) hv
    obtain ⟨y, hy⟩ := Expr.eval_isSome b (fun v hv => h v (by simp [hv]))
      (fun g hg => hf g (by simp [hg])) hv
    exact ⟨Term.least x y, by rw [Expr.eval_min, hx, Option.bind_some, hy, Option.map_some]⟩

theorem Expr.evalList_isSome {sig : Signature} {σ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, v ∈ Env.dom σ)
    (hf : ∀ f ∈ Expr.fnsList es, sig.IsCtor f)
    (hv : ∀ b ∈ σ, b.2.IsValue sig) :
    ∃ ts, Expr.evalList sig es σ = some ts := by
  match es with
  | [] => exact ⟨[], rfl⟩
  | e :: es =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome e (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inl hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inl hg))) hv
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome es (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inr hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inr hg))) hv
    exact ⟨t :: ts, by rw [Expr.evalList_cons, ht, Option.bind_some, hts, Option.map_some]⟩

end

mutual

/-- **Extending the environment on the right keeps a value.** `Env.lookup` is left-biased, so
a variable the prefix already binds reads the same either way — which is what relates a rule
head's reading at `σ ++ db.env` to the match's own at `σ`. -/
theorem Expr.eval_append_env {sig : Signature} {σ τ : Env} :
    ∀ (e : Expr) {t : Term}, e.eval sig σ = some t → e.eval sig (σ ++ τ) = some t
  | .lit _, _, h => h
  | .var v, _, h => by
      obtain ⟨hl, hv⟩ := Option.filter_eq_some_iff.mp h
      exact Option.filter_eq_some_iff.mpr ⟨Env.lookup_append_of_some hl, hv⟩
  | .app f args, t, h => by
      by_cases hctor : sig.IsCtor f
      · rw [Expr.eval_app_ctor hctor] at h ⊢
        obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
        rw [Expr.evalList_append_env args hts, Option.map_some]
        exact congrArg some hap
      · rw [Expr.eval_app_not_ctor hctor] at h
        exact absurd h (by simp)
  | .min a b, t, h => by
      rw [Expr.eval_min] at h ⊢
      obtain ⟨x, hx, hmap⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rw [Expr.eval_append_env a hx, Option.bind_some, Expr.eval_append_env b hy,
        Option.map_some]

@[inherit_doc Expr.eval_append_env]
theorem Expr.evalList_append_env {sig : Signature} {σ τ : Env} :
    ∀ (es : List Expr) {ts : List Term},
      Expr.evalList sig es σ = some ts → Expr.evalList sig es (σ ++ τ) = some ts
  | [], _, h => h
  | e :: es, _, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_append_env e ht, Option.bind_some,
        Expr.evalList_append_env es hts, Option.map_some]
      exact congrArg some hcons

end

/-! ### Complete atoms -/

namespace Expr

theorem entry_none_of_allConstructors {sig : Signature} (hs : sig.AllConstructors)
    (e : Expr) : e.entry sig = none := by
  cases e with
  | lit _ => rfl
  | var _ => rfl
  | min _ _ => rfl
  | app f cols =>
    cases hd : sig f with
    | none => simp [Expr.entry, hd]
    | some d =>
      have hm : d.merge = none := by simpa [Signature.mergeOf, hd] using hs f
      simp [Expr.entry, hd, hm]

/-- Value evaluation never classifies its expression as a function write. -/
theorem entry_none_of_eval {sig : Signature} {e : Expr} {ρ : Env} {t : Term}
    (h : e.eval sig ρ = some t) : e.entry sig = none := by
  cases e with
  | lit _ | var _ | min _ _ => rfl
  | app f args =>
      have hc : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at h
        contradiction
      obtain ⟨d, hd, hm⟩ := hc
      simp [Expr.entry, hd, hm]

/-- Outside the function-entry case, complete atoms and values agree. -/
theorem evalAtom_eq_eval_of_entry_none {sig : Signature} {e : Expr} {ρ : Env}
    (h : e.entry sig = none) : e.evalAtom sig ρ = e.eval sig ρ := by
  cases e with
  | lit _ | var _ | min _ _ => rfl
  | app f args =>
      cases hd : sig f with
      | none =>
          have hc : ¬ sig.IsCtor f := by
            rintro ⟨d, he, _⟩
            simp [hd] at he
          simp [Expr.evalAtom, hd, Expr.eval_app_not_ctor hc]
      | some d =>
          have hm : d.merge = none := by
            cases hm : d.merge with
            | none => rfl
            | some ms => simp [Expr.entry, hd, hm] at h
          have hc : sig.IsCtor f := ⟨d, hd, hm⟩
          simp [Expr.evalAtom, hd, hm, Expr.eval_app_ctor hc]

@[simp] theorem evalAtom_lit {sig : Signature} {l : Lit} {σ : Env} :
    (Expr.lit l).evalAtom sig σ = some (.lit l) := rfl

@[simp] theorem evalAtom_var {sig : Signature} {v : Var} {σ : Env} :
    (Expr.var v).evalAtom sig σ = (Env.lookup v σ).filter (Term.isValue sig) := rfl

@[simp] theorem evalAtom_app_decl {sig : Signature} {f : FnName} {cols : List Expr}
    {d : FnDecl} {σ : Env} (hd : sig f = some d)
    (hw : d.merge = none ∨ cols.length = d.entryWidth) :
    (Expr.app f cols).evalAtom sig σ = (Expr.evalList sig cols σ).map (Term.app f) := by
  simp [Expr.evalAtom, hd, hw]

@[simp] theorem evalList_append_map {sig : Signature} {σ : Env} (as bs : List Expr) :
    Expr.evalList sig (as ++ bs) σ = (Expr.evalList sig as σ).bind fun ts =>
      (Expr.evalList sig bs σ).map (ts ++ ·) := by
  induction as with
  | nil => simp [Expr.evalList]
  | cons a as ih =>
    simp only [List.cons_append, Expr.evalList, ih]
    cases a.eval sig σ <;> cases Expr.evalList sig as σ <;> simp [Function.comp_def]

/-- Recover the table declaration and the full column list of an entry atom. -/
theorem entry_some {sig : Signature} {e : Expr} {f : FnName} {keys vals : List Expr}
    (h : e.entry sig = some (f, keys, vals)) :
    ∃ d, sig f = some d ∧ d.merge.isSome = true ∧ e = .app f (keys ++ vals) := by
  cases e with
  | lit _ => simp [Expr.entry] at h
  | var _ => simp [Expr.entry] at h
  | min _ _ => simp [Expr.entry] at h
  | app g cols =>
    cases hd : sig g with
    | none => simp [Expr.entry, hd] at h
    | some d =>
      simp only [Expr.entry, hd, Option.bind_some] at h
      split at h
      · rename_i hm
        cases Option.some.inj h
        exact ⟨d, hd, hm, by rw [List.take_append_drop]⟩
      · simp at h

theorem evalAtom_entry {sig : Signature} {e : Expr} {f : FnName} {keys vals : List Expr}
    {σ : Env} {ts us : List Term} (he : e.entry sig = some (f, keys, vals))
    (hk : Expr.evalList sig keys σ = some ts) (hv : Expr.evalList sig vals σ = some us)
    (hw : e.AtomWidthOk sig) :
    e.evalAtom sig σ = some (.app f (ts ++ us)) := by
  obtain ⟨d, hd, _, rfl⟩ := entry_some he
  simp [evalAtom_app_decl hd (Or.inr (hw.1 d hd)), hk, hv]

theorem evalAtom_app_inv {sig : Signature} {f : FnName} {cols : List Expr}
    {σ : Env} {t : Term}
    (h : (Expr.app f cols).evalAtom sig σ = some t) :
    ∃ ts, Expr.evalList sig cols σ = some ts ∧ t = .app f ts := by
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · obtain ⟨ts, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ts, hs, rfl⟩
  · simp at h

theorem evalAtom_stored {sig : Signature} {e : Expr} {σ : Env} {t : Term}
    (h : e.evalAtom sig σ = some t) : t.Stored sig := by
  cases e with
  | lit _ | var _ | min _ _ => exact Or.inl (eval_isValue h)
  | app f cols =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    next hw =>
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      by_cases hm : d.merge = none
      · exact Or.inl (.app ⟨d, hd, hm⟩ (evalList_isValue hts))
      · have hl : ts.length = d.arity + d.outArity :=
          by simpa [FnDecl.entryWidth, hm] using
            (evalList_length hts).trans (hw.resolve_left hm)
        refine Or.inr ⟨⟨f, ts.take d.arity, ts.drop d.arity⟩, ?_, ?_⟩
        · refine ⟨d, hd, hm, ?_, ?_, ?_⟩
          · simp only [List.length_take]; omega
          · simp only [List.length_drop]; omega
          · simpa only [Entry.columns, List.take_append_drop] using evalList_isValue hts
        · simp only [Entry.atom, Entry.columns, List.take_append_drop]
    next => simp at h

/-- Value evaluation is the restriction of atom evaluation to value expressions. -/
theorem evalAtom_of_eval {sig : Signature} {e : Expr} {σ : Env} {t : Term}
    (h : e.eval sig σ = some t) : e.evalAtom sig σ = some t := by
  cases e with
  | lit _ => exact h
  | var _ => exact h
  | min _ _ => exact h
  | app f cols =>
    by_cases hc : sig.IsCtor f
    · obtain ⟨d, hd, hm⟩ := hc
      simpa [Expr.evalAtom, Expr.eval, hd, Signature.IsCtor, hm] using h
    · simp [Expr.eval, hc] at h

/-- In a constructor-only signature the two evaluators coincide. -/
theorem evalAtom_eq_eval {sig : Signature} (hs : sig.AllConstructors) (e : Expr) (σ : Env) :
    e.evalAtom sig σ = e.eval sig σ := by
  cases e with
  | lit _ => rfl
  | var _ => rfl
  | min _ _ => rfl
  | app f cols =>
    cases hd : sig f with
    | none => simp [Expr.evalAtom, Expr.eval, hd, Signature.IsCtor]
    | some d =>
      have hm : d.merge = none := by simpa [Signature.mergeOf, hd] using hs f
      simp [Expr.evalAtom, Expr.eval, hd, Signature.IsCtor, hm]

theorem evalAtom_agree {sig : Signature} {σ τ : Env} (h : Env.Agree σ τ) (e : Expr) :
    e.evalAtom sig σ = e.evalAtom sig τ := by
  cases e with
  | lit _ => rfl
  | var v => simp only [Expr.evalAtom, Expr.eval, h v]
  | app f cols => simp only [Expr.evalAtom, Expr.evalList_agree h cols]
  | min a b => exact Expr.eval_agree h (.min a b)

theorem evalAtom_agreeOn {sig : Signature} {σ τ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, Env.lookup v σ = Env.lookup v τ) :
    e.evalAtom sig σ = e.evalAtom sig τ := by
  cases e with
  | lit _ => rfl
  | var v => simp only [Expr.evalAtom, Expr.eval, h v (by simp)]
  | app f cols => simp only [Expr.evalAtom, Expr.evalList_agreeOn cols (by simpa using h)]
  | min a b => exact Expr.eval_agreeOn (.min a b) h

/-- Atom evaluation respects the declaration's full entry width. -/
theorem evalAtom_declaredTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.DeclaredTerm sig b.2) {e : Expr} {t : Term}
    (hw : e.AtomWidthOk sig) (hs : e.evalAtom sig σ = some t) : Term.DeclaredTerm sig t := by
  cases e with
  | lit l =>
    cases Option.some.inj hs
    exact Term.declaredTerm_lit
  | var v => exact hσ (v, t) (Env.mem_of_lookup (Option.filter_eq_some_iff.mp hs).1)
  | min a b => exact Expr.eval_declaredTerm hσ (show (Expr.min a b).WidthOk sig from hw) hs
  | app f cols =>
    cases hd : sig f with
    | none => simp [Expr.evalAtom, hd] at hs
    | some d =>
      rw [evalAtom_app_decl hd (Or.inr (hw.1 d hd))] at hs
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hs
      intro g bs hsub
      rw [Term.subterms_app] at hsub
      rcases Set.mem_insert_iff.mp hsub with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
        exact ⟨d, hd, (Expr.evalList_length hts).trans (hw.1 d hd)⟩
      · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
        exact Expr.evalList_declaredTerm hσ hw.2 hts x hx g bs hxs

end Expr

@[simp] theorem evalActions_nil {db : Database} : evalActions db [] = some db := rfl

@[simp] theorem evalActions_cons {db : Database} {a : Action} {as : List Action} :
    evalActions db (a :: as) = (evalAction db a).bind fun db' => evalActions db' as := rfl

/-! ### Actions only add -/
/-- A value expression is inserted as a constructor value, without inserting a function entry. -/
theorem evalAction_expr_of_eval {db : Database} {e : Expr} {t : Term}
    (h : e.eval db.sig db.env = some t) :
    evalAction db (.expr e) = some (db.addTerm t) := by
  simp [evalAction, Expr.evalAtom_of_eval h]

/-- An action adds a complete atom or asserts a value equation. -/
theorem evalAction_eq_some {db db' : Database} {a : Action}
    (h : evalAction db a = some db') :
    (∃ e t, a = .expr e ∧ e.evalAtom db.sig db.env = some t ∧ db' = db.addTerm t) ∨
      (∃ e₁ e₂ t₁ t₂, a = .union e₁ e₂ ∧ e₁.eval db.sig db.env = some t₁ ∧
        e₂.eval db.sig db.env = some t₂ ∧ ¬ (t₁.isLit ∨ t₂.isLit) ∧ db' = db.addEq t₁ t₂) := by
  cases a with
  | expr e =>
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Or.inl ⟨e, t, rfl, ht, rfl⟩
  | union e₁ e₂ =>
      obtain ⟨t₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · simp at h
      · next hl =>
          cases Option.some.inj h
          exact Or.inr ⟨e₁, e₂, t₁, t₂, rfl, h₁, h₂,
            by simpa using hl, rfl⟩

theorem evalAction_contained {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db.Contained db' := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, -, rfl⟩
  · exact .addTerm t db
  · exact .addEq t₁ t₂ db

theorem evalAction_rules {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.rules = db.rules := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, -, rfl⟩ <;> rfl

theorem evalAction_sig {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.sig = db.sig := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, -, rfl⟩ <;> rfl

theorem evalAction_env {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.env = db.env := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, -, rfl⟩ <;> rfl

theorem evalAction_entries_subset {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db.entries ⊆ db'.entries := by
  intro row hr
  exact ⟨by rw [evalAction_sig h]; exact hr.1, (evalAction_contained h).eqs hr.2⟩

theorem evalActions_entries_subset {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db.entries ⊆ db'.entries := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; exact subset_rfl
  | cons a as ih =>
      obtain ⟨d, ha, has⟩ := Option.bind_eq_some_iff.mp h
      exact (evalAction_entries_subset ha).trans (ih has)

theorem evalAction_storeOk {db db' : Database} (hs : db.StoreOk) {a : Action}
    (h : evalAction db a = some db') : db'.StoreOk := by
  rcases evalAction_eq_some h with ⟨_, t, -, ht, rfl⟩ |
    ⟨_, _, t₁, t₂, -, h₁, h₂, -, rfl⟩
  · exact hs.addTerm t (Expr.evalAtom_stored ht)
  · exact hs.addEq t₁ t₂ (Expr.eval_isValue h₁) (Expr.eval_isValue h₂)

theorem evalActions_storeOk {db db' : Database} (hs : db.StoreOk) {as : List Action}
    (h : evalActions db as = some db') : db'.StoreOk := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; exact hs
  | cons a as ih =>
      obtain ⟨d, ha, has⟩ := Option.bind_eq_some_iff.mp h
      exact ih (evalAction_storeOk hs ha) has

/-- Every action in a block uses the same substitution. -/
theorem evalActions_env {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.env = db.env := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; rfl
  | cons a as ih =>
      obtain ⟨d, ha, has⟩ := Option.bind_eq_some_iff.mp h
      exact (ih has).trans (evalAction_env ha)

theorem evalAction_wf {db db' : Database} (hw : db.WF) {a : Action}
    (h : evalAction db a = some db') : db'.WF := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, hlit, rfl⟩
  · exact hw.addTerm t
  · exact hw.addEq t₁ t₂ fun hl => absurd hl hlit

theorem evalActions_contained {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db.Contained db' := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact (evalAction_contained hv).trans (ih h)

theorem evalActions_sig {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.sig = db.sig := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_sig hv]

theorem evalActions_rules {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.rules = db.rules := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_rules hv]

theorem evalActions_wf {db db' : Database} (hw : db.WF) {as : List Action}
    (h : evalActions db as = some db') : db'.WF := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (evalAction_wf hw hv) h

/-! ### Actions keep `DeclaredTerms`

`Action.WidthOk` checks the complete atom an action records. Its declaration determines
the column count: `arity + outArity` for a merge function and `arity` for a constructor.
Evaluation checks that nested value expressions apply declared constructors. -/

/-- **`DeclaredTerms` is preserved by an action.** -/
theorem evalAction_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {a : Action} (hw : a.WidthOk db.sig)
    (h : evalAction db a = some db') : db'.DeclaredTerms := by
  have henv := Database.env_declaredTerm hwf hdt
  rcases evalAction_eq_some h with ⟨e, t, rfl, ht, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, ht₁, ht₂, -, rfl⟩
  · exact Database.declaredTerms_addTerm hdt (Expr.evalAtom_declaredTerm henv hw ht)
  · exact Database.declaredTerms_addEq hdt (Expr.eval_declaredTerm henv hw.1 ht₁)
      (Expr.eval_declaredTerm henv hw.2 ht₂)

theorem evalActions_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    {as : List Action} (hw : Actions.WidthOk as db.sig)
    (h : evalActions db as = some db') : db'.DeclaredTerms := by
  induction as generalizing db with
  | nil => rw [evalActions_nil, Option.some_inj] at h; exact h ▸ hdt
  | cons a as ih =>
    rw [evalActions_cons, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, hrest⟩ := h
    have hsig : d.sig = db.sig := evalAction_sig hd
    exact ih (evalAction_wf hwf hd) (evalAction_declaredTerms hwf hdt hw.1 hd)
      (by rw [hsig]; exact hw.2) hrest

/-! ### Agreeing environments are interchangeable

`Expr.eval_agree` says evaluation reads the environment only through `lookup`. Lifting
that to whole action sequences is what justifies two places the semantics is loose
about environments on purpose: `Env.Union2` can leave a variable bound twice, and
`ValidEnv` fixes a substitution's domain only up to permutation. -/
theorem evalAction_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a : Action) :
    Option.Rel Database.EnvAgree (evalAction d₁ a) (evalAction d₂ a) := by
  cases a with
  | expr e =>
      simp only [evalAction, ← h.sig, ← Expr.evalAtom_agree h.env e]
      cases e.evalAtom d₁.sig d₁.env with
      | none => exact .none
      | some t => exact .some (h.addTerm t)
  | union e₁ e₂ =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e₁,
      ← Expr.eval_agree (sig := d₁.sig) h.env e₂]
    cases e₁.eval d₁.sig d₁.env with
    | none => exact .none
    | some t₁ =>
      cases e₂.eval d₁.sig d₁.env with
      | none => exact .none
      | some t₂ =>
        simp only [Option.bind_some]
        by_cases hlit : t₁.isLit || t₂.isLit
        · simp only [if_pos hlit]; exact .none
        · simp only [if_neg hlit]
          exact .some ⟨h.sig,
            by simp only [Database.addEq_eqs, h.eqs],
            h.rules, h.env⟩

theorem evalActions_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (as : List Action) :
    Option.Rel Database.EnvAgree (evalActions d₁ as) (evalActions d₂ as) := by
  induction as generalizing d₁ d₂ with
  | nil => exact .some h
  | cons a as ih =>
    have hrel := evalAction_envAgree h a
    cases h₁ : evalAction d₁ a with
    | none =>
      cases h₂ : evalAction d₂ a with
      | none => simp only [evalActions_cons, h₁, h₂, Option.bind_none]; exact .none
      | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₁ =>
      cases h₂ : evalAction d₂ a with
      | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
      | some e₂ =>
        rw [h₁, h₂] at hrel
        cases hrel with
        | some he =>
          simp only [evalActions_cons, h₁, h₂, Option.bind_some]
          exact ih he

/-- Local actions cannot tell agreeing substitutions apart. -/
theorem evalLocalActions_agree {db : Database} (as : List Action) {σ₁ σ₂ : Env}
    (h : Env.Agree σ₁ σ₂) : evalLocalActions db as σ₁ = evalLocalActions db as σ₂ := by
  have hE : Database.EnvAgree { db with env := σ₁ ++ db.env } { db with env := σ₂ ++ db.env } :=
    ⟨rfl, rfl, rfl, Env.Agree.append_right db.env h⟩
  have hrel := evalActions_envAgree hE as
  simp only [evalLocalActions]
  cases h₁ : evalActions { db with env := σ₁ ++ db.env } as with
  | none =>
    cases h₂ : evalActions { db with env := σ₂ ++ db.env } as with
    | none => rfl
    | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
  | some e₁ =>
    cases h₂ : evalActions { db with env := σ₂ ++ db.env } as with
    | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₂ =>
      rw [h₁, h₂] at hrel
      cases hrel with
      | some he => simp only [Option.map_some, he.eq_of_env_rules db.env db.rules]

/-! ### Local actions preserve the caller's environment and rules -/
/-- Local actions run the actions with `σ` in scope and then put the caller's
environment and rules back. -/
theorem evalLocalActions_eq_some {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') :
    ∃ d, evalActions { db with env := σ ++ db.env } as = some d ∧
      db' = { d with env := db.env, rules := db.rules } := by
  cases hv : evalActions { db with env := σ ++ db.env } as with
  | none => simp [evalLocalActions, hv] at h
  | some d =>
    simp only [evalLocalActions, hv, Option.map_some, Option.some.injEq] at h
    exact ⟨d, rfl, h.symm⟩

theorem evalLocalActions_env {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.env = db.env := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_rules {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.rules = db.rules := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_sig {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.sig = db.sig := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact (evalActions_sig hv : _ = ({ db with env := σ ++ db.env } : Database).sig)

theorem evalLocalActions_entries_subset {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db.entries ⊆ db'.entries := by
  obtain ⟨post, hp, rfl⟩ := evalLocalActions_eq_some h
  exact evalActions_entries_subset (db := { db with env := σ ++ db.env }) (db' := post) hp

theorem evalLocalActions_contained {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db.Contained db' := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact ⟨(evalActions_contained hv).eqs⟩

/-- Local actions preserve well-formedness provided the substitution only mentions
terms the database holds — which is what `ValidEnv` guarantees. -/
theorem evalLocalActions_wf {db db' : Database} (hw : db.WF) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (h : evalLocalActions db as σ = some db') : db'.WF := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  have hd := evalActions_wf (hw.appendEnv hσ) hv
  exact ⟨fun b hb => Database.terms_setEnvRules ▸ (evalActions_contained hv).terms
      (Database.terms_setEnv ▸ hw.envInTerms b hb),
    hd.litsIsolated⟩

/-- Local actions keep `DeclaredTerms`, under `evalLocalActions_wf`'s condition on the
substitution and the two checks `evalActions_declaredTerms` asks of the block. -/
theorem evalLocalActions_declaredTerms {db db' : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hw : Actions.WidthOk as db.sig)
    (h : evalLocalActions db as σ = some db') :
    db'.DeclaredTerms := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  intro g cs hmem
  rw [Database.terms_setEnvRules] at hmem
  exact evalActions_declaredTerms (hwf.appendEnv hσ)
    (by intro g cs hm; rw [Database.terms_setEnv] at hm; exact hdt g cs hm) hw hv g cs hmem

/-- Evaluating a concatenation evaluates each part. -/
theorem Expr.evalList_append {sig : Signature} {σ : Env} :
    ∀ {es fs : List Expr} {ts : List Term}, Expr.evalList sig (es ++ fs) σ = some ts →
      ∃ as bs, Expr.evalList sig es σ = some as ∧ Expr.evalList sig fs σ = some bs ∧
        ts = as ++ bs := by
  intro es
  induction es with
  | nil => intro fs ts h; exact ⟨[], ts, rfl, h, rfl⟩
  | cons e es ih =>
    intro fs ts h
    rw [List.cons_append, Expr.evalList] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨as, bs, has, hbs, rfl⟩ := ih hus
    exact ⟨t :: as, bs, by rw [Expr.evalList, ht, Option.bind_some, has, Option.map_some],
      hbs, rfl⟩

end Egglog
