import EgglogSemantics.Spec.Merge
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Interp

/-!
# What M9 has to prove

`MERGE.md` says which theorem buys what. Five are still unproved; the rest are proved.

M9 gives the state a **row set** and keeps `Spec/Congruence.lean`'s `Cong` as the only
equality. What a row set adds to congruence is the functional dependency, and that is
`Proofs/Congruence.lean`'s `Cong.fd` — a theorem, under the hypothesis that a
constructor's rows have their canonical shape. So every M2–M8 theorem transports
unchanged, and `closureF`, which reads `terms` and `eqs` and no row, still decides the
relation the specification's `Database.Out` and `Matches` compare keys with.

Two statements needed repair, and the repairs are the interesting output:

* `execM_reachable` is false without a side condition. It carries `Program.CtorDecls` and
  is **proved**; its docstring justifies it.
* `MergeStep.self_id` and `MergeStep.wf` need the row half of well-formedness
  (`Database.RowsWF`), which `Database.WF` deliberately omits, and `self_id`
  additionally needs `ctorRowsOf db.terms ⊆ db.rows`.

`MergeStep.diamond_of_join` and `RunStep.unique_of_confluent` are the two `MERGE.md`
flags as guesses, and both have hypotheses that cannot be used; their docstrings say
what replaces them.
-/

namespace Egglog
/-! ### The constructor fragment collapses

Congruence is M2's already; this says the same of the *step* relations. -/
/-- With no `.merge` function there is no collision to resolve, so a round is `RunRules`
and nothing else: M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : Database}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  cases h with
  | collide _ _ _ hm _ _ => exact (hsig.elim hm).elim

/-! ### The one signature change worth naming

`Cong` reads neither `sig` nor `rows`, so a declaration cannot take a derivation away.
Named rather than inlined because `CmdStep.mono_recorded`'s `.decl` case is the only
place it is spent, and the name says what that case is doing. -/

/-- Declaring a name preserves every derivation. -/
theorem Cong.mono_update {db : Database} {f : FnName} {dc : FnDecl} {a b : Term}
    (h : Cong db a b) :
    Cong ({ db with sig := Function.update db.sig f (some dc) } : Database) a b :=
  Cong.mono (show db.Contained { db with sig := Function.update db.sig f (some dc) } from
    ⟨subset_rfl, subset_rfl, subset_rfl⟩) h

@[inherit_doc Cong.mono_update]
theorem CongList.mono_update {db : Database} {f : FnName} {dc : FnDecl} {as bs : List Term}
    (h : CongList db as bs) :
    CongList ({ db with sig := Function.update db.sig f (some dc) } : Database) as bs :=
  CongList.mono (show db.Contained { db with sig := Function.update db.sig f (some dc) } from
    ⟨subset_rfl, subset_rfl, subset_rfl⟩) h

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, CongList.mono h hl, h.rows hrow⟩

/-! ### Recording: containment for an implementation that re-keys

`Database.Recorded` is `Contained` with its row clause read through `Out`, and
`Spec/Merge.lean` says why the refinement chain needs it: a rebuild moves a row onto the
canonical key of its class, which `Out` still reads and `⊆` does not. Everything
`Contained` gave the chain has to be given again, and each lemma below is the `Contained`
one with that single clause changed.

The price shows up in exactly one place, `Cong.fd`: its two rows are now found at
*congruent* keys rather than at the same ones, so its key premise has to be recomposed
from three congruences instead of transported. Every other case is `Contained`'s. -/
/-- `CongList` is reflexive on tuples the database holds, which is what makes a row
`Out` at its own key. `Cong.refl`'s membership side condition is why this is not free. -/
theorem CongList.refl_of_mem {db : Database} {as : List Term}
    (h : ∀ a ∈ as, a ∈ db.terms) : CongList db as as := by
  induction as with
  | nil => exact .nil
  | cons a as ih =>
    exact .cons (.refl (h a (by simp))) (ih fun x hx => h x (by simp [hx]))

/-- A row the database holds is `Out` at its own key, provided the key's terms are held
too. -/
theorem Database.out_self {db : Database} {r : Row} (hr : r ∈ db.rows)
    (ha : ∀ a ∈ r.args, a ∈ db.terms) : db.Out r.fn r.args r.out :=
  ⟨r.args, CongList.refl_of_mem ha, hr⟩

/-- Every listed term is held by `addTerms`. -/
theorem Database.mem_terms_addTerms {db : Database} {ts : List Term} {t : Term}
    (h : t ∈ ts) : t ∈ (db.addTerms ts).terms := by
  induction ts generalizing db with
  | nil => simp at h
  | cons s ts ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact (Database.Contained.addTerms ts (db.addTerm t)).terms
        (Or.inr t.self_mem_subterms)
    · exact ih h'

/-- A constructor row of `t` talks only about subterms of `t`. -/
theorem Term.args_mem_subterms_of_mem_ctorRows {t : Term} {r : Row} (h : r ∈ t.ctorRows)
    {a : Term} (ha : a ∈ r.args) : a ∈ t.subterms :=
  Term.subterms_subset_of_mem h.2 (Term.IsSubterm.arg ha (Term.IsSubterm.refl a))

mutual

/-- `Cong.mono` along `Recorded`. `Recorded` weakens only the row clause, and `Cong`
reads no rows, so this is `Cong.mono` with the same proof. -/
theorem Cong.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂)
    {a b : Term} (hc : Cong d₁ a b) : Cong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .refl hm => exact .refl (h.terms hm)
  | .symm hc => exact .symm (Cong.mono_recorded h hc)
  | .trans h₁ h₂ => exact .trans (Cong.mono_recorded h h₁) (Cong.mono_recorded h h₂)
  | .congr hm₁ hm₂ hl =>
    exact .congr (h.terms hm₁) (h.terms hm₂) (CongList.mono_recorded h hl)

theorem CongList.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂)
    {as bs : List Term} (hc : CongList d₁ as bs) : CongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (Cong.mono_recorded h hab) (CongList.mono_recorded h hl)

end

/-- `Out.mono` along `Recorded`: the key class is searched twice and the two searches
compose. -/
theorem Database.Out.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) :
    d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  obtain ⟨cs, hl', hrow'⟩ := h.rows _ hrow
  exact ⟨cs, (CongList.mono_recorded h hl).trans hl', hrow'⟩

namespace Database
namespace Recorded

/-- Reflexivity is **not** free: `Out` reads a key up to congruence and `CongList` is
reflexive only on terms the database holds, so `RowsWF` is the side condition. Every state
the refinement chain visits has it, as the row half of `FDatabase.Inv`. -/
theorem refl {db : Database} (h : db.RowsWF) : db.Recorded db :=
  ⟨subset_rfl, fun r hr => Database.out_self hr (h r hr).1, subset_rfl⟩

/-- Syntactic containment is recording, under the same side condition. -/
theorem of_contained {d₁ d₂ : Database} (h : d₁.Contained d₂) (hw : d₁.RowsWF) :
    d₁.Recorded d₂ :=
  ⟨h.terms, fun r hr => Database.out_self (h.rows hr) fun a ha => h.terms ((hw r hr).1 a ha),
    h.eqs⟩

/-- `Recorded` reads `sig`, `terms`, `rows` and `eqs`; `env` and `rules` may be replaced
freely on both sides. -/
theorem setEnvRules {d₁ d₂ : Database} (h : d₁.Recorded d₂) (σ τ : Env) (rs ss : Set Rule) :
    ({ d₁ with env := σ, rules := rs } : Database).Recorded
      { d₂ with env := τ, rules := ss } := by
  have hc : d₂.Contained ({ d₂ with env := τ, rules := ss } : Database) :=
    ⟨subset_rfl, subset_rfl, subset_rfl⟩
  exact ⟨h.terms, fun r hr => Database.Out.mono hc (h.rows r hr), h.eqs⟩

/-- Nothing reads the environment through `Out`, so both sides may be re-based. -/
theorem setEnv {d₁ d₂ : Database} (h : d₁.Recorded d₂) (σ τ : Env) :
    ({ d₁ with env := σ } : Database).Recorded { d₂ with env := τ } :=
  h.setEnvRules σ τ d₁.rules d₂.rules

theorem trans {d₁ d₂ d₃ : Database} (h₁ : d₁.Recorded d₂) (h₂ : d₂.Recorded d₃) :
    d₁.Recorded d₃ :=
  ⟨h₁.terms.trans h₂.terms,
    fun r hr => Database.Out.mono_recorded h₂ (h₁.rows r hr), h₁.eqs.trans h₂.eqs⟩

/-- Growing the right-hand side keeps it a recorder. -/
theorem trans_contained {d₁ d₂ d₃ : Database} (h₁ : d₁.Recorded d₂)
    (h₂ : d₂.Contained d₃) : d₁.Recorded d₃ :=
  ⟨h₁.terms.trans h₂.terms,
    fun r hr => Database.Out.mono h₂ (h₁.rows r hr), h₁.eqs.trans h₂.eqs⟩

/-! The same operation applied to both sides, as `Contained` has. The added rows are the
same on both, so they are `Out` at their own keys and only the *old* rows need the
weakening. -/
theorem addTerm_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (t : Term) :
    (d₁.addTerm t).Recorded (d₂.addTerm t) := by
  refine ⟨Set.union_subset_union h.terms subset_rfl, ?_, h.eqs⟩
  rintro r (hr | hr)
  · exact Database.Out.mono (Database.Contained.addTerm t d₂) (h.rows r hr)
  · exact Database.out_self (Or.inr hr)
      fun a ha => Or.inr (Term.args_mem_subterms_of_mem_ctorRows hr ha)

theorem addTerms_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (ts : List Term) :
    (d₁.addTerms ts).Recorded (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

theorem addEq_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (a b : Term) :
    (d₁.addEq a b).Recorded (d₂.addEq a b) := by
  have h' := (h.addTerm_mono a).addTerm_mono b
  have hc : ((d₂.addTerm a).addTerm b).Contained (d₂.addEq a b) :=
    ⟨subset_rfl, subset_rfl, Set.subset_insert _ _⟩
  exact ⟨h'.terms, fun r hr => Database.Out.mono hc (h'.rows r hr),
    Set.insert_subset_insert h.eqs⟩

theorem addRow_mono {d₁ d₂ : Database} (h : d₁.Recorded d₂) (f : FnName)
    (as vs : List Term) : (d₁.addRow f as vs).Recorded (d₂.addRow f as vs) := by
  have h' := (h.addTerms_mono as).addTerms_mono vs
  have hc : ((d₂.addTerms as).addTerms vs).Contained (d₂.addRow f as vs) :=
    ⟨subset_rfl, Set.subset_insert _ _, subset_rfl⟩
  refine ⟨h'.terms, ?_, h'.eqs⟩
  rintro r (rfl | hr)
  · exact Database.out_self (Set.mem_insert _ _) fun a ha =>
      (Database.Contained.addTerms vs _).terms (Database.mem_terms_addTerms ha)
  · exact Database.Out.mono hc (h'.rows r hr)

end Recorded

/-- What the **smaller** side of a `Recorded` has to satisfy for a row written at a
congruent key to be free: it is subterm-closed, its rows talk only about terms it holds,
and it holds the constructor row of every application it holds.

Together they are `Database.addTerms_eq_self`'s hypotheses, which is the point: re-adding a
key the database already has changes nothing, so the specification is free to write the
combined row at a *different* key of the same class without the implementation's terms or
constructor rows going missing. Every state the refinement chain visits has all three —
they are `FDatabase.Inv`'s `wf`, `rowsWF` and `rowsComplete`. -/
structure Solid (db : Database) : Prop where
  wf : db.WF
  rowsWF : db.RowsWF
  rowsComplete : db.RowsComplete

namespace Recorded

/-- **`addRow_mono` with the two keys merely congruent.** This is the shape a re-keying
implementation needs: it writes the combined row at the canonical key of the class and the
specification writes it at the key of the row it merged, and `Out` reads the one from the
other. -/
theorem addRow_congr {d₁ d₂ : Database} (h : d₁.Recorded d₂) (hs : d₁.Solid) (f : FnName)
    {as : List Term} (bs vs : List Term) (has : ∀ a ∈ as, a ∈ d₁.terms)
    (hab : CongList (d₂.addRow f bs vs) as bs) :
    (d₁.addRow f as vs).Recorded (d₂.addRow f bs vs) := by
  have hself : d₁.addTerms as = d₁ :=
    Database.addTerms_eq_self hs.wf hs.rowsComplete has
  have hc : (d₂.addTerms vs).Contained (d₂.addRow f bs vs) :=
    ((Database.Contained.addTerms bs d₂).addTerms_mono vs).trans
      ⟨subset_rfl, Set.subset_insert _ _, subset_rfl⟩
  have hrest : (d₁.addTerms vs).Recorded (d₂.addRow f bs vs) :=
    (h.addTerms_mono vs).trans_contained hc
  refine ⟨?_, ?_, ?_⟩
  · show ((d₁.addTerms as).addTerms vs).terms ⊆ _
    rw [hself]; exact hrest.terms
  · show ∀ r ∈ insert (Row.mk f as vs) ((d₁.addTerms as).addTerms vs).rows, _
    rw [hself]
    rintro r (rfl | hr)
    · exact ⟨bs, hab, Set.mem_insert _ _⟩
    · exact hrest.rows r hr
  · show ((d₁.addTerms as).addTerms vs).eqs ⊆ _
    rw [hself]; exact hrest.eqs

end Recorded
end Database

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `Cong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d f as _ _ _ vs _ _ _ _ _ _ hbody _ =>
    have hb : d₁.Contained d :=
      ⟨(evalActions_contained hbody).terms, (evalActions_contained hbody).rows,
        (evalActions_contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hc.terms, hc.rows, hc.eqs⟩

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

set_option linter.unusedVariables false in
/-- **A vacuous self-collision is the identity step.**

Three hypotheses beyond the original statement, all forced and all discharged by the
invariants `addTerm` maintains: `addRow` re-inserts the row's key and value terms, so
those insertions have to be no-ops. See `Database.addTerm_eq_self`.

`hsig` and `hres` are not used by the equation — they are what makes the conclusion an
instance of `MergeStep`, so removing them would change what the theorem says. -/
theorem MergeStep.self_id {db d : Database} {f : FnName} {as a : List Term}
    {body : List Action} {res : List Expr} (hw : db.WF) (hrw : db.RowsWF)
    (hctor : Database.ctorRowsOf db.terms ⊆ db.rows) (hrow : Row.mk f as a ∈ db.rows)
    (hsig : db.sig.mergeOf f = some (MergeSpec.merge body res))
    (hbody : evalActions { db with env := mergeEnv a a } body = some d)
    (hfix : d.terms = db.terms ∧ d.rows = db.rows ∧ d.eqs = db.eqs)
    (hres : Expr.evalList d.sig res d.env = some a) :
    ({ d.addRow f as a with env := db.env, rules := db.rules } : Database) = db := by
  obtain ⟨hft, hfr, hfe⟩ := hfix
  have hbase : (db.addTerms as).addTerms a = db := by
    rw [Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).1 t ht]
    exact Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).2 t ht
  obtain ⟨h1t, h1r⟩ := Database.addTerms_terms_rows hft hfr as
  obtain ⟨h2t, h2r⟩ := Database.addTerms_terms_rows h1t h1r a
  rw [hbase] at h2t h2r
  have hsg := evalActions_sig hbody
  refine Database.ext ?_ ?_ ?_ ?_ rfl rfl
  · exact (Database.addRow_sig (db := d) (f := f) (as := as) (vs := a)).trans hsg
  · exact h2t
  · change insert (Row.mk f as a) ((d.addTerms as).addTerms a).rows = db.rows
    rw [h2r]
    exact Set.insert_eq_self.mpr hrow
  · exact (Database.addRow_eqs (db := d) (f := f) (as := as) (vs := a)).trans hfe

/-! ### The observable value

Constraint (3)'s second half. `PLAN.md` proposes a merge-fold and asks for it to be
well defined; `Current` is that value defined as a maximum instead, which needs only
antisymmetry. It is not what `Expr.eval` reads. -/
/-- The value a *join* merge settles on at the class of `as`: the `le`-greatest
recorded output.

**Not** what a query read matches — that is `Database.Out`, any recorded output.
`Current` exists only when `f`'s merge is a join for `le`, and it is here for the two
places that need to match egglog's answer rather than over-approximate it: differential
testing, and M11's simulation theorem.

A maximum rather than a fold, because a greatest element is unique from antisymmetry
alone (`current_unique`) where a fold over a set needs commutativity and associativity
first. `le` is a parameter rather than an instance because the order is per function —
one `Term` type carries every sort — and it orders whole rows, since a multi-column merge
can settle its columns jointly. See `MERGE.md`, "Why a maximum and not a fold". -/
def Database.Current (db : Database) (le : List Term → List Term → Prop) (f : FnName)
    (as : List Term) (vs : List Term) : Prop :=
  db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs

/-- The observable value is unique. This is "the fold is well defined", with a fold's
commutativity and associativity obligations replaced by antisymmetry of the order —
see `MERGE.md`, "Why a maximum and not a fold". -/
theorem Database.current_unique {db : Database} {le : List Term → List Term → Prop}
    (hanti : ∀ x y, le x y → le y x → x = y) {f : FnName} {as v w : List Term}
    (hv : db.Current le f as v) (hw : db.Current le f as w) : v = w :=
  hanti _ _ (hw.2 v hv.1) (hv.2 w hw.1)

/-! ### The term order

`Term.blt` unfolds definitionally in every case, so the equation lemmas below are `rfl`
and the three order laws are ordinary case analyses over the (length, name, lex) key.
`Term.bltList` is only used at equal lengths, which is why *totality* is the one law
that needs a length hypothesis on the list level — `bltList [] (b :: bs)` and
`bltList (b :: bs) []` are both `false`. -/
namespace Term
@[simp] theorem blt_lit_lit {m n : Int} :
    Term.blt (.lit (.int m)) (.lit (.int n)) = decide (m < n) := rfl

@[simp] theorem blt_lit_app {l : Lit} {f : FnName} {as : List Term} :
    Term.blt (.lit l) (.app f as) = true := by cases l; rfl

@[simp] theorem blt_app_lit {f : FnName} {as : List Term} {l : Lit} :
    Term.blt (.app f as) (.lit l) = false := rfl

theorem blt_app_app {f g : FnName} {as bs : List Term} :
    Term.blt (.app f as) (.app g bs) =
      (if as.length ≠ bs.length then decide (as.length < bs.length)
       else if f ≠ g then decide (f < g) else Term.bltList as bs) := rfl

@[simp] theorem bltList_nil {bs : List Term} : Term.bltList [] bs = false := rfl

@[simp] theorem bltList_cons_nil {a : Term} {as : List Term} :
    Term.bltList (a :: as) [] = false := rfl

theorem bltList_cons_cons {a b : Term} {as bs : List Term} :
    Term.bltList (a :: as) (b :: bs) =
      if a = b then Term.bltList as bs else Term.blt a b := rfl

end Term
mutual

/-- Asymmetry. On the list level this needs no length hypothesis: a `bltList` between
lists of different lengths is `false` in both directions. -/
theorem Term.blt_asymm (s t : Term) (h : Term.blt s t = true) : Term.blt t s = false := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    rw [Term.blt_lit_lit] at h
    rw [Term.blt_lit_lit, decide_eq_false_iff_not]
    simp only [decide_eq_true_eq] at h
    omega
  | .lit _, .app _ _ => rfl
  | .app _ _, .lit _ => simp at h
  | .app f as, .app g bs =>
    rw [Term.blt_app_app] at h
    rw [Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl)] at h
      rw [if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf)] at h
        rw [if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_asymm as bs h
      · rw [if_pos hf] at h
        rw [if_pos (Ne.symm hf), decide_eq_false_iff_not]
        simp only [decide_eq_true_eq] at h
        exact String.lt_asymm h
    · rw [if_pos hl] at h
      rw [if_pos (Ne.symm hl), decide_eq_false_iff_not]
      simp only [decide_eq_true_eq] at h
      omega

theorem Term.bltList_asymm (as bs : List Term) (h : Term.bltList as bs = true) :
    Term.bltList bs as = false := by
  match as, bs with
  | [], _ => simp at h
  | _ :: _, [] => simp at h
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons] at h
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h
      rw [if_pos hab.symm]
      exact Term.bltList_asymm as bs h
    · rw [if_neg hab] at h
      rw [if_neg (Ne.symm hab)]
      exact Term.blt_asymm a b h

end

mutual

/-- Totality. `bltList` gets the length hypothesis `blt` guarantees at every call. -/
theorem Term.blt_total (s t : Term) (h : s ≠ t) :
    Term.blt s t = true ∨ Term.blt t s = true := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    have hmn : m ≠ n := fun hmn => h (by rw [hmn])
    have : m < n ∨ n < m := by omega
    rcases this with hh | hh
    · exact Or.inl (by simp [hh])
    · exact Or.inr (by simp [hh])
  | .lit _, .app _ _ => exact Or.inl (by simp)
  | .app _ _, .lit _ => exact Or.inr (by simp)
  | .app f as, .app g bs =>
    rw [Term.blt_app_app, Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl), if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf), if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_total as bs hl fun hab => h (by rw [hab])
      · rw [if_pos hf, if_pos (Ne.symm hf)]
        simp only [decide_eq_true_eq]
        by_cases hfg : f < g
        · exact Or.inl hfg
        · refine Or.inr ?_
          by_contra hgf
          exact hf (String.le_antisymm (String.not_lt.mp hgf) (String.not_lt.mp hfg))
    · rw [if_pos hl, if_pos (Ne.symm hl)]
      simp only [decide_eq_true_eq]
      omega

theorem Term.bltList_total (as bs : List Term) (hlen : as.length = bs.length)
    (h : as ≠ bs) : Term.bltList as bs = true ∨ Term.bltList bs as = true := by
  match as, bs with
  | [], [] => exact absurd rfl h
  | [], _ :: _ => simp at hlen
  | _ :: _, [] => simp at hlen
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons, Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab.symm]
      subst hab
      exact Term.bltList_total as bs (by simpa using hlen) fun hh => h (by rw [hh])
    · rw [if_neg hab, if_neg (Ne.symm hab)]
      exact Term.blt_total a b hab

end

mutual

/-- Transitivity. The only case that needs asymmetry is the list one: `a ≠ c` has to be
derived from `blt a b` and `blt b c` before the lexicographic step can fire. -/
theorem Term.blt_trans (s t u : Term) (h₁ : Term.blt s t = true)
    (h₂ : Term.blt t u = true) : Term.blt s u = true := by
  match s, t, u with
  | .lit (.int m), .lit (.int n), .lit (.int p) =>
    rw [Term.blt_lit_lit] at h₁ h₂ ⊢
    simp only [decide_eq_true_eq] at h₁ h₂ ⊢
    omega
  | .lit _, .lit _, .app _ _ => simp
  | .lit _, .app _ _, .lit _ => simp at h₂
  | .lit _, .app _ _, .app _ _ => simp
  | .app _ _, .lit _, _ => simp at h₁
  | .app _ _, .app _ _, .lit _ => simp at h₂
  | .app f as, .app g bs, .app e cs =>
    rw [Term.blt_app_app] at h₁ h₂
    rw [Term.blt_app_app]
    by_cases hab : as.length = bs.length
    · rw [if_neg (not_not_intro hab)] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        rw [if_neg (not_not_intro (hab.trans hbc))]
        by_cases hfg : f = g
        · rw [if_neg (not_not_intro hfg)] at h₁
          by_cases hge : g = e
          · rw [if_neg (not_not_intro hge)] at h₂
            rw [if_neg (not_not_intro (hfg.trans hge))]
            subst hfg; subst hge
            exact Term.bltList_trans as bs cs h₁ h₂
          · rw [if_pos hge] at h₂
            have hfe : f ≠ e := by rintro rfl; exact hge hfg.symm
            rw [if_pos hfe]
            subst hfg
            exact h₂
        · rw [if_pos hfg] at h₁
          by_cases hge : g = e
          · have hfe : f ≠ e := by rintro rfl; exact hfg hge.symm
            rw [if_pos hfe]
            subst hge
            exact h₁
          · rw [if_pos hge] at h₂
            simp only [decide_eq_true_eq] at h₁ h₂
            have hlt : f < e := String.lt_trans h₁ h₂
            have hfe : f ≠ e := by rintro rfl; exact String.lt_irrefl f hlt
            rw [if_pos hfe, decide_eq_true_eq]
            exact hlt
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
    · rw [if_pos hab] at h₁
      simp only [decide_eq_true_eq] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega

theorem Term.bltList_trans (as bs cs : List Term) (h₁ : Term.bltList as bs = true)
    (h₂ : Term.bltList bs cs = true) : Term.bltList as cs = true := by
  match as, bs, cs with
  | [], _, _ => simp at h₁
  | _ :: _, [], _ => simp at h₁
  | _ :: _, _ :: _, [] => simp at h₂
  | a :: as, b :: bs, c :: cs =>
    rw [Term.bltList_cons_cons] at h₁ h₂
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h₁
      by_cases hbc : b = c
      · rw [if_pos hbc] at h₂
        rw [if_pos (hab.trans hbc)]
        exact Term.bltList_trans as bs cs h₁ h₂
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by rintro rfl; exact hbc hab.symm
        rw [if_neg hac, hab]
        exact h₂
    · rw [if_neg hab] at h₁
      by_cases hbc : b = c
      · have hac : a ≠ c := by rintro rfl; exact hab hbc.symm
        rw [if_neg hac, ← hbc]
        exact h₁
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by
          rintro rfl
          rw [Term.blt_asymm a b h₁] at h₂
          simp at h₂
        rw [if_neg hac]
        exact Term.blt_trans a b c h₁ h₂

end

/-- `Term.blt` is a strict linear order. Needed for `ordering-min`/`ordering-max` to be
a deterministic choice, and for "keep the smaller side" to descend. -/
theorem Term.blt_linear : (∀ s t : Term, Term.blt s t = true → Term.blt t s = false) ∧
    (∀ s t : Term, s ≠ t → Term.blt s t = true ∨ Term.blt t s = true) ∧
    (∀ s t u : Term, Term.blt s t = true → Term.blt t u = true → Term.blt s u = true) :=
  ⟨Term.blt_asymm, Term.blt_total, Term.blt_trans⟩

/-- **A constructor's outputs are all congruent.**

The functional dependency, stated as what it buys: however many rows a constructor
accumulates at one key class, they are one e-class. For `@UF_<Sort>` this is
"every parent a term ever had is equal to it"; for `@<C>View` it is congruence.

`hrow` is `Cong.fd`'s, and is what a `set` on a constructor breaks. -/
theorem Database.Out.union_cong {db : Database} {f : FnName} {as v w : List Term}
    {x y : Term}
    (hrow : ∀ r ∈ db.rows, db.sig.IsCtor r.fn →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    (hsig : db.sig.IsCtor f) (hv : db.Out f as v)
    (hw : db.Out f as w) (hxy : (x, y) ∈ v.zip w) : Cong db x y := by
  obtain ⟨bs, hlb, hrb⟩ := hv
  obtain ⟨cs, hlc, hrc⟩ := hw
  exact Cong.fd hrow hrb hrc hsig (hlb.symm.trans hlc) hxy

/-- **The functional dependency, at a state something reaches.**

`Out.union_cong` with its hypothesis discharged rather than assumed: run any
constructor-fragment program from a state whose rows are canonical, and in the state it
reaches a constructor's outputs at one key class are congruent. Nothing consumes this —
it is the argument that `Spec/` needs no `fd` rule, made machine-checkable end to end
instead of spread across docstrings. -/
theorem ProgramStep.out_union_cong {db db' : Database} {p : Program}
    (h : ProgramStep db p db') (hwf : db.WF) (hrows : db.CtorRows)
    (hsig : db.sig.AllConstructors) (hterms : db.CtorTerms) (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal db.sig) (hrules : ∀ r ∈ db.rules, r.SetLegal db.sig)
    {f : FnName} {as v w : List Term} {x y : Term} (hf : db'.sig.IsCtor f)
    (hv : db'.Out f as v) (hw : db'.Out f as w) (hxy : (x, y) ∈ v.zip w) :
    Cong db' x y :=
  Database.Out.union_cong
    (Database.CtorRows.fd_hyp
      (h.ctorRows hwf hrows hsig hterms hdecl hlegal hrules)) hf hv hw hxy

/-! ### Invariants over the step relation

The shape every M11 safety theorem takes, and the reason termination and confluence are
*not* in the spec: an invariant holds at every reachable state, so a run that diverges
satisfies it throughout and a run that merges in a different order satisfies it too.
"Every proof row the encoding writes is checker-valid" is one of these. -/
/-- Reachable states satisfy any invariant preserved by one command. -/
theorem invariant_of_step {I : Database → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    {db db' : Database} {p : Program} (hinit : I db) (h : ProgramStep db p db') :
    I db' := by
  induction h with
  | nil => exact hinit
  | cons hc _ ih => exact ih (hstep _ _ _ hinit hc)

/-- **Every command only adds.**

The formal content of "never delete a term row or a proof row", which the encoding
depends on and which the invariant argument needs: anything the checker reads is
positive in the state, so once true it stays true. `.rule` and `.decl` touch only
fields `Contained` ignores. -/
theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  cases h with
  | action ha hm =>
    exact (evalAction_contained ha).trans (MergeClosure.contained hm)
  | rule => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run hrun =>
    have hu : db.Contained (RunRules db) := Database.Contained.sUnion _ _
    exact hu.trans (MergeClosure.contained hrun)
  | decl => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem ProgramStep.contained {db db' : Database} {p : Program}
    (h : ProgramStep db p db') : db.Contained db' := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons hc _ ih => exact (CmdStep.contained hc).trans ih

/-! ### Determinism

Demoted. Confluence is not needed by any safety theorem — see `invariant_of_step`. It
buys one thing only: strengthening M10's refinement from "the interpreter's result is
spec-reachable" to an equality. -/
/-! **Evaluation reads the database only through its signature**, which after M12 is
literally the type of `Expr.eval`: with one evaluator taking a `Signature`, "two databases
with the same signature admit the same evaluations" is a rewrite rather than a theorem.
Monotonicity in `Contained` — half of what a diamond proof for `MergeStep` needs, see
`MergeStep.diamond_of_join` — follows the same way. -/

/-- A saturated state is a fixpoint of the whole closure, not only of one step. -/
theorem MergeSaturated.closure_eq {db d : Database} (hs : MergeSaturated db)
    (h : MergeClosure db d) : d = db := by
  induction h with
  | refl => rfl
  | @tail _ _ _ hstep ih => subst ih; exact hs _ hstep

/-- A merge that is a `le`-join is locally confluent: two collisions available at once
can be fired in either order and rejoined. **Unproved, and the statement is worse than
"not known to hold" — `hjoin` is vacuous.** Instantiate `le := fun _ _ => False`:
then `db.Current le f as v` unfolds to `db.Out f as v ∧ ∀ ws, db.Out f as ws → False`,
which is self-contradictory, so `hjoin` holds for *every* `db` and the statement is
unconditional local confluence of `MergeStep`. Any repair has to make the join
condition bite on the merge *body*, not on `Current`.

Unconditional local confluence nevertheless looks **true**, and in the stronger
one-step-on-one-side form `Relation.church_rosser` wants, for a reason `MERGE.md`'s
"open question 2" does not consider: a step's *effect* does not depend on the ambient
state. `addTerm`/`addEq`/`addRow` each add a set determined by the terms involved, and
those terms are fixed by the evaluation, which reads only `sig` and so stays
available in a larger database. So firing collision 2 at `d₁` and collision 1 at `d₂`
should land on the same state — the third table's merge that `MERGE.md` worries about
is a *later* step, and it too remains available because nothing is removed.

What is missing is exactness, and only exactness. The *existential* form of that
transport — `evalActions db body = some d → db.Contained e → e.sig = db.sig →
e.env = db.env → ∃ d', evalActions e body = some d' ∧ d.Contained d'` — is
`evalActions_mono` below,
and it is enough for the containment contract. The diamond needs the same statement with
`d'` pinned to the componentwise join `e ⊔ d`, which is one case per action against the
set algebra of `addTerm`/`addTerms`/`addRow`; that part is still open. -/
theorem MergeStep.diamond_of_join {db d₁ d₂ : Database}
    {le : List Term → List Term → Prop}
    (hjoin : ∀ f as v w, db.Current le f as v → db.Out f as w → le w v)
    (h₁ : MergeStep db d₁) (h₂ : MergeStep db d₂) :
    ∃ d, MergeClosure d₁ d ∧ MergeClosure d₂ d := by
  sorry

/-- **`hconf` is too weak to use.** Local confluence plus "both are normal forms" gives
uniqueness only via Newman's lemma, which needs the relation to be *terminating* — and
`MergeStep` deliberately is not (`MERGE.md`, constraint (6)). Without termination the
implication genuinely fails in general rewriting: `a ⇄ b`, `a → c`, `b → d` with `c`,
`d` normal is locally confluent and has two normal forms. That shape cannot arise here,
because `MergeStep.contained` forbids cycles — so the *conclusion* is very likely true
— but it is true for a reason `hconf` does not supply, and the only route to it is the
strong diamond, which is `MergeStep.diamond_of_join` restated. Hence
`RunStep.unique_of_diamond` below, which is this theorem with a hypothesis a proof can
actually consume. -/
theorem RunStep.unique_of_confluent {db d₁ d₂ : Database}
    (hconf : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', MergeClosure e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  sorry

/-- With a confluent merge the *saturated* states of a round coincide, so an
interpreter that runs merges to a fixpoint computes the one answer `RunStep` allows
that egglog also allows. `RunStep` itself stays a relation.

The hypothesis is `Relation.church_rosser`'s: one of the two joining paths has to be at
most a *single* step. That is exactly the form the monotonicity argument in
`MergeStep.diamond_of_join` would give, and unlike plain local confluence it needs no
termination. -/
theorem RunStep.unique_of_diamond {db d₁ d₂ : Database}
    (hdiamond : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', Relation.ReflGen MergeStep e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  obtain ⟨e, he₁, he₂⟩ := Relation.church_rosser hdiamond h₁ h₂
  exact (hs₁.closure_eq he₁).symm.trans (hs₂.closure_eq he₂)

/-! ### Fewer rows mean fewer matches

The other half of the containment contract. `mergeRound_confined` says the implementation
deletes only what it may; this says that deleting can only *lose* results, never invent
them — there is no negation anywhere in the fragment, so every premise of a match is
positive in the state. Together they are "the implementation may find fewer results, never
more", which is the safe direction for M11: a safety property is positive in the state, so
it transfers downward. `Database.Contained`'s `addTerm_mono` family, in
`Proofs/Database.lean`, is what carries a match along. -/
theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.2 b hb)⟩

/-- **A larger database admits every match a smaller one does.** Read contrapositively —
which is how the containment contract uses it — a database missing rows finds at most the
matches the full one finds. -/
theorem ValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : ValidSubst d₁ p σ) :
    ValidSubst d₂ p σ := by
  have hsig₁ : ∀ t : Term, (d₁.addTerm t).sig = (d₂.addTerm t).sig := fun _ => hsig
  refine ⟨by rw [henv]; exact h.1.mono hc, ?_⟩
  cases h.2 with
  | expr hw he hcong =>
    refine .expr (hc.terms hw) ?_
      (congOn_singleton.mpr
        (Cong.mono (hc.addTerm_mono _) (congOn_singleton.mp hcong)))
    · rw [henv, ← hsig]; exact he
  | eq hw he₁ he₂ hc₁ hc₂ =>
    refine .eq (hc.terms hw) ?_ ?_
      (congOn_pair.mpr (Cong.mono ((hc.addTerm_mono _).addTerm_mono _)
        (congOn_pair.mp hc₁)))
      (congOn_pair.mpr (Cong.mono ((hc.addTerm_mono _).addTerm_mono _)
        (congOn_pair.mp hc₂)))
    · rw [henv, ← hsig]; exact he₁
    · rw [henv, ← hsig]; exact he₂
  | @values vs f as σ us ts ws bs hu ht hk hw hrow =>
    refine .values ?_ ?_
      (congListOn_append.mpr (CongList.mono ((hc.addTerms_mono ts).addTerms_mono us)
        (congListOn_append.mp hk)))
      (congListOn_append.mpr (CongList.mono ((hc.addTerms_mono ts).addTerms_mono us)
        (congListOn_append.mp hw)))
      (hc.rows hrow)
    · rw [henv, ← hsig]; exact hu
    · rw [henv, ← hsig]; exact ht

theorem ValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => ValidSubst.mono hc hsig henv hv, hu⟩

/-- `ValidEnv.mono` needs only the term half, which `Recorded` has unchanged. -/
theorem ValidEnv.mono_recorded {d₁ d₂ : Database} (h : d₁.Recorded d₂) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.2 b hb)⟩

/-- **`ValidSubst.mono` along `Recorded`.** Only the row atom differs from the
`Contained` proof: the row is found at a *congruent* key, so the atom's key congruence is
composed with the one `Recorded` supplies. Its value columns are untouched, which is why
`Database.Recorded` may weaken the key clause and must not weaken the value one. -/
theorem ValidSubst.mono_recorded {d₁ d₂ : Database} (hc : d₁.Recorded d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env}
    (h : ValidSubst d₁ p σ) : ValidSubst d₂ p σ := by
  have hsig₁ : ∀ t : Term, (d₁.addTerm t).sig = (d₂.addTerm t).sig := fun _ => hsig
  refine ⟨by rw [henv]; exact h.1.mono_recorded hc, ?_⟩
  cases h.2 with
  | expr hw he hcong =>
    refine .expr (hc.terms hw) ?_
      (congOn_singleton.mpr
        (Cong.mono_recorded (hc.addTerm_mono _) (congOn_singleton.mp hcong)))
    · rw [henv, ← hsig]; exact he
  | eq hw he₁ he₂ hc₁ hc₂ =>
    refine .eq (hc.terms hw) ?_ ?_
      (congOn_pair.mpr (Cong.mono_recorded ((hc.addTerm_mono _).addTerm_mono _)
        (congOn_pair.mp hc₁)))
      (congOn_pair.mpr (Cong.mono_recorded ((hc.addTerm_mono _).addTerm_mono _)
        (congOn_pair.mp hc₂)))
    · rw [henv, ← hsig]; exact he₁
    · rw [henv, ← hsig]; exact he₂
  | @values vs f as σ us ts ws bs hu ht hk hw hrow =>
    have hc' : ((d₁.addTerms ts).addTerms us).Recorded ((d₂.addTerms ts).addTerms us) :=
      (hc.addTerms_mono ts).addTerms_mono us
    have hsig' : ((d₁.addTerms ts).addTerms us).sig = ((d₂.addTerms ts).addTerms us).sig := by
      simp [hsig]
    obtain ⟨bs', hbs', hrow'⟩ := hc.rows _ hrow
    refine .values ?_ ?_
      (congListOn_append.mpr
        ((CongList.mono_recorded hc' (congListOn_append.mp hk)).trans
          (CongList.mono
            ((Database.Contained.addTerms ts d₂).trans (Database.Contained.addTerms us _))
            hbs')))
      (congListOn_append.mpr (CongList.mono_recorded hc' (congListOn_append.mp hw)))
      hrow'
    · rw [henv, ← hsig]; exact hu
    · rw [henv, ← hsig]; exact ht

theorem ValidQuerySubst.mono_recorded {d₁ d₂ : Database} (hc : d₁.Recorded d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : ValidQuerySubst d₁ q σ) : ValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => ValidSubst.mono_recorded hc hsig henv hv, hu⟩

/-! ### Transporting a step

A step's *effect* is fixed by the evaluation witnesses it carries, and those witnesses
depend on the state only through `sig` and on the environment only through
`Env.lookup`. Two transports follow, and the containment contract spends both.

Along `Contained`: the same block re-run on a larger state lands on a state containing
the smaller run's result. That is `evalActions_mono`, and it is the weak — but
sufficient — form of what `MergeStep.diamond_of_join` wants.

Along `Env.Agree`: two environments no `lookup` can tell apart give runs differing only
in the `env` field, which `Database.EnvAgree.eq_of_env_rules` then collapses once the
caller's environment is restored. This is `Proofs/Eval.lean`'s `evalActions_envAgree`
for the relational semantics, and it is what lets a rule fire under the substitution the
specification admits rather than the one the enumerator emitted. -/

/-- Agreement survives a shared innermost binding, which is the `letBind` case of
`evalAction_envAgree`. -/
theorem Env.Agree.cons {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (w : Var) (t : Term) :
    Env.Agree ((w, t) :: σ₁) ((w, t) :: σ₂) := by
  intro v
  simp only [Env.lookup_cons]
  split
  · rfl
  · exact h v

/-- `EnvAgree` fixes `terms`, `rows` and `eqs`, so it is `Contained` in both directions.
This is how the `Contained`-indexed monotonicity lemmas apply to it. -/
theorem Database.EnvAgree.contained {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) :
    d₁.Contained d₂ :=
  ⟨fun _ hx => h.terms ▸ hx, fun _ hx => h.rows ▸ hx, fun _ hx => h.eqs ▸ hx⟩

/-- The `union` case of `evalAction_envAgree`; companion of
`Database.EnvAgree.addTerm` and `.addRow` in `Proofs/Database.lean`. -/
theorem Database.EnvAgree.addEq {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a b : Term) :
    (d₁.addEq a b).EnvAgree (d₂.addEq a b) :=
  let h' := (h.addTerm a).addTerm b
  ⟨h'.sig, h'.terms, h'.rows, by simp [Database.addEq, h.eqs], h'.rules, h'.env⟩

/-- `evalActions_envAgree` in the shape the transports use: a run under one environment
gives a run under any environment agreeing with it. -/
theorem evalActions_envAgree_exists {d₁ d₂ c : Database} (h : d₁.EnvAgree d₂)
    {as : List Action} (hs : evalActions d₁ as = some c) :
    ∃ c', evalActions d₂ as = some c' ∧ c.EnvAgree c' := by
  have hrel := evalActions_envAgree h as
  rw [hs] at hrel
  cases hx : evalActions d₂ as with
  | none => rw [hx] at hrel; cases hrel
  | some c' => rw [hx] at hrel; cases hrel with | some hc => exact ⟨c', rfl, hc⟩

/-- **An action available at `db` is available at any `D` containing it, with the same
effect.** The result is an existential over a database containing the smaller one, not
the exact join `MergeStep.diamond_of_join` asks for; the evaluation reads only `sig` and
`env`, which is what makes the witnesses survive. -/
theorem evalAction_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : evalAction db a = some d) :
    ∃ D', evalAction D a = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ | ⟨v, e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, rfl⟩ | ⟨f, args, out, as, vs, rfl, hv₁, hv₂, rfl⟩
  · refine ⟨D.addTerm t, ?_, hc.addTerm_mono t, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · simpa using hsig
    · simpa using henv
  · refine ⟨{ D.addTerm t with env := (v, t) :: D.env }, ?_, ?_, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · exact ⟨(hc.addTerm_mono t).terms, (hc.addTerm_mono t).rows, (hc.addTerm_mono t).eqs⟩
    · simpa using hsig
    · simp [henv]
  · refine ⟨D.addEq t₁ t₂, ?_, hc.addEq_mono t₁ t₂, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv
  · refine ⟨D.addRow f as vs, ?_, hc.addRow_mono f as vs, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv

/-- `evalAction_mono` over a block: each step re-bases onto the previous one's larger
result. -/
theorem evalActions_mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : evalActions db as = some d) :
    ∃ D', evalActions D as = some D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction as generalizing db D with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨D, rfl, h ▸ hc, h ▸ hsig, h ▸ henv⟩
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := evalAction_mono hc hsig henv hv
      obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀ h
      exact ⟨D₁, by rw [evalActions_cons, hD₀, Option.bind_some]; exact hD₁, hc₁, hs₁, he₁⟩

/-- `evalAction_mono` along `Recorded`. An action never *reads* a row — `Expr.eval` takes
only a signature — so the proof is the `Contained` one with `Database.Recorded`'s
`addTerm`/`addEq`/`addRow` monotonicity in place of `Contained`'s. -/
theorem evalAction_mono_recorded {db D d : Database} (hc : db.Recorded D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : evalAction db a = some d) :
    ∃ D', evalAction D a = some D' ∧ d.Recorded D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, hv, rfl⟩ | ⟨v, e, t, rfl, hv, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, rfl⟩ | ⟨f, args, out, as, vs, rfl, hv₁, hv₂, rfl⟩
  · refine ⟨D.addTerm t, ?_, hc.addTerm_mono t, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · simpa using hsig
    · simpa using henv
  · refine ⟨{ D.addTerm t with env := (v, t) :: D.env }, ?_, ?_, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv]
    · exact (hc.addTerm_mono t).setEnv _ _
    · simpa using hsig
    · simp [henv]
  · refine ⟨D.addEq t₁ t₂, ?_, hc.addEq_mono t₁ t₂, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv
  · refine ⟨D.addRow f as vs, ?_, hc.addRow_mono f as vs, ?_, ?_⟩
    · simp [evalAction, ← hsig, ← henv, hv₁, hv₂]
    · simpa using hsig
    · simpa using henv

/-- `evalActions_mono` along `Recorded`. -/
theorem evalActions_mono_recorded {db D d : Database} (hc : db.Recorded D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : evalActions db as = some d) :
    ∃ D', evalActions D as = some D' ∧ d.Recorded D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction as generalizing db D with
  | nil =>
    rw [evalActions_nil, Option.some.injEq] at h
    exact ⟨D, rfl, h ▸ hc, h ▸ hsig, h ▸ henv⟩
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      rw [evalActions_cons, hv, Option.bind_some] at h
      obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := evalAction_mono_recorded hc hsig henv hv
      obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀ h
      exact ⟨D₁, by rw [evalActions_cons, hD₀, Option.bind_some]; exact hD₁, hc₁, hs₁, he₁⟩

/-- **A merge collision available at `A` is available at any `C` containing it.**

No `env`/`rules` hypothesis is needed: a `MergeStep` overwrites the environment with
`mergeEnv a b` before running the body and restores the caller's `env`/`rules`
afterwards, so neither field is ever read. `sig` is needed, because `CongList.mono` is.
-/
theorem MergeStep.transport {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (h : MergeStep A B) : ∃ D, MergeStep C D ∧ B.Contained D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f as bs a b vs body res hra hrb hcong hm hbody hres =>
    have hc0 : ({ A with env := mergeEnv a b } : Database).Contained
        { C with env := mergeEnv a b } := ⟨hc.terms, hc.rows, hc.eqs⟩
    obtain ⟨dC, hstepC, hcont, hsig', henv'⟩ := evalActions_mono hc0 hsig rfl hbody
    refine ⟨{ dC.addRow f as vs with env := C.env, rules := C.rules },
      .collide (hc.rows hra) (hc.rows hrb) (CongList.mono hc hcong)
        (by rw [← hsig]; exact hm) hstepC
        (hsig' ▸ henv' ▸ hres), ?_, ?_⟩
    · exact ⟨(hcont.addRow_mono f as vs).terms, (hcont.addRow_mono f as vs).rows,
        (hcont.addRow_mono f as vs).eqs⟩
    · simpa using hsig'

/-- `MergeStep.transport` iterated: a closure from `A` re-bases onto one from any `C`
containing `A`. This is the composition step of `mergeSaturateF_contained`. -/
theorem MergeClosure.transport {A C B : Database} (hc : A.Contained C)
    (hsig : A.sig = C.sig) (h : MergeClosure A B) :
    ∃ D, MergeClosure C D ∧ B.Contained D ∧ B.sig = D.sig := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, hc, hsig⟩
  | tail _ hstep ih =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ := ih
    obtain ⟨D', hstepD', hcont', hsig'⟩ := hstep.transport hcontD hsigD
    exact ⟨D', hclD.tail hstepD', hcont', hsig'⟩

/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than `exec`'s on
purpose: with a `:merge` function in play the spec admits several results, so the
interpreter's is one of them rather than *the* one. -/
/-- **The constructor interpreter lands where the specification does.** `exec_programStep`
proves the two directions at once; this is the half the merge interpreter below cannot
have, kept under its own name because that contrast is the point.

**The one hypothesis**, not removable: `Program.CtorDecls` gives
`Signature.AllConstructors` at every intermediate state
(`Signature.AllConstructors.sigBind`), which is what makes `MergeStep` vacuous and so how
the `MergeClosure` phase of `CmdStep.action` gets discharged
(`MergeClosure.eq_of_allConstructors`). `Falsity.exec_programStep_needs_ctorDecls` is the
witness that dropping it is false. -/
theorem execM_reachable {p : Program} {d : FDatabase} (hdecl : p.CtorDecls)
    (h : exec p = some d) :
    ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  rw [FDatabase.toDatabase_empty]
  exact (exec_programStep hdecl).mp (by rw [h, Option.map_some])

/-! ### The contract for `execM`: containment, not reachability

`execM_reachable`'s shape is unavailable for `execM`, and not because it is hard —
because it is **false**. The implementation's merge phase deletes the rows it merged and
the specification never deletes, so no `ProgramStep` state equals the implementation's:
a spec run that performed the same merges still holds the two originals, and a spec run
that performed none holds no combined row. `execM_reachable` above survives only because
`exec` is `Impl/Interp.lean`'s constructor interpreter, which has no merge phase at all
(`FDatabase.mergeRound_eq_self` and `hasMergeRow_eq_false`) — the layering is intact.

What replaces it is that every row the implementation holds is one the specification
*records* — `Database.Recorded` — so the implementation may find **fewer** results, never
more. That is the safe direction, because everything the M11 safety theorem reads is
positive in the state, so safety transfers downward. `ValidSubst.mono_recorded` is the
step that makes "fewer rows" mean "fewer matches" rather than merely "a different
database".

Two things push the contract off plain `Database.Contained`, and each buys one clause of
`Recorded`. The **deletion** adds the obligation that the witness `db` can be chosen to
have performed *at least* the merges the implementation did, which is where
`MergeClosure`'s freedom to take any number of steps is spent. The **rebuild** moves a row
onto the canonical key of its class, where no specification row is, so the row clause has
to be read through `Database.Out` — which searches the class and therefore sees it. Nothing
semantically new is claimed: `Out` is the only read there is.

#### The refinement chain

A step-by-step account of the merge interpreter against the merge specification. It runs
from `Inv` preservation through evaluation, actions and matching to containment, and it
is proved all the way to `execM_contained`. What is left over is
`execM_current_of_lattice`, which wants more than containment.

`execCmdM_contained` was once false, and the defect was in the *specification*:
`CmdStep.action` had no merge phase and `execCmdM` runs one, so the interpreter reached a
state holding a merge result no `CmdStep` state held. `CmdStep.action` now carries a
`MergeClosure`, which is what egglog does — a bare top-level action is compiled into a
one-rule run and every rule-set run ends in `merge_all`.

The chain needs no bridge at the congruence step, and that is the point of keeping one
relation: `patternHolds` compares keys with `congrKeys` at the closure of the database
extended with the atom's operands, `closureF` closes over `eqsF` and `congrPair` with no
notion of a row, and the specification's row atom compares them with the same `Cong`.

What the induction does have to carry is `Inv` — the well-formedness the merge passes
consume. Prove its preservation lemmas first; the rest of the chain is structural
recursion once they are available. -/

/-- The invariant the refinement chain carries.

`wf` is what `mem_closureF_iff_of_wf` needs; `ctorTerms` and `ctorRows` are what tell the
merge passes which rows are a constructor's, so that they leave them alone;
`rowsComplete` and `rowsWF` are the other two thirds of `Database.Solid`, which
`Database.Recorded.addRow_congr` reads. All five hold of `FDatabase.empty`.

`ctorRows` is also `Proofs/Congruence.lean`'s `Cong.fd` hypothesis, with its guard widened
from `IsCtor r.fn` to `mergeOf r.fn = none`: it is the reverse inclusion `RowsComplete`
omits, restricted to the functions where it survives a `:merge` declaration, and
`Action.SetLegal` is what preserves it. -/
structure FDatabase.Inv (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete
  rowsWF : d.toDatabase.RowsWF
  ctorRows : ∀ r ∈ d.toDatabase.rows, d.sig.mergeOf r.fn = none →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.toDatabase.terms

/-- The `sig`/`terms`/`rows` half of `FDatabase.Inv`, on a spec database. Everything but
`wf` constrains only those three fields, so it is proved once here and transported through
the `toDatabase_*` bridges. -/
structure Database.Inv0 (db : Database) : Prop where
  ctorTerms : db.CtorTerms
  rowsComplete : db.RowsComplete
  rowsWF : db.RowsWF
  ctorRows : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = none →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms

namespace Database

namespace Inv0

theorem addTerm {db : Database} (h : db.Inv0) {t : Term}
    (ht : Term.CtorTerm db.sig t) : (db.addTerm t).Inv0 where
  ctorTerms := by
    rintro f as (hm | hm)
    · exact h.ctorTerms f as hm
    · exact ht f as hm
  rowsComplete := by
    rintro r ⟨hout, hm | hm⟩
    · exact Or.inl (h.rowsComplete ⟨hout, hm⟩)
    · exact Or.inr ⟨hout, hm⟩
  rowsWF := by
    rintro r (hr | ⟨hout, hm⟩)
    · exact ⟨fun a ha => Or.inl ((h.rowsWF r hr).1 a ha),
        fun v hv => Or.inl ((h.rowsWF r hr).2 v hv)⟩
    · refine ⟨fun a ha => Or.inr ?_, ?_⟩
      · exact Term.subterms_subset_of_mem hm (Term.IsSubterm.arg ha (Term.IsSubterm.refl a))
      · intro v hv
        rw [hout] at hv
        rcases List.mem_singleton.mp hv with rfl
        exact Or.inr hm
  ctorRows := by
    rintro r (hr | ⟨hout, hm⟩) hf
    · exact ⟨(h.ctorRows r hr hf).1, Or.inl (h.ctorRows r hr hf).2⟩
    · exact ⟨hout, Or.inr hm⟩

theorem addTerms {db : Database} (h : db.Inv0) {ts : List Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm db.sig t) : (db.addTerms ts).Inv0 := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih =>
    exact ih (h.addTerm (hts t (by simp))) fun s hs => hts s (by simp [hs])

theorem addEq {db : Database} (h : db.Inv0) {a b : Term}
    (ha : Term.CtorTerm db.sig a) (hb : Term.CtorTerm db.sig b) : (db.addEq a b).Inv0 :=
  let h' := (h.addTerm ha).addTerm hb
  ⟨h'.ctorTerms, h'.rowsComplete, h'.rowsWF, h'.ctorRows⟩

theorem addRow {db : Database} (h : db.Inv0) {f : FnName} {as vs : List Term}
    (hf : db.sig.mergeOf f ≠ none)
    (has : ∀ a ∈ as, Term.CtorTerm db.sig a) (hvs : ∀ v ∈ vs, Term.CtorTerm db.sig v) :
    (db.addRow f as vs).Inv0 := by
  have h' : ((db.addTerms as).addTerms vs).Inv0 :=
    (h.addTerms has).addTerms (by simpa using hvs)
  refine ⟨h'.ctorTerms, h'.rowsComplete.trans (Set.subset_insert _ _), ?_, ?_⟩
  · rintro r (rfl | hr)
    · exact ⟨fun a ha => Contained.addTerms vs _ |>.terms (mem_terms_addTerms ha),
        fun v hv => mem_terms_addTerms hv⟩
    · exact h'.rowsWF r hr
  · rintro r (rfl | hr) hmf
    · exact absurd (by simpa using hmf) hf
    · exact h'.ctorRows r hr hmf

end Inv0
end Database

namespace FDatabase

/-- The three fields `Database.Recorded.addRow_congr` reads. -/
theorem Inv.solid {d : FDatabase} (h : d.Inv) : d.toDatabase.Solid :=
  ⟨h.wf, h.rowsWF, h.rowsComplete⟩

theorem Inv.toInv0 {d : FDatabase} (h : d.Inv) : d.toDatabase.Inv0 :=
  ⟨h.ctorTerms, h.rowsComplete, h.rowsWF, h.ctorRows⟩

theorem Inv.of_inv0 {d : FDatabase} (hw : d.WF) (h : d.toDatabase.Inv0) : d.Inv :=
  ⟨hw, h.ctorTerms, h.rowsComplete, h.rowsWF, h.ctorRows⟩

/-- The `addRow` companion to `WF.addTerm` and `WF.addEq`. -/
theorem WF.addRow {d : FDatabase} (h : d.WF) (f : FnName) (as vs : List Term) :
    (d.addRow f as vs).WF := by
  show (d.addRow f as vs).toDatabase.WF
  rw [toDatabase_addRow]
  exact Database.WF.addRow h f as vs

end FDatabase

theorem FDatabase.Inv.empty : FDatabase.empty.Inv := by
  refine ⟨FDatabase.empty_wf, ?_, ?_, ?_, ?_⟩ <;>
    simp [FDatabase.empty, FDatabase.toDatabase, Database.CtorTerms, Database.RowsComplete,
      Database.RowsWF, Database.ctorRowsOf]

@[simp] theorem FDatabase.addTerms_sig {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).sig = d.sig := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

/-- `addTerm` takes an arbitrary `Term`, so it needs `ht`: inserting an application of a
`:merge` function would put a non-constructor into `terms` and break `ctorTerms`. -/
theorem FDatabase.Inv.addTerm {d : FDatabase} (h : d.Inv) {t : Term}
    (ht : Term.CtorTerm d.sig t) : (d.addTerm t).Inv := by
  refine Inv.of_inv0 (h.wf.addTerm t) ?_
  rw [toDatabase_addTerm]
  exact h.toInv0.addTerm ht

/-- `Inv.addTerm` over a list. A merge firing inserts the terms of the combined row this
way, since it writes the row itself into the slot of the row it replaces. -/
theorem FDatabase.Inv.addTerms {d : FDatabase} (h : d.Inv) {ts : List Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm d.sig t) : (d.addTerms ts).Inv := by
  refine Inv.of_inv0 ?_ ?_
  · change (d.addTerms ts).toDatabase.WF
    rw [toDatabase_addTerms]
    exact Database.WF.addTerms h.wf ts
  · rw [toDatabase_addTerms]
    exact h.toInv0.addTerms hts

theorem FDatabase.Inv.addEq {d : FDatabase} (h : d.Inv) {a b : Term}
    (ha : Term.CtorTerm d.sig a) (hb : Term.CtorTerm d.sig b) : (d.addEq a b).Inv := by
  refine Inv.of_inv0 (h.wf.addEq a b) ?_
  rw [toDatabase_addEq]
  exact h.toInv0.addEq ha hb

/-- `hf` is what keeps `ctorRows` true — a `set` on anything but a merge function would add
a row that `ctorRows` then has to be a constructor row and is not, which is exactly what
`Action.SetLegal` rules out. `has`/`hvs` are `addTerm`'s condition on the operands. -/
theorem FDatabase.Inv.addRow {d : FDatabase} (h : d.Inv) {f : FnName} {as vs : List Term}
    (hf : d.sig.mergeOf f ≠ none)
    (has : ∀ x ∈ as, Term.CtorTerm d.sig x) (hvs : ∀ x ∈ vs, Term.CtorTerm d.sig x) :
    (d.addRow f as vs).Inv := by
  refine Inv.of_inv0 (h.wf.addRow f as vs) ?_
  rw [toDatabase_addRow]
  exact h.toInv0.addRow hf has hvs

/-- Every term the database holds is constructor-built: `subtermClosed` pushes the
application into `terms`, where `ctorTerms` reads it off. -/
theorem FDatabase.Inv.ctorTerm_of_mem {d : FDatabase} (h : d.Inv) {t : Term}
    (ht : t ∈ d.toDatabase.terms) : Term.CtorTerm d.sig t :=
  fun _ _ hsub => h.ctorTerms _ _ (h.wf.subtermClosed t ht hsub)

/-- The environment holds only constructor terms, since `WF.envInTerms` puts its values in
`terms`. -/
theorem FDatabase.Inv.env_ctorTerm {d : FDatabase} (h : d.Inv) :
    ∀ b ∈ d.env, Term.CtorTerm d.sig b.2 :=
  fun b hb => h.ctorTerm_of_mem (h.wf.envInTerms b hb)

theorem FDatabase.Inv.execAction {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hlegal : a.SetLegal d.sig) (hs : execAction d a = some d') : d'.Inv := by
  match a with
  | .expr e =>
    simp only [Egglog.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact h.addTerm (Expr.eval_ctorTerm h.env_ctorTerm ht)
  | .letBind v e =>
    simp only [Egglog.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hbase := h.addTerm (Expr.eval_ctorTerm h.env_ctorTerm ht)
    refine ⟨⟨hbase.wf.subtermClosed, hbase.wf.eqsInTerms, ?_⟩, hbase.ctorTerms,
      hbase.rowsComplete, hbase.rowsWF, hbase.ctorRows⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have hmem : t ∈ (d.addTerm t).terms := by
        simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
        exact Or.inl ((Term.mem_subtermList t).mpr (Term.IsSubterm.refl t))
      exact hmem
    · exact hbase.wf.envInTerms b hb
  | .union e₁ e₂ =>
    simp only [Egglog.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hs
    exact h.addEq (Expr.eval_ctorTerm h.env_ctorTerm ht₁)
      (Expr.eval_ctorTerm h.env_ctorTerm ht₂)
  | .set f args out =>
    simp only [Egglog.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨ts, hts, vs, hvs, rfl⟩ := hs
    exact h.addRow hlegal (Expr.evalList_ctorTerm h.env_ctorTerm hts)
      (Expr.evalList_ctorTerm h.env_ctorTerm hvs)


/-! #### Actions

There is nothing here any more. `Impl/Interp.lean`'s `execAction` and `execActions` are
the merge interpreter's action semantics too, and `Proofs/Interp.lean`'s
`execAction_toDatabase` already says they compute `evalAction`/`evalActions` — which
after M12 is what `CmdStep.action`, `RuleResults` and `MergeStep.collide` read. -/
/-- `execAction_toDatabase` in the `some` shape the merge proofs use. -/
theorem FDatabase.execAction_evalAction {d d' : FDatabase} {a : Action}
    (hs : execAction d a = some d') : evalAction d.toDatabase a = some d'.toDatabase := by
  rw [← execAction_toDatabase, hs, Option.map_some]

/-- `execActions_toDatabase` in the `some` shape the merge proofs use. -/
theorem FDatabase.execActions_evalActions {d d' : FDatabase} {as : List Action}
    (hs : execActions d as = some d') :
    evalActions d.toDatabase as = some d'.toDatabase := by
  rw [← execActions_toDatabase, hs, Option.map_some]

/-! #### Matching -/

/-- Every value visible to `Expr.eval` under `d.env ++ σ` is a constructor term, given
that `σ`'s values are terms `d` holds. `Expr.eval_ctorTerm`'s hypothesis, at the
environment `patternHolds` evaluates in. -/
theorem FDatabase.envAppend_ctorTerm {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ∀ b ∈ d.env ++ σ, Term.CtorTerm d.sig b.2 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact h.env_ctorTerm b hb
  · exact h.ctorTerm_of_mem (hσ b hb)

/-- **`patternHolds` is sound for `ValidSubst`.**

`ValidEnv (p.freeVars d.env) d.toDatabase σ` is load-bearing, not decoration.
`patternHolds` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the
pattern never mentions still passes the test, while `ValidSubst`'s `ValidEnv` pins
`Env.dom σ` to a permutation of the pattern's free variables —
`Falsity.patternHolds_validSubst_false` is the witness. Nothing is lost by requiring
it: it is a *consequence* of the conclusion (`ValidSubst.validEnv`), so this is the
strongest statement whose conclusion can hold, and it is the hypothesis
`Proofs/Interp.lean`'s `patternHolds_iff` already carries.

`Interp.lean`'s `patternHolds_iff`, forward direction, under `Inv` instead of `d.WF` —
which is what lets it be applied once a `:merge` function is declared. `congrKeys`
computes the same `Cong` that `ValidSubst` wants, so the only gap is that every case
closes over an *extended* database — `d.addTerm t` for `.expr`, and
`(d.addTerms ts).addTerms us` for the row atom's key and value operands — and `Inv` has
to be re-established there, from `Inv.addTerm`/`Inv.addTerms`. Those need the instance to
be a constructor term, which is `Expr.eval_ctorTerm`/`Expr.evalList_ctorTerm`, which in
turn need the `ValidEnv`. -/
theorem FDatabase.patternHolds_validSubst {d : FDatabase} (h : d.Inv) {p : Pattern}
    {σ : Env} (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ)
    (hs : patternHolds d p σ = true) : ValidSubst d.toDatabase p σ := by
  have hσ := FDatabase.envAppend_ctorTerm h hv.2
  cases p with
  | expr e =>
    rw [patternHolds] at hs
    split at hs
    · exact absurd hs (by simp)
    · next t hev =>
      rw [decide_eq_true_eq] at hs
      obtain ⟨w, hwm, hcl⟩ := hs
      exact ⟨hv, .expr hwm hev (congOn_singleton.mpr
        ((FDatabase.mem_closureF_addTerm h.wf).mp hcl))⟩
  | eq e₁ e₂ =>
    rw [patternHolds] at hs
    split at hs
    · next t₁ t₂ hev₁ hev₂ =>
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hs
      obtain ⟨heq, w, hwm, hcl⟩ := hs
      exact ⟨hv, .eq hwm hev₁ hev₂
        (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ h.wf).mp hcl))
        (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ h.wf).mp heq))⟩
    · exact absurd hs (by simp)
  | values vs f as =>
    rw [patternHolds] at hs
    split at hs
    · next us ts hu ht =>
      rw [List.any_eq_true] at hs
      obtain ⟨r, hr, hcond⟩ := hs
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hfn, hkey⟩, hval⟩ := hcond
      subst hfn
      exact ⟨hv, .values hu ht
        (congListOn_append.mpr ((FDatabase.congrTuple_addTerms_iff h.wf).mp hkey))
        (congListOn_append.mpr ((FDatabase.congrTuple_addTerms_iff h.wf).mp hval))
        hr⟩
    · exact absurd hs (by simp)

/-- **Every substitution the enumerator produces is, up to `Env.Agree`, one
`ValidQuerySubst` admits.**

The `Env.Agree` is forced, and not by the `ValidEnv` defect above. `Query.freeVars`
deduplicates, so `matchQuery` binds a variable two patterns share exactly **once**;
`ValidQuerySubst` instead demands `Env.UnionAll σs σ`, which is literal
*concatenation* of one substitution per pattern, each binding its own pattern's free
variables. A query with a repeated variable therefore admits no `σ` on the nose — the
lengths cannot match — and `Falsity.matchQuery_validQuerySubst_false` is the witness.
`Proofs/Interp.lean`'s `validQuerySubst_of_mem_matchQuery` already concludes up to
`Env.Agree` for the same reason. -/
theorem FDatabase.matchQuery_validQuerySubst {d : FDatabase} (h : d.Inv) {q : Query}
    {σ : Env} (hs : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  rw [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at hs
  obtain ⟨⟨hdom, hval⟩, hall⟩ := hs
  have hall' : ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) :=
    fun p hp =>
      FDatabase.patternHolds_validSubst h (validEnv_canon hp hdom hval) (hall p hp)
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars d.env) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self hall', hu⟩, Env.agree_of_refines hr ?_⟩
  -- `σ` binds only the query's free variables, and each is bound by some restriction
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars d.env) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp

/-! #### The merge phase and the round

These are the two containment steps, and the only places the *witness* has to be chosen
rather than computed. A merge pass deletes, so its result is not a `MergeClosure` state;
the specification state to compare against is one that took at least the same merges, and
`MergeClosure`'s freedom to take any number of steps is what pays for that.

`FDatabase.mergeRound_contained`, `mergeSaturateF_contained` and
`execRunRules_contained` are proved at the end of the file, under "Containment for the
merge interpreter": they read `mergeOneWith_inv`, `mergeOneWith_confined`,
`mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv` and `Inv.mergeRound_of_legalMerges`,
all of which are stated below. -/

/-! #### Commands and programs

`FDatabase.execCmdM_contained`, `FDatabase.execProgramM_contained` and `execM_contained`
are proved at the end of the file, under "Containment for a whole program", because they
read the whole chain. What is worth reading here is their **side conditions**, which are
this section's real output:

* a merge body is an action block nothing type-checks — `Cmd.SetLegal (.decl _ _)` is
  `True`, so `Program.SetLegal` says nothing about one, and without
  `Signature.MergesLegal` the accumulator's `Inv` fails at the first body that writes an
  illegal `set` (`Falsity.mergeRound_inv_false`);
* `FDatabase.Inv` does **not** survive an arbitrary declaration — `Falsity.claim1`
  machine-checks that declaring `g` `:merge` after `g ()` is already a term breaks
  `CtorTerms` — so a declaration has to name something the state does not yet mention
  (`FDatabase.Unused`), which is egglog's own "declare before use".

`FDatabase.ProgramLegal` bundles those two with `Cmd.SetLegal` and checks them at the
state each command actually runs in. -/

/-- **Completeness, so containment is not vacuous.**

A do-nothing implementation satisfies `execM_contained`, so containment needs a companion
saying the implementation keeps the *right* row and not merely a subset of the rows. For a
**lattice** merge that is exactly `Database.Current`, which is what `Current` was defined
for — "the single value it has when the merge is a join, used only where a result must
match egglog exactly".

`le` is a parameter rather than an instance because the order is per function and orders
whole rows. `hjoin` says the merge really is a `le`-join: whatever the body computes from
two colliding outputs is an upper bound of both. `hanti` is what makes the greatest
element unique (`Database.current_unique`). For a merge that is *not* a lattice there is no
`Current` to be complete against and nothing is claimed — `MERGE.md`'s "order-dependent
merges are the user's fault".

**False as stated.** `Proofs/Lattice.lean` refutes it three independent ways, all
machine-checked, and it stays false under the obvious repairs.

`hjoin` is an *implication*, so a merge that never fires satisfies it vacuously while
`Current` still demands `le vs vs` — instantiate its second conjunct at `ws := vs`. That is
the same defect `MergeStep.diamond_of_join`'s `hjoin` has, one statement above, and
`le := fun _ _ => False` refutes both. Giving `le` a genuine partial order does not save it
(`currentOfLattice_false_partialOrder`): when the merge body is stuck `mergeOneWith`
returns `none`, `settled` holds with two rows at one key class, and `Current` is
unsatisfiable at either. Nor does a *total* merge with reflexive `le`
(`currentOfLattice_false_total`): `hjoin` bounds one collision, and a class that collides
twice needs them to compose.

A corrected statement needs `hrefl`, `htrans`, `hjoin` strengthened from an implication to
the existence of a resolving merge, and `ProgramLegal`. Even then it may be false for
programs with rules: `MergeStep` never removes a row, so a specification state keeps every
superseded output and `Matches.values` lets a rule read one, writing rows the
implementation never had. That last part is unverified — `closureF` does not reduce in the
kernel, so no program containing a rule has an `execM` that evaluates by `rfl`. -/
theorem execM_current_of_lattice {p : Program} {d : FDatabase}
    {le : List Term → List Term → Prop} (hexec : execM p = some d)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (hjoin : ∀ (f : FnName) (body : List Action) (res : List Expr) (a b vs : List Term),
      d.sig.mergeOf f = some (MergeSpec.merge body res) →
      (∃ e, evalActions { d.toDatabase with env := mergeEnv a b } body = some e ∧
        Expr.evalList e.sig res e.env = some vs) → le a vs ∧ le b vs)
    {f : FnName} {as vs : List Term} {body : List Action} {res : List Expr}
    (hmerge : d.sig.mergeOf f = some (MergeSpec.merge body res))
    (hrow : Row.mk f as vs ∈ d.rows) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ db.Current le f as vs := by
  sorry

/-- The interpreter's merge phase against the specification's.

**Equality is false once the implementation deletes**, and **syntactic containment is
false once it re-keys.** `MergeClosure` is `Relation.ReflTransGen MergeStep` and
`MergeStep.contained` says every step only grows the state, so no `MergeClosure` reaches a
database with fewer rows; and a rebuild puts a row at a key no specification row has.
`Database.Recorded` is what survives both, and this is the merge-phase instance of
`execM_contained`.

Stated here with **no** hypothesis, which is why it is still open:
`FDatabase.mergeRound_contained` is this statement under `d.Inv` and `hlegal`, and both
are forced. `mergeOne` gates on `congrKeys d.closureF`, and `closureF` decides `Cong`
only for a well-formed database (`mem_closureF_iff_of_wf`), while `MergeStep` gates on
`CongList`; `Database.Recorded.refl` needs `RowsWF` on its own; and without `hlegal` the
accumulator's `Inv` fails at the first merge body that writes an illegal `set`
(`Falsity.mergeRound_inv_false`). What `mergeRound_confined` gives unconditionally is only
that the rows the pass drops are merge rows and nothing else. -/
theorem mergeRound_closure {d : FDatabase} :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Recorded db := by
  sorry

/-! ### The implementation deletes, the specification does not

`Spec/` is append-only and stays so: the M11 safety theorem is an invariant over
`MergeStep`, which needs neither termination nor confluence exactly because nothing is
removed, and the encoding depends on the same property to let proofs refer to terms after
they leave the e-graph. `Impl/Merge.lean`'s merge phase does **not** stay append-only,
because egglog's merge replaces the row: an append-only reference implementation is
faithful to our spec and unfaithful to the system the spec models.

So the contract between them weakens from an equality to a **containment**, which is the
safe direction — everything M11 reads is positive in the state, so an implementation that
finds fewer results cannot make a safety claim false. Two theorems carry that:
`FDatabase.mergeRound_confined`, that deletion touches nothing it must not, and
`ValidSubst.mono`, that fewer rows really do mean fewer matches. -/
namespace FDatabase

@[simp] theorem addRow_sig {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).sig = d.sig := by
  show ((d.addTerms as).addTerms vs).sig = d.sig
  rw [addTerms_sig, addTerms_sig]

/-- The interpreter's actions only add, so the only thing that ever removes a row is the
merge phase. `evalAction_contained` read through `toDatabase`. -/
theorem execAction_contained {d e : FDatabase} {a : Action}
    (h : execAction d a = some e) : d.toDatabase.Contained e.toDatabase := by
  cases a with
  | expr e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      rw [toDatabase_addTerm]
      exact Database.Contained.addTerm t d.toDatabase
  | letBind v e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => hx⟩
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
  | union e₁ e₂ =>
    cases hv₁ : Expr.eval d.sig e₁ d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : Expr.eval d.sig e₂ d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addEq]
        exact Database.Contained.addEq t₁ t₂ d.toDatabase
  | set f args out =>
    cases hv₁ : Expr.evalList d.sig args d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : Expr.evalList d.sig out d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addRow]
        exact Database.Contained.addRow f ts vs d.toDatabase

/-- The interpreter's actions do not touch the signature either, so which functions are
`.merge` functions is stable across a merge pass. -/
theorem execAction_sig {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    e.sig = d.sig := by
  cases a with
  | expr e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | letBind v e₀ =>
    cases hv : Expr.eval d.sig e₀ d.env with
    | none => rw [execAction, hv] at h; simp at h
    | some t =>
      rw [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | union e₁ e₂ =>
    cases hv₁ : Expr.eval d.sig e₁ d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : Expr.eval d.sig e₂ d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ rfl
  | set f args out =>
    cases hv₁ : Expr.evalList d.sig args d.env with
    | none => rw [execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : Expr.evalList d.sig out d.env with
      | none => rw [execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ addRow_sig

theorem execActions_contained {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : d.toDatabase.Contained e.toDatabase := by
  induction as generalizing d with
  | nil =>
    rw [execActions, Option.some.injEq] at h
    exact h ▸ Database.Contained.refl _
  | cons a as ih =>
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (execAction_contained hv).trans (ih h)

theorem execActions_sig {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => rw [execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_sig hv)

/-- `addRow` only adds, at the interpreter level. -/
theorem contained_addRow {d : FDatabase} {f : FnName} {as vs : List Term} :
    d.toDatabase.Contained (d.addRow f as vs).toDatabase := by
  rw [toDatabase_addRow]; exact Database.Contained.addRow f as vs d.toDatabase

/-- `addTerms` only adds, at the interpreter level. This is `contained_addRow` without the
row, which is what a merge firing needs: it inserts the combined row itself, in the slot
the row it replaces occupied. -/
theorem contained_addTerms {d : FDatabase} {ts : List Term} :
    d.toDatabase.Contained (d.addTerms ts).toDatabase := by
  rw [toDatabase_addTerms]; exact Database.Contained.addTerms ts d.toDatabase

/-- The rows a merge firing leaves in place: everything but `r₁`, with `r₂` overwritten by
the combined row. Membership in one direction; `mem_mergeRows` is the other. -/
theorem mem_mergeRows_of {rs : List Row} {r₁ r₂ r : Row} {vs : List Term} (hr : r ∈ rs)
    (h₁ : r ≠ r₁) (h₂ : r ≠ r₂) :
    r ∈ (rs.filter fun x => x ≠ r₁).map fun x =>
      if x = r₂ then (⟨r₂.fn, r₂.args, vs⟩ : Row) else x :=
  List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [h₁]⟩, by simp [h₂]⟩

/-- The rows a **no-conflict** firing leaves: everything but `r₁`. `mergeOneOriented`'s
`noConflict` branch runs no body and overwrites nothing, so the row list only shrinks.
Membership in one direction; `mem_dropRow` is the other. -/
theorem mem_dropRow_of {rs : List Row} {r₁ r : Row} (hr : r ∈ rs) (h₁ : r ≠ r₁) :
    r ∈ rs.filter fun x => x ≠ r₁ :=
  List.mem_filter.mpr ⟨hr, by simp [h₁]⟩

/-- A no-conflict firing leaves only rows that were already there. -/
theorem mem_dropRow {rs : List Row} {r₁ r : Row} (hr : r ∈ rs.filter fun x => x ≠ r₁) :
    r ∈ rs := (List.mem_filter.mp hr).1

/-- Every row a merge firing leaves is one that was there or the combined row. -/
theorem mem_mergeRows {rs : List Row} {r₁ r₂ r : Row} {vs : List Term}
    (hr : r ∈ (rs.filter fun x => x ≠ r₁).map fun x =>
      if x = r₂ then (⟨r₂.fn, r₂.args, vs⟩ : Row) else x) :
    r ∈ rs ∨ r = ⟨r₂.fn, r₂.args, vs⟩ := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  by_cases hq : s = r₂
  · exact Or.inr (by simp [hq])
  · exact Or.inl (by simpa [hq] using (List.mem_filter.mp hs).1)

/-- **One merge firing removes nothing it must not.**

The three prohibitions of the design, discharged: a merge deletes no term, no equality,
and no row of a function that is not the `.merge` function being merged. The last covers
both `.union` — constructor rows, which `Database.CtorRows` and the whole congruence
argument rest on — and `.noMerge`, which is how the proof encoding declares its proof
nodes, so deleting one would delete a proof.

The reason it holds is one line: the only rows dropped or overwritten are `r₁` and `r₂`
themselves, whose function is `r₁.fn`, and the branch was taken only because
`d.sig.mergeOf r₁.fn = .merge body res`. A row of any other kind of function is therefore
distinct from both. The `noConflict` branch drops `r₁` and nothing else, so the same line
covers it with `r₂` to spare. -/
theorem mergeOneOriented_confined {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (h : d.mergeOneOriented cl r₁ r₂ = some e) :
    d.toDatabase.terms ⊆ e.toDatabase.terms ∧ d.toDatabase.eqs ⊆ e.toDatabase.eqs ∧
      e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ e.rows := by
  unfold FDatabase.mergeOneOriented at h
  match hm : d.sig.mergeOf r₁.fn with
  | none => rw [hm] at h; simp at h
  | some .noMerge => rw [hm] at h; simp at h
  | some (.merge body res) =>
    rw [hm] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue hcond =>
      split at h
      case isTrue =>
        -- The no-conflict skip: `r₁` is dropped and nothing else moves.
        rw [Option.some.injEq] at h
        subst h
        refine ⟨subset_rfl, subset_rfl, rfl, fun r hr hnm => ?_⟩
        exact mem_dropRow_of hr fun hq => hnm body res (by rw [hq]; exact hm)
      case isFalse =>
        cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
        | none => rw [hb] at h; simp at h
        | some eb =>
          rw [hb, Option.bind_some] at h
          cases hv : Expr.evalList eb.sig res eb.env with
          | none => rw [hv] at h; simp at h
          | some vs =>
            rw [hv, Option.map_some, Option.some.injEq] at h
            subst h
            have hcb := execActions_contained hb
            have hsb := execActions_sig hb
            have hadd : eb.toDatabase.Contained ((eb.addTerms r₂.args).addTerms vs).toDatabase :=
              contained_addTerms.trans contained_addTerms
            refine ⟨fun x hx => hadd.terms (hcb.terms hx), fun q hq => hadd.eqs (hcb.eqs hq),
              ?_, fun r hr hnm => ?_⟩
            · show ((eb.addTerms r₂.args).addTerms vs).sig = d.sig
              rw [addTerms_sig, addTerms_sig]; exact hsb
            · have hrb : r ∈ ((eb.addTerms r₂.args).addTerms vs).rows := hadd.rows (hcb.rows hr)
              have hfn : r₁.fn = r₂.fn := by
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                exact hcond.1.1.1
              have hne : r ≠ r₁ ∧ r ≠ r₂ := by
                refine ⟨fun hq => hnm body res ?_, fun hq => hnm body res ?_⟩
                · rw [hq]; exact hm
                · rw [hq, ← hfn]; exact hm
              exact mem_mergeRows_of hrb hne.1 hne.2

/-- **A firing is a firing on one of the two orientations, and nothing else.**

`mergeOneWith` only chooses which colliding row is the one already in the table — that
is `swapForCanon`, and every fact below is indifferent to it, so each is proved once for
`mergeOneOriented` and transported through this. What the choice *does* change is which
`MergeStep` the firing refines, and `MergeStep.collide` has the two rows as premises in
both orders, so either is available. -/
theorem mergeOneWith_eq_oriented {cl : Finset (Term × Term)} {d : FDatabase} (r₁ r₂ : Row) :
    ∃ a b, d.mergeOneWith cl r₁ r₂ = d.mergeOneOriented cl a b := by
  unfold FDatabase.mergeOneWith
  split
  · exact ⟨r₂, r₁, rfl⟩
  · exact ⟨r₁, r₂, rfl⟩

/-- `mergeOneOriented_confined` at whichever orientation the firing took. -/
theorem mergeOneWith_confined {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) :
    d.toDatabase.terms ⊆ e.toDatabase.terms ∧ d.toDatabase.eqs ⊆ e.toDatabase.eqs ∧
      e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ e.rows := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂
  exact mergeOneOriented_confined (he ▸ h)

/-! #### The rebuild

`FDatabase.rebuild` re-keys every `:merge` row onto its class's canonical key, drops the
duplicates that creates and moves the re-keyed rows to the front. It writes `rows` and
nothing else, so `terms`, `eqs`, `sig`, `env` and `rules` come out untouched by `rfl` and
what has to be proved is only about rows: which they are, that the ones a merge may not
delete are still there, and that the specification records them. -/

/-- A fold that only ever keeps its accumulator or takes the new element lands on the
accumulator or on an element of the list that satisfies whatever the choice required.
`canonOf` is such a fold, and its two facts — the representative is a term the database
holds, and it is congruent to what it represents — are this lemma twice. -/
theorem foldl_pick {α : Type _} {P : α → Prop} {f : α → α → α}
    (hf : ∀ a u, f a u = a ∨ (f a u = u ∧ P u)) :
    ∀ (l : List α) (a : α), l.foldl f a = a ∨ (l.foldl f a ∈ l ∧ P (l.foldl f a)) := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons u l ih =>
    intro a
    rcases ih (f a u) with hh | ⟨hm, hp⟩
    · rcases hf a u with he | ⟨he, hpu⟩
      · exact Or.inl (by rw [List.foldl_cons, hh, he])
      · exact Or.inr ⟨by rw [List.foldl_cons, hh, he]; simp,
          by rw [List.foldl_cons, hh, he]; exact hpu⟩
    · exact Or.inr ⟨by rw [List.foldl_cons]; exact List.mem_cons_of_mem _ hm,
        by rw [List.foldl_cons]; exact hp⟩

/-- The representative is either the term itself, or a term the list holds and the closure
relates to it. -/
theorem canonOf_spec {cl : Finset (Term × Term)} {ts : List Term} {t : Term} :
    FDatabase.canonOf cl ts t = t ∨
      (FDatabase.canonOf cl ts t ∈ ts ∧
        (FDatabase.canonOf cl ts t = t ∨ (t, FDatabase.canonOf cl ts t) ∈ cl)) := by
  refine foldl_pick (P := fun u => u = t ∨ (t, u) ∈ cl) (fun a u => ?_) ts t
  by_cases hu : u == t || decide ((t, u) ∈ cl)
  · refine Or.inr ⟨by simp [hu], ?_⟩
    rcases Bool.or_eq_true .. |>.mp hu with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · exact Or.inl (by simp [hu])

/-- A row of a function without a `:merge` body is not re-keyed. -/
theorem rebuildRow_of_not_merge {cl : Finset (Term × Term)} {d : FDatabase} {r : Row}
    (h : ∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) :
    d.rebuildRow cl r = r := by
  unfold FDatabase.rebuildRow
  split
  · rename_i body res hm; exact absurd hm (h body res)
  · rfl

/-- A rebuilt row is a row of `d`, re-keyed — and every row of `d` contributes one. -/
theorem mem_rebuild_rows {cl : Finset (Term × Term)} {d : FDatabase} {r : Row} :
    r ∈ (FDatabase.rebuild cl d).rows ↔ ∃ s ∈ d.rows, r = d.rebuildRow cl s := by
  have hmap : ∀ b : Bool, (∃ p ∈ (d.rows.map fun s => (d.rebuildRow cl s, s)).filter
      fun p => (p.1 == p.2) == b, r = p.1) → ∃ s ∈ d.rows, r = d.rebuildRow cl s := by
    intro b ⟨p, hp, hr⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
    exact ⟨s, hs, hr⟩
  constructor
  · intro hr
    simp only [FDatabase.rebuild, List.mem_dedup, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨p, hp, hr⟩ | ⟨p, hp, hr⟩
    · exact hmap false ⟨p, by simpa using hp, hr.symm⟩
    · exact hmap true ⟨p, by simpa using hp, hr.symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hp : (d.rebuildRow cl s, s) ∈ d.rows.map fun x => (d.rebuildRow cl x, x) :=
      List.mem_map_of_mem hs
    simp only [FDatabase.rebuild, List.mem_dedup, List.mem_append, List.mem_map]
    by_cases hq : d.rebuildRow cl s = s
    · exact Or.inr ⟨(d.rebuildRow cl s, s), List.mem_filter.mpr ⟨hp, by simp [hq]⟩, rfl⟩
    · exact Or.inl ⟨(d.rebuildRow cl s, s), List.mem_filter.mpr ⟨hp, by simp [hq]⟩, rfl⟩

/-- **A rebuild removes nothing it must not.** Same three prohibitions as
`mergeOneOriented_confined`, and the reason is the same one line: only a `.merge`
function's rows are re-keyed, so a row of any other kind is its own image. -/
theorem rebuild_confined {cl : Finset (Term × Term)} {d : FDatabase} :
    d.toDatabase.terms ⊆ (FDatabase.rebuild cl d).toDatabase.terms ∧
      d.toDatabase.eqs ⊆ (FDatabase.rebuild cl d).toDatabase.eqs ∧
      (FDatabase.rebuild cl d).sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ (FDatabase.rebuild cl d).rows :=
  ⟨subset_rfl, subset_rfl, rfl,
    fun r hr hnm => mem_rebuild_rows.mpr ⟨r, hr, (rebuildRow_of_not_merge hnm).symm⟩⟩

/-- A rebuild restores the caller's environment and rule list, having never left them. -/
theorem rebuild_envRules {cl : Finset (Term × Term)} {d : FDatabase} :
    (FDatabase.rebuild cl d).env = d.env ∧ (FDatabase.rebuild cl d).rules = d.rules :=
  ⟨rfl, rfl⟩

/-- **A rebuild preserves the refinement-chain invariant.**

Each field for its own reason, and `ctorTerms` is what carries two of them: an application
the database holds is a *constructor* application, so a row whose output is one is a row of
a constructor, which no rebuild moves. Only `rowsWF` needs anything about the new keys, and
`canonOf_spec` is it. -/
theorem Inv.rebuild {cl : Finset (Term × Term)} {d : FDatabase} (h : d.Inv) :
    (FDatabase.rebuild cl d).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hctor : d.sig.IsCtor r.fn := by
      obtain ⟨hout, hm⟩ := hr
      have : Term.app r.fn r.args ∈ d.toDatabase.terms := hm
      exact h.ctorTerms r.fn r.args this
    exact mem_rebuild_rows.mpr ⟨r, h.rowsComplete hr,
      (rebuildRow_of_not_merge fun body res hb => by
        rw [hctor.mergeOf] at hb; exact absurd hb (by simp)).symm⟩
  rowsWF := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
    unfold FDatabase.rebuildRow
    split
    · refine ⟨?_, (h.rowsWF s hs).2⟩
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      rcases canonOf_spec (cl := cl) (ts := d.terms) (t := b) with he | ⟨hm, -⟩
      · rw [he]; exact (h.rowsWF s hs).1 b hb
      · exact hm
    · exact h.rowsWF s hs
  ctorRows := by
    intro r hr hu
    obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
    have hsame : d.rebuildRow cl s = s :=
      rebuildRow_of_not_merge fun body res hb => by
        have hfn : (d.rebuildRow cl s).fn = s.fn := by
          unfold FDatabase.rebuildRow; split <;> rfl
        rw [← hfn] at hb
        rw [show (FDatabase.rebuild cl d).sig = d.sig from rfl, hb] at hu
        exact absurd hu (by simp)
    rw [hsame] at hu ⊢
    exact h.ctorRows s hs hu

/-- **The specification records a rebuilt row.** A re-keyed row's key is congruent to the
one it came from, so `Database.Out` reads it from the original — which is the whole reason
the contract is `Database.Recorded` and not `Database.Contained`. -/
theorem rebuild_recorded {d : FDatabase} (h : d.Inv) :
    (FDatabase.rebuild d.closureF d).toDatabase.Recorded d.toDatabase := by
  have hcanon : ∀ a ∈ d.toDatabase.terms,
      Cong d.toDatabase (FDatabase.canonOf d.closureF d.terms a) a := by
    intro a hat
    rcases canonOf_spec (cl := d.closureF) (ts := d.terms) (t := a) with he | ⟨-, hp⟩
    · rw [he]; exact .refl hat
    · rcases hp with he | hcl
      · rw [he]; exact .refl hat
      · exact ((FDatabase.mem_closureF_iff_of_wf h.wf).mp hcl).symm
  have hcanonL : ∀ l : List Term, (∀ a ∈ l, a ∈ d.toDatabase.terms) →
      CongList d.toDatabase (l.map (FDatabase.canonOf d.closureF d.terms)) l := by
    intro l
    induction l with
    | nil => intro _; exact .nil
    | cons a l ih =>
      intro hl
      exact .cons (hcanon a (hl a (by simp))) (ih fun x hx => hl x (by simp [hx]))
  refine ⟨subset_rfl, ?_, subset_rfl⟩
  intro r hr
  obtain ⟨s, hs, rfl⟩ := mem_rebuild_rows.mp hr
  unfold FDatabase.rebuildRow
  split
  · exact ⟨s.args, hcanonL s.args fun a ha => (h.rowsWF s hs).1 a ha, hs⟩
  · exact Database.out_self hs (h.rowsWF s hs).1

/-- **A merge pass removes nothing it must not.** `rebuild_confined`, then
`mergeOneWith_confined` through the two folds. This is the formal content of "`Impl/`
deletes merge rows only". -/
theorem mergeRound_confined {d : FDatabase} :
    d.toDatabase.terms ⊆ d.mergeRound.toDatabase.terms ∧
      d.toDatabase.eqs ⊆ d.mergeRound.toDatabase.eqs ∧ d.mergeRound.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) →
        r ∈ d.mergeRound.rows := by
  -- The invariant is exactly the conclusion, relative to the fixed starting database.
  let P : FDatabase → Prop := fun x =>
    d.toDatabase.terms ⊆ x.toDatabase.terms ∧ d.toDatabase.eqs ⊆ x.toDatabase.eqs ∧
      x.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ some (MergeSpec.merge body res)) → r ∈ x.rows
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      obtain ⟨ht, hq, hs, hr⟩ := mergeOneWith_confined hy
      refine ⟨hx.1.trans ht, hx.2.1.trans hq, hs.trans hx.2.2.1, fun r hrd hnm => ?_⟩
      exact hr r (hx.2.2.2 r hrd hnm) (by rw [hx.2.2.1]; exact hnm)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hb : r₁ == r₂
      · simpa [hb] using hx
      · simpa [hb] using hstep x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  have hinit : P d := ⟨subset_rfl, subset_rfl, rfl, fun r hr _ => hr⟩
  have hreb : P (FDatabase.rebuild d.closureF d) :=
    ⟨rebuild_confined.1, rebuild_confined.2.1, rebuild_confined.2.2.1,
      fun r hr hnm => rebuild_confined.2.2.2 r hr hnm⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter _ _ _ hreb

/-- **On the constructor fragment nothing is deleted, because nothing merges.** With every
function a constructor no row belongs to a `.merge` function, `hasMergeRow` is false and
the pass is the identity — which is why `Impl/Interp.lean`'s `exec` and the equality
`exec_programStep` are untouched by any of this, and, via `execM_eq_exec` below, why the
differential test constrains them. -/
theorem hasMergeRow_eq_false {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.hasMergeRow = false := by
  simp only [FDatabase.hasMergeRow, List.any_eq_false]
  intro r _
  rw [hsig r.fn]
  simp

theorem mergeRound_eq_self {d : FDatabase} (h : d.hasMergeRow = false) :
    d.mergeRound = d := by
  unfold FDatabase.mergeRound
  simp [h]

theorem mergeSaturateF_eq_self {d : FDatabase} (h : d.hasMergeRow = false) {n : Nat} :
    FDatabase.mergeSaturateF n d = some d := by
  have hs : d.settled = true := by
    simp [FDatabase.settled, mergeRound_eq_self h]
  cases n <;> simp [FDatabase.mergeSaturateF, hs]

end FDatabase

/-! ### The two interpreters agree on the constructor fragment

`Program.expectedSizes` — what the differential test runs — calls `execM`, and
`exec_programStep` is stated about `exec`. Without an equation between them the chain from
a passing difftest case back to `Spec/` has a hole in it. `execCmdM` differs from
`execCmd` only by a `mergeSaturateF` after each command, and with no `:merge` function
declared there is no merge row for a pass to fire on, so that call is the identity. -/
/-- The signature a command leaves, for `Impl/Interp.lean`'s interpreter. This is what
carries `Signature.AllConstructors` along a run. -/
theorem execCmd_sig {d d' : FDatabase} {c : Cmd} (hs : execCmd d c = some d') :
    d'.sig = c.sigBind d.sig := by
  cases c with
  | action a => exact FDatabase.execAction_sig hs
  | rule r => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ rfl
  | run => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ sig_execRunRules
  | decl f dc => simp only [execCmd, Option.some.injEq] at hs; exact hs ▸ rfl

theorem execProgramM_eq_execProgram {d : FDatabase} (hsig : d.sig.AllConstructors)
    {p : Program} (hdecl : p.CtorDecls) : d.execProgramM p = execProgram d p := by
  induction p generalizing d with
  | nil => rfl
  | cons c cs ih =>
    have hc : d.execCmdM c = execCmd d c := by
      cases c with
      | action a =>
        show (execAction d a).bind (FDatabase.mergeSaturateF mergeFuel) = execAction d a
        cases hv : execAction d a with
        | none => rfl
        | some e =>
          rw [Option.bind_some, FDatabase.mergeSaturateF_eq_self
            (FDatabase.hasMergeRow_eq_false (by rw [FDatabase.execAction_sig hv]; exact hsig))]
      | rule r => rfl
      | run =>
        show FDatabase.mergeSaturateF mergeFuel (execRunRules d) = some (execRunRules d)
        exact FDatabase.mergeSaturateF_eq_self
          (FDatabase.hasMergeRow_eq_false (by rw [sig_execRunRules]; exact hsig))
      | decl f dc => rfl
    show (d.execCmdM c).bind (fun d' => d'.execProgramM cs)
      = (execCmd d c).bind fun d' => execProgram d' cs
    rw [hc]
    cases hv : execCmd d c with
    | none => rfl
    | some e =>
      rw [Option.bind_some, Option.bind_some]
      exact ih (by rw [execCmd_sig hv]; exact hsig.sigBind (hdecl c (by simp)))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-- **`execM` is `exec` on the constructor fragment.** This is the link that makes a
differential-test case say something about `Spec/`: `Program.expectedSizes` runs `execM`,
this carries it to `exec`, and `exec_programStep` carries that to `ProgramStep`. -/
theorem execM_eq_exec {p : Program} (hdecl : p.CtorDecls) : execM p = exec p :=
  execProgramM_eq_execProgram (d := FDatabase.empty)
    (by intro f; simp [Signature.mergeOf, FDatabase.empty]) hdecl


/-- **Row counts do not observe the merge phase.**

`rowCount` counts congruence classes of *keys*. A merge step writes its combined row at a
key already present, and a merge with an empty action block writes nothing else, so a
merge pass leaves every count alone.

This is what lets the differential test compare row counts while the interpreter runs
only one merge pass instead of saturating — and it is also why keeping every superseded
output, the over-approximation the design rests on, does not inflate the number: three
recorded values at one key are still one row. Both halves of `PLAN.md`'s row-count oracle
survive into M9 because of it.

**False as stated.** `hpure` bounds the merge's *action block* but not its *result*, and
`FDatabase.addRow` inserts the result's terms together with their constructor rows —
so a merge whose result builds an application adds a key class to a *different*
function's table. Counterexample, with `k` any term:

```
d.sig  = fun n => if n = "f" then some ⟨1, 1, .merge [] [.app "F" [.var "old"]]⟩ else none
d.terms = [k],  d.rows = [⟨"f", [k], [k]⟩],  d.eqs = []
```

`hpure` holds (the only block is `[]`). The row collides with itself — `CongList` is
reflexive and `closureF` has `(k, k)` — so `mergeRound` fires, the result evaluates to
`F k`, and `addRow "f" [k] [F k]` writes the constructor row `⟨F, [k], [F k]⟩`. Then
`d.mergeRound.keyRowCount "F" = 1` while `d.keyRowCount "F" = 0`.

The theorem the difftest actually relies on is the same statement with `hpure`
strengthened to "the merge result is a term the database already holds" — under which
`addRow` adds no key class anywhere, which is the argument the docstring gives. Every
generated merge case satisfies it (results are `i64` literals). -/
theorem FDatabase.mergeRound_rowCount {d : FDatabase} (f : FnName)
    (hpure : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) → body = []) :
    d.mergeRound.keyRowCount f = d.keyRowCount f := by
  sorry

/-! ### Well-formedness -/
/-- Every binding a merge body's environment provides is one of the two colliding rows'
outputs. This is what `MergeStep.wf` needs `RowsWF` for: `WF.envInTerms` has to hold of
`mergeEnv a b` before the body runs. -/
theorem mem_mergeEnvIdx {i : Nat} {os ns : List Term} {p : Var × Term}
    (h : p ∈ mergeEnvIdx i os ns) : p.2 ∈ os ∨ p.2 ∈ ns := by
  induction os generalizing i ns with
  | nil => simp [mergeEnvIdx] at h
  | cons o os ih =>
    cases ns with
    | nil => simp [mergeEnvIdx] at h
    | cons n ns =>
      simp only [mergeEnvIdx, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih h).imp (fun hm => by simp [hm]) fun hm => by simp [hm]

theorem mem_mergeEnv {os ns : List Term} {p : Var × Term} (h : p ∈ mergeEnv os ns) :
    p.2 ∈ os ∨ p.2 ∈ ns := by
  unfold mergeEnv at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · exact mem_mergeEnvIdx h

/-! #### The merge phase

`mergeRound` does **not** preserve `Inv` unconditionally. A merge body is an arbitrary
`List Action` carrying no `Action.SetLegal` obligation, so a `(set (F) ...)` inside one, on
a constructor `F`, writes a `.union` function's row whose output is not `[.app F args]` —
which is exactly what `ctorRows` forbids. `mergeRound_inv_false` in the counterexample
section machine-checks it. `CtorTerms` *is* preserved, as the `Inv` docstring claims:
`Expr.eval` builds an application only under a `.union` guard, and every other branch
returns an operand, a literal, or a recorded row output that `rowsWF` already places in
`terms`.

The hypothesis below is the repair: every declared merge's body obeys the same `set`
discipline every other action block obeys. The gap it patches is in the specification —
`Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about merge
bodies. -/

namespace FDatabase

theorem Inv.setEnv {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ } : FDatabase).Inv :=
  ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, hσ⟩, h.ctorTerms, h.rowsComplete, h.rowsWF,
    h.ctorRows⟩

theorem Inv.setEnvRules {d : FDatabase} (h : d.Inv) {σ : Env} {rs : List Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ, rules := rs } : FDatabase).Inv :=
  ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, hσ⟩, h.ctorTerms, h.rowsComplete, h.rowsWF,
    h.ctorRows⟩

/-- **`Inv` survives a merge firing's rewrite of the row list**: `r₁` dropped, and `r₂`
overwritten where it stands by the combined row.

Both hypotheses are about the *signature*, not about the two rows, and that is the whole
argument: a `.merge` function's row is never a constructor row, so neither `rowsComplete`
— which demands every constructor row of `terms` be present — nor `ctorRows` — which reads
one back — can be talking about `r₁` or `r₂`. `hvs` is why the combined row is written
after `addTerms` and not before: `rowsWF` needs its value columns already held. -/
theorem Inv.mergeRows {d : FDatabase} (h : d.Inv) {r₁ r₂ : Row} {vs : List Term}
    (h₁ : d.sig.mergeOf r₁.fn ≠ none)
    (h₂ : d.sig.mergeOf r₂.fn ≠ none)
    (hargs : ∀ a ∈ r₂.args, a ∈ d.toDatabase.terms)
    (hvs : ∀ v ∈ vs, v ∈ d.toDatabase.terms) :
    ({ d with rows := (d.rows.filter fun r => r ≠ r₁).map fun r =>
        if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hu : d.sig.mergeOf r.fn = none := (h.ctorTerms r.fn r.args hr.2).mergeOf
    exact mem_mergeRows_of (h.rowsComplete hr) (fun hq => h₁ (hq ▸ hu))
      (fun hq => h₂ (hq ▸ hu))
  rowsWF := by
    intro r hr
    rcases mem_mergeRows hr with hr' | rfl
    · exact h.rowsWF r hr'
    · exact ⟨hargs, hvs⟩
  ctorRows := by
    intro r hr hu
    rcases mem_mergeRows hr with hr' | rfl
    · exact h.ctorRows r hr' hu
    · exact absurd hu h₂

/-- **`Inv` survives a no-conflict firing's rewrite of the row list**: `r₁` dropped, and
nothing put back.

`Inv.mergeRows` without its second row and without the combined row, so it needs neither
`hargs` nor `hvs` — the rows that remain were already there, and the one hypothesis left
is `rowsComplete`'s: a `.merge` function's row is never a constructor row, so dropping
`r₁` cannot drop one the invariant demands. -/
theorem Inv.dropRow {d : FDatabase} (h : d.Inv) {r₁ : Row}
    (h₁ : d.sig.mergeOf r₁.fn ≠ none) :
    ({ d with rows := d.rows.filter fun r => r ≠ r₁ } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hu : d.sig.mergeOf r.fn = none := (h.ctorTerms r.fn r.args hr.2).mergeOf
    exact mem_dropRow_of (h.rowsComplete hr) fun hq => h₁ (hq ▸ hu)
  rowsWF := fun r hr => h.rowsWF r (mem_dropRow hr)
  ctorRows := fun r hr => h.ctorRows r (mem_dropRow hr)

/-- `Inv` through a whole action block, given every `set` in it is legal. `Inv.execAction`
iterated; `execAction_sig` is what keeps `SetLegal` — a condition on the signature —
applicable at each step. -/
theorem Inv.execActions {as : List Action} : ∀ {d d' : FDatabase}, d.Inv →
    Actions.SetLegal as d.sig → execActions d as = some d' → d'.Inv := by
  induction as with
  | nil =>
    intro d d' h _ hs
    rw [Egglog.execActions, Option.some.injEq] at hs
    exact hs ▸ h
  | cons a as ih =>
    intro d d' h hlegal hs
    obtain ⟨hl₁, hl₂⟩ := hlegal
    cases hv : Egglog.execAction d a with
    | none => rw [Egglog.execActions, hv] at hs; simp at hs
    | some d₁ =>
      rw [Egglog.execActions, hv, Option.bind_some] at hs
      refine ih (h.execAction hl₁ hv) ?_ hs
      rw [execAction_sig hv]
      exact hl₂

set_option maxHeartbeats 1000000 in
/-- **One merge firing preserves `Inv`, provided the merge body's `set`s are legal.**

Four steps, each a lemma above. Rebinding `env` to `mergeEnv r₂.out r₁.out` is harmless
because `rowsWF` puts both rows' outputs in `terms`. Running the body preserves `Inv` by
`Inv.execActions`, which is exactly where `hlegal` is spent. The combined row's operands
are constructor terms by `Expr.evalList_ctorTerm`, so `Inv.addTerms` takes them into
`terms`. And rewriting the row list — `r₁` dropped, `r₂` overwritten — is `Inv.mergeRows`,
whose side condition is that both rows belong to a `.merge` function, which is how the
branch was entered. The `noConflict` branch runs none of the four: it only drops `r₁`,
which is `Inv.dropRow` with the same side condition. -/
theorem mergeOneOriented_inv {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    (hm : d.mergeOneOriented cl r₁ r₂ = some e) : e.Inv := by
  unfold FDatabase.mergeOneOriented at hm
  match hmo : d.sig.mergeOf r₁.fn with
  | none => rw [hmo] at hm; simp at hm
  | some .noMerge => rw [hmo] at hm; simp at hm
  | some (.merge body res) =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, -⟩, hr₁⟩, hr₂⟩ := hcond
      split at hm
      case isTrue =>
        rw [Option.some.injEq] at hm
        subst hm
        exact h.dropRow (by rw [hmo]; simp)
      case isFalse =>
      have hσ : ∀ b ∈ mergeEnv r₂.out r₁.out, b.2 ∈ d.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact (h.rowsWF r₂ hr₂).2 b.2 hb'
        · exact (h.rowsWF r₁ hr₁).2 b.2 hb'
      have h₀ : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).Inv := h.setEnv hσ
      cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        have hsig : eb.sig = d.sig :=
          execActions_sig (d := { d with env := mergeEnv r₂.out r₁.out }) hb
        have hebInv : eb.Inv := h₀.execActions (hlegal r₁.fn body res hmo) hb
        have hcont : d.toDatabase.terms ⊆ eb.toDatabase.terms :=
          (execActions_contained (d := { d with env := mergeEnv r₂.out r₁.out }) hb).terms
        have hvsCtor : ∀ x ∈ vs, Term.CtorTerm eb.sig x :=
          Expr.evalList_ctorTerm hebInv.env_ctorTerm hv
        have hasCtor : ∀ x ∈ r₂.args, Term.CtorTerm eb.sig x := fun x hx =>
          hebInv.ctorTerm_of_mem (hcont ((h.rowsWF r₂ hr₂).1 x hx))
        have hInv₀ : ((eb.addTerms r₂.args).addTerms vs).Inv :=
          (hebInv.addTerms hasCtor).addTerms (by simpa using hvsCtor)
        have hsig₀ : ((eb.addTerms r₂.args).addTerms vs).sig = d.sig := by
          rw [addTerms_sig, addTerms_sig]; exact hsig
        have hne₁ : ((eb.addTerms r₂.args).addTerms vs).sig.mergeOf r₁.fn ≠ none := by
          rw [hsig₀, hmo]; simp
        have hne₂ : ((eb.addTerms r₂.args).addTerms vs).sig.mergeOf r₂.fn ≠ none := by
          rw [← hfn]; exact hne₁
        have hargs : ∀ a ∈ r₂.args,
            a ∈ ((eb.addTerms r₂.args).addTerms vs).toDatabase.terms := by
          intro a ha
          refine contained_addTerms.terms ?_
          rw [toDatabase_addTerms]
          exact Database.mem_terms_addTerms ha
        have hvsMem : ∀ v ∈ vs,
            v ∈ ((eb.addTerms r₂.args).addTerms vs).toDatabase.terms := by
          intro v hvm
          rw [toDatabase_addTerms]
          exact Database.mem_terms_addTerms hvm
        refine (hInv₀.mergeRows hne₁ hne₂ hargs hvsMem).setEnvRules ?_
        intro b hb'
        exact (contained_addTerms.trans contained_addTerms).terms
          (hcont (h.wf.envInTerms b hb'))

/-- `mergeOneOriented_inv` at whichever orientation the firing took. -/
theorem mergeOneWith_inv {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.Inv := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂
  exact mergeOneOriented_inv h hlegal (he ▸ hm)

/-- **A merge pass preserves the refinement-chain invariant, provided every declared
merge's action block writes only legal `set`s.** `mergeOneWith_inv` through the two folds
of `mergeRound`, exactly as `mergeRound_confined` threads `mergeOneWith_confined`. The
accumulator also carries `sig = d.sig`, which is what lets `hlegal` — a statement about
the *pre-pass* signature — apply at every intermediate state. -/
theorem Inv.mergeRound_of_legalMerges {d : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig) :
    d.mergeRound.Inv := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      have hs : y.sig = x.sig := (mergeOneWith_confined hy).2.2.1
      refine ⟨mergeOneWith_inv hx.1 (fun g body res hg => ?_) hy, hs.trans hx.2⟩
      exact hx.2 ▸ hlegal g body res (hx.2 ▸ hg)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  have hinit : P d := ⟨h, rfl⟩
  have hreb : P (FDatabase.rebuild d.closureF d) := ⟨h.rebuild, rfl⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit.1
  · exact (houter _ _ _ hreb).1

/-- The special case the task names: merge bodies are `[]`, which is `SetLegal` outright. -/
theorem Inv.mergeRound_of_pureMerges {d : FDatabase} (h : d.Inv)
    (hpure : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) → body = []) :
    d.mergeRound.Inv :=
  h.mergeRound_of_legalMerges fun g body res hg => by
    rw [hpure g body res hg]
    exact trivial

end FDatabase

/-- A merge preserves the invariants. `RowsWF` is an added hypothesis and is forced: the
body runs with `mergeEnv a b` in scope, so `WF.envInTerms` needs the colliding rows'
outputs to be terms, which only `RowsWF` says. -/
theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (hrw : d₁.RowsWF)
    (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d f as _ a b vs _ _ hra hrb _ _ hbody _ =>
    have hw0 : ({ d₁ with env := mergeEnv a b } : Database).WF := by
      refine ⟨hw.subtermClosed, hw.eqsInTerms, fun p hp => ?_⟩
      rcases mem_mergeEnv hp with hpa | hpb
      · exact (hrw _ hra).2 _ hpa
      · exact (hrw _ hrb).2 _ hpb
    have hd : d.WF := evalActions_wf hw0 hbody
    have hr : (d.addRow f as vs).WF := hd.addRow f as vs
    have hb : d₁.Contained d :=
      ⟨(evalActions_contained hbody).terms, (evalActions_contained hbody).rows,
        (evalActions_contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hr.subtermClosed, hr.eqsInTerms, fun p hp => hc.terms (hw.envInTerms p hp)⟩

/-! ### `Database.Solid` survives a step

`Database.Recorded.addRow_congr` — what lets the specification write the combined row at a
*different* key of the class — needs `Solid` of the side being recorded, so transporting a
whole merge closure needs `Solid` to survive one. It does, and with no side condition:
every operation an action performs inserts terms together with their subterms and their
constructor rows, which is all three fields at once. -/

namespace Database
namespace Solid

theorem addTerm {db : Database} (h : db.Solid) (t : Term) : (db.addTerm t).Solid where
  wf := h.wf.addTerm t
  rowsWF := by
    rintro r (hr | ⟨hout, hm⟩)
    · exact ⟨fun a ha => Or.inl ((h.rowsWF r hr).1 a ha),
        fun v hv => Or.inl ((h.rowsWF r hr).2 v hv)⟩
    · refine ⟨fun a ha => Or.inr ?_, ?_⟩
      · exact Term.subterms_subset_of_mem hm (Term.IsSubterm.arg ha (Term.IsSubterm.refl a))
      · intro v hv
        rw [hout] at hv
        rcases List.mem_singleton.mp hv with rfl
        exact Or.inr hm
  rowsComplete := by
    rintro r ⟨hout, hm | hm⟩
    · exact Or.inl (h.rowsComplete ⟨hout, hm⟩)
    · exact Or.inr ⟨hout, hm⟩

theorem addTerms {db : Database} (h : db.Solid) (ts : List Term) :
    (db.addTerms ts).Solid := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addEq {db : Database} (h : db.Solid) (a b : Term) : (db.addEq a b).Solid := by
  have h' := (h.addTerm a).addTerm b
  refine ⟨⟨h'.wf.subtermClosed, ?_, h'.wf.envInTerms⟩, h'.rowsWF, h'.rowsComplete⟩
  rintro p (rfl | hp)
  · exact ⟨(Database.Contained.addTerm b _).terms (Or.inr a.self_mem_subterms),
      Or.inr b.self_mem_subterms⟩
  · exact h'.wf.eqsInTerms p hp

theorem addRow {db : Database} (h : db.Solid) (f : FnName) (as vs : List Term) :
    (db.addRow f as vs).Solid := by
  have h' := (h.addTerms as).addTerms vs
  refine ⟨h.wf.addRow f as vs, ?_, h'.rowsComplete.trans (Set.subset_insert _ _)⟩
  rintro r (rfl | hr)
  · exact ⟨fun a ha => (Database.Contained.addTerms vs _).terms (mem_terms_addTerms ha),
      fun v hv => mem_terms_addTerms hv⟩
  · exact h'.rowsWF r hr

/-- Only `WF.envInTerms` reads the environment, so a new one has to be checked and nothing
else moves. -/
theorem setEnv {db : Database} (h : db.Solid) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) : ({ db with env := σ } : Database).Solid :=
  ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, hσ⟩, h.rowsWF, h.rowsComplete⟩

end Solid
end Database

theorem evalAction_solid {db d : Database} (h : db.Solid) {a : Action}
    (hv : evalAction db a = some d) : d.Solid := by
  rcases evalAction_eq_some hv with ⟨e, t, rfl, -, rfl⟩ | ⟨v, e, t, rfl, -, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, rfl, -, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, -, -, rfl⟩
  · exact h.addTerm t
  · refine ⟨⟨(h.addTerm t).wf.subtermClosed, (h.addTerm t).wf.eqsInTerms, ?_⟩,
      (h.addTerm t).rowsWF, (h.addTerm t).rowsComplete⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inr t.self_mem_subterms
    · exact Or.inl (h.wf.envInTerms b hb')
  · exact h.addEq t₁ t₂
  · exact h.addRow f as vs

theorem evalActions_solid {db d : Database} (h : db.Solid) {as : List Action}
    (hv : evalActions db as = some d) : d.Solid := by
  induction as generalizing db with
  | nil => rw [evalActions_nil, Option.some.injEq] at hv; exact hv ▸ h
  | cons a as ih =>
    cases hx : evalAction db a with
    | none => rw [evalActions_cons, hx] at hv; simp at hv
    | some db₁ =>
      rw [evalActions_cons, hx, Option.bind_some] at hv
      exact ih (evalAction_solid h hx) hv

/-- A merge step is an action block followed by an `addRow`, so `Solid` survives it. -/
theorem MergeStep.solid {d₁ d₂ : Database} (h : d₁.Solid) (hstep : MergeStep d₁ d₂) :
    d₂.Solid := by
  cases hstep with
  | @collide d f as _ a b vs _ _ hra hrb _ _ hbody _ =>
    have h0 : ({ d₁ with env := mergeEnv a b } : Database).Solid :=
      h.setEnv fun p hp => by
        rcases mem_mergeEnv hp with hpa | hpb
        · exact (h.rowsWF _ hra).2 _ hpa
        · exact (h.rowsWF _ hrb).2 _ hpb
    have hd : d.Solid := evalActions_solid h0 hbody
    have hr := hd.addRow f as vs
    have hb : d₁.Contained d :=
      ⟨(evalActions_contained hbody).terms, (evalActions_contained hbody).rows,
        (evalActions_contained hbody).eqs⟩
    have hcont := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨⟨hr.wf.subtermClosed, hr.wf.eqsInTerms,
        fun p hp => hcont.terms (h.wf.envInTerms p hp)⟩, hr.rowsWF, hr.rowsComplete⟩

theorem MergeClosure.solid {d₁ d₂ : Database} (h : d₁.Solid) (hcl : MergeClosure d₁ d₂) :
    d₂.Solid := by
  induction hcl with
  | refl => exact h
  | tail _ hstep ih => exact hstep.solid ih

/-- **A merge collision available at `A` is available at any `C` that *records* it.**

The one step beyond `MergeStep.transport`: the specification finds the two rows at
congruent keys and so writes the combined row at a key the implementation did not, which
`Database.Recorded.addRow_congr` is exactly the shape of. -/
theorem MergeStep.transport_recorded {A C B : Database} (hc : A.Recorded C)
    (hsig : A.sig = C.sig) (hs : A.Solid) (h : MergeStep A B) :
    ∃ D, MergeStep C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f as bs a b vs body res hra hrb hcong hm hbody hres =>
    obtain ⟨as', ha', hra'⟩ := hc.rows _ hra
    obtain ⟨bs', hb', hrb'⟩ := hc.rows _ hrb
    have h0 : ({ A with env := mergeEnv a b } : Database).Solid :=
      hs.setEnv fun p hp => by
        rcases mem_mergeEnv hp with hpa | hpb
        · exact (hs.rowsWF _ hra).2 _ hpa
        · exact (hs.rowsWF _ hrb).2 _ hpb
    have hc0 : ({ A with env := mergeEnv a b } : Database).Recorded
        { C with env := mergeEnv a b } := hc.setEnv _ _
    obtain ⟨dC, hstepC, hcont, hsig', henv'⟩ := evalActions_mono_recorded hc0 hsig rfl hbody
    have hsolid : dA.Solid := evalActions_solid h0 hbody
    have hcong' : CongList C as' bs' :=
      ha'.symm.trans ((CongList.mono_recorded hc hcong).trans hb')
    have hargs : ∀ x ∈ as, x ∈ dA.terms := fun x hx =>
      (evalActions_contained hbody).terms ((hs.rowsWF _ hra).1 x hx)
    have hCdC : C.Contained dC :=
      ⟨(evalActions_contained hstepC).terms, (evalActions_contained hstepC).rows,
        (evalActions_contained hstepC).eqs⟩
    have hdAsig : A.sig = dA.sig := by simpa using (evalActions_sig hbody).symm
    have hdCsig : C.sig = dC.sig := hsig ▸ hdAsig.trans hsig'
    have hMC : CongList (dC.addRow f as' vs) as as' :=
      CongList.mono (hCdC.trans (Database.Contained.addRow f as' vs dC)) ha'
    have hAR : (dA.addRow f as vs).Recorded (dC.addRow f as' vs) :=
      Database.Recorded.addRow_congr hcont hsolid f as' vs hargs hMC
    have hEnv : (dC.addRow f as' vs).Contained
        ({ dC.addRow f as' vs with env := C.env, rules := C.rules } : Database) :=
      ⟨subset_rfl, subset_rfl, subset_rfl⟩
    refine ⟨{ dC.addRow f as' vs with env := C.env, rules := C.rules },
      .collide hra' hrb' hcong' (by rw [← hsig]; exact hm) hstepC
        (hsig' ▸ henv' ▸ hres), ?_, ?_⟩
    · exact ⟨hAR.terms, fun r hr => Database.Out.mono hEnv (hAR.rows r hr), hAR.eqs⟩
    · simpa using hsig'

/-- `MergeStep.transport_recorded` iterated. -/
theorem MergeClosure.transport_recorded {A C B : Database} (hc : A.Recorded C)
    (hsig : A.sig = C.sig) (hs : A.Solid) (h : MergeClosure A B) :
    ∃ D, MergeClosure C D ∧ B.Recorded D ∧ B.sig = D.sig := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, hc, hsig⟩
  | @tail b c hcl hstep ih =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ := ih
    obtain ⟨D', hstepD', hcont', hsig'⟩ :=
      hstep.transport_recorded hcontD hsigD (MergeClosure.solid hs hcl)
    exact ⟨D', hclD.tail hstepD', hcont', hsig'⟩

/-! ### Containment for the merge interpreter

Stage 4 of the refinement chain, together with the `execActions` refinement it rests on.
It sits here rather than beside the statements it discharges because every part of it
reads something stated above: `execAction_sig`, `mergeOneWith_inv`,
`mergeOneWith_confined`, `mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv`,
`Inv.execActions` and `Inv.mergeRound_of_legalMerges`.

`hlegal` — every declared merge's body writes only legal `set`s — recurs throughout, for
`Inv.mergeRound_of_legalMerges`'s reason: without it the accumulator's `Inv` fails, and
`Inv` is what turns the interpreter's evaluation into an `Expr.eval` witness. -/

namespace FDatabase

/-- **One firing of the pass lands in a state the merge closure reaches.**

`x` is the accumulator, `D` a specification state the closure has already reached that
contains it. The firing's congruence test is against the *pre-pass* closure `d.closureF`,
which is why `d`'s invariant appears alongside `x`'s. `evalActions_mono` is what
re-runs the merge body at `D`.

The witness takes the two rows in the order `(r₂, r₁)`, which is the whole reason
`MergeStep.collide` lines up with the implementation: `collide` runs the body under
`mergeEnv a b` and writes the combined row at the *first* row's key, and
`mergeOneOriented` binds `old` from `r₂` and overwrites `r₂`. Both facts are the one fact
that `r₂` is the row already in the table — which of the two colliding rows that is,
`mergeOneWith` decides, and `mergeOneWith_mergeStep` says the decision is free.

**Why the conclusion is `MergeClosure` and not `MergeStep`.** A firing takes exactly one
`MergeStep` — *except* at a `noConflict` collision, which egglog resolves by running
nothing, and which this therefore has to model by taking **no** step: the implementation
never evaluates the body there, so the `evalActions` and `Expr.evalList` premises
`MergeStep.collide` demands are not available and in general do not hold (nothing
scope-checks a merge body, so a body with a free variable makes `evalActions` fail while
the skip still fires). Zero-or-one steps is `MergeClosure`, so that is what this states.
Nothing downstream notices: `mergeRound_contained` consumed the step with
`ReflTransGen.tail` and now consumes the closure with `.trans`, and its statement — the
containment contract the interpreter is actually held to — is unchanged. -/
theorem mergeOneOriented_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Recorded D)
    (hm : FDatabase.mergeOneOriented d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Recorded D' := by
  have hDsig : D.sig = d.sig := MergeClosure.sig hcl
  unfold FDatabase.mergeOneOriented at hm
  match hmo : x.sig.mergeOf r₁.fn with
  | none => rw [hmo] at hm; simp at hm
  | some .noMerge => rw [hmo] at hm; simp at hm
  | some (.merge body res) =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, hck⟩, hr₁⟩, hr₂⟩ := hcond
      have hσ : ∀ b ∈ mergeEnv r₂.out r₁.out, b.2 ∈ x.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact (hx.rowsWF r₂ hr₂).2 b.2 hb'
        · exact (hx.rowsWF r₁ hr₁).2 b.2 hb'
      have h₀ : ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).Inv := hx.setEnv hσ
      have hlx : Actions.SetLegal body x.sig := by
        rw [hxs]; exact hlegal r₁.fn body res (hxs ▸ hmo)
      split at hm
      case isTrue =>
        -- The no-conflict skip takes no specification step: `y` only drops a row of `x`.
        rw [Option.some.injEq] at hm
        subst hm
        exact ⟨D, Relation.ReflTransGen.refl,
          hxc.terms, fun r hr => hxc.rows r (mem_dropRow hr), hxc.eqs⟩
      case isFalse =>
      cases hb : execActions { x with env := mergeEnv r₂.out r₁.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        have hbodyStep : evalActions
            ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase body
            = some eb.toDatabase := FDatabase.execActions_evalActions hb
        obtain ⟨D₁, hD₁step, hD₁c, hD₁sig, hD₁env⟩ :=
          evalActions_mono_recorded
            (db := ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase)
            (D := { D with env := mergeEnv r₂.out r₁.out })
            (hxc.setEnv _ _) (hxs.trans hDsig.symm) rfl hbodyStep
        have hebInv : eb.Inv := h₀.execActions hlx hb
        have hml : Expr.evalList eb.toDatabase.sig res eb.toDatabase.env = some vs := hv
        have hmlD : Expr.evalList D₁.sig res D₁.env = some vs := by
          rw [← hD₁env, ← hD₁sig]
          exact hml
        -- The two rows are found at *congruent* keys, so the combined row is written at
        -- `bs₂` where the interpreter writes it at `r₂.args`; `Out` reads each from the
        -- other, which is the whole content of the weakening.
        obtain ⟨bs₂, hb₂, hr₂D⟩ := hxc.rows r₂ hr₂
        obtain ⟨bs₁, hb₁, hr₁D⟩ : D.Out r₂.fn r₁.args r₁.out := by
          rw [← hfn]; exact hxc.rows r₁ hr₁
        have hcongD : CongList D r₂.args r₁.args :=
          (CongList.mono (MergeClosure.contained hcl)
            ((FDatabase.congrTuple_iff h.wf).mp hck)).symm
        have hcongB : CongList D bs₂ bs₁ := hb₂.symm.trans (hcongD.trans hb₁)
        have hmoD : D.sig.mergeOf r₂.fn = some (MergeSpec.merge body res) := by
          rw [← hfn, hDsig, ← hxs]; exact hmo
        refine ⟨{ D₁.addRow r₂.fn bs₂ vs with env := D.env, rules := D.rules },
          Relation.ReflTransGen.single
            (MergeStep.collide hr₂D hr₁D hcongB hmoD hD₁step hmlD), ?_⟩
        have hebInvT : eb.toDatabase.Solid :=
          ⟨hebInv.wf, hebInv.rowsWF, hebInv.rowsComplete⟩
        have hargs : ∀ a ∈ r₂.args, a ∈ eb.toDatabase.terms := fun a ha =>
          (FDatabase.execActions_contained hb).terms ((hx.rowsWF r₂ hr₂).1 a ha)
        have hDD₁ : D.Contained D₁ :=
          ⟨(evalActions_contained hD₁step).terms, (evalActions_contained hD₁step).rows,
            (evalActions_contained hD₁step).eqs⟩
        have hebSig : eb.sig = D.sig := by
          rw [FDatabase.execActions_sig hb]
          show x.sig = D.sig
          rw [hxs, hDsig]
        have hDD₁sig : D.sig = D₁.sig := hebSig.symm.trans hD₁sig
        have hMC : CongList (D₁.addRow r₂.fn bs₂ vs) r₂.args bs₂ :=
          CongList.mono (hDD₁.trans (Database.Contained.addRow r₂.fn bs₂ vs D₁)) hb₂
        have hAR : (eb.toDatabase.addRow r₂.fn r₂.args vs).Recorded
            (D₁.addRow r₂.fn bs₂ vs) :=
          Database.Recorded.addRow_congr hD₁c hebInvT r₂.fn bs₂ vs hargs hMC
        have hbridge : ((eb.addTerms r₂.args).addTerms vs).toDatabase
            = (eb.toDatabase.addTerms r₂.args).addTerms vs := by
          simp only [FDatabase.toDatabase_addTerms]
        have hEnv : (D₁.addRow r₂.fn bs₂ vs).Contained
            ({ D₁.addRow r₂.fn bs₂ vs with env := D.env, rules := D.rules } : Database) :=
          ⟨subset_rfl, subset_rfl, subset_rfl⟩
        refine ⟨?_, fun r hr => ?_, ?_⟩
        · show ((eb.addTerms r₂.args).addTerms vs).toDatabase.terms ⊆ _
          rw [hbridge]; exact hAR.terms
        · rcases mem_mergeRows hr with hr' | rfl
          · refine Database.Out.mono hEnv (hAR.rows r (Or.inr ?_))
            show r ∈ ((eb.toDatabase.addTerms r₂.args).addTerms vs).rows
            rw [← hbridge]; exact hr'
          · exact ⟨bs₂, CongList.mono hEnv hMC, Set.mem_insert _ _⟩
        · show ((eb.addTerms r₂.args).addTerms vs).toDatabase.eqs ⊆ _
          rw [hbridge]; exact hAR.eqs

/-- **Either orientation stays inside the closure, so the choice between them is free.**

`mergeOneOriented_mergeStep` instantiates `MergeStep.collide` with the two rows in one
order; `collide` takes them in both, so `swapForCanon`'s answer never has to be justified
against the specification. That is what makes matching egglog's `old`/`new` an
implementation question — settled by `Impl/Merge.lean`'s `canonTerm` against the binary —
rather than a change to the semantics. -/
theorem mergeOneWith_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Recorded D)
    (hm : FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Recorded D' := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := d.closureF) (d := x) r₁ r₂
  exact mergeOneOriented_mergeStep h hlegal hx hxs hcl hxc (he ▸ hm)

/-- **The merge pass lands inside a state the merge closure reaches.**

The pass deletes the two rows it merged, so its result is not itself a `MergeClosure`
state; the witness is a specification state that took the same collisions and kept the
originals. The fold invariant is "the accumulator is `Inv`, has the pre-pass signature,
and is contained in some state the closure has reached"; each firing extends the closure
by one `MergeStep.collide`. -/
theorem mergeRound_contained {d : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig) :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Recorded db := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig ∧
    ∃ D, MergeClosure d.toDatabase D ∧ x.toDatabase.Recorded D
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    obtain ⟨hxInv, hxs, D, hcl, hxc⟩ := hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => exact ⟨hxInv, hxs, D, hcl, hxc⟩
    | some y =>
      obtain ⟨D', hstepD, hyc⟩ :=
        mergeOneWith_mergeStep h hlegal hxInv hxs hcl hxc hy
      refine ⟨mergeOneWith_inv hxInv (fun g body res hg => ?_) hy,
        ((mergeOneWith_confined hy).2.2.1).trans hxs, D', hcl.trans hstepD, hyc⟩
      exact hxs ▸ hlegal g body res (hxs ▸ hg)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  -- The rebuild is the pass's first step and the one place the witness stands still: no
  -- `MergeStep` is taken, and `rebuild_recorded` is what pays for the re-keying.
  have hreb : P (FDatabase.rebuild d.closureF d) :=
    ⟨h.rebuild, rfl, d.toDatabase, Relation.ReflTransGen.refl, rebuild_recorded h⟩
  unfold FDatabase.mergeRound
  split
  · exact ⟨d.toDatabase, Relation.ReflTransGen.refl, Database.Recorded.refl h.rowsWF⟩
  · obtain ⟨-, -, D, hcl, hc⟩ := houter _ _ _ hreb
    exact ⟨D, hcl, hc⟩

/-- `mergeSaturateF_contained`, with the fuel first so the induction can generalize the
database. -/
theorem mergeSaturateF_contained_aux {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    (∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig) →
    d.mergeSaturateF n = some e →
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Recorded db := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Recorded.refl h.rowsWF⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Recorded.refl h.rowsWF⟩
    · have hsigR : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
      have hlegal' : ∀ g body res, d.mergeRound.sig.mergeOf g = some (MergeSpec.merge body res) →
          Actions.SetLegal body d.mergeRound.sig := by
        rw [hsigR]; exact hlegal
      have hround : d.mergeRound.Inv := h.mergeRound_of_legalMerges hlegal
      obtain ⟨db₂, hcl₂, hcont₂⟩ := ih hround hlegal' hs
      obtain ⟨db₁, hcl₁, hcont₁⟩ := mergeRound_contained h hlegal
      have hsig₁ : d.mergeRound.toDatabase.sig = db₁.sig := by
        show d.mergeRound.sig = db₁.sig
        rw [hsigR]
        exact (MergeClosure.sig hcl₁).symm
      obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
        MergeClosure.transport_recorded hcont₁ hsig₁ hround.solid hcl₂
      exact ⟨db₃, hcl₁.trans hcl₃, hcont₂.trans hcont₃⟩

/-- **The merge phase run to a fixpoint stays inside the merge closure.**

`mergeRound_contained` once per round, with `MergeClosure.transport` re-basing the tail's
closure onto the head's witness. `mergeRound_confined` is what keeps `hlegal` applicable
at the next round: a pass does not touch `sig`. -/
theorem mergeSaturateF_contained {d e : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    {n : Nat} (hs : d.mergeSaturateF n = some e) :
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Recorded db :=
  mergeSaturateF_contained_aux h hlegal hs

/-- **A round's rule firings stay inside `RunRules`.**

The witness is `RunRules d.toDatabase` itself and the merge closure is the reflexive one:
`execRunRules` runs no merge phase (`Impl/Merge.lean` defers it to `execCmdM`), so
nothing has to be re-based here.

**Rule legality is not needed.** Containment only asks that every row the enumerator
writes is one the specification writes, and `execActions_evalActions` matches the two
action interpreters on every action block, legal or not. `FDatabase.Inv.execRunRules` is
where legality is spent — keeping the invariant, which is a stronger conclusion than this
one.

The enumerator's substitution is transported to the specification's by
`evalActions_envAgree`: `matchQuery_validQuerySubst` only produces one that
`Env.Agree`s, and `Database.EnvAgree.eq_of_env_rules` turns that back into equality once
`fireInto` restores the caller's environment. -/
theorem execRunRules_contained {d : FDatabase} (h : d.Inv) :
    ∃ db, RunStep d.toDatabase db ∧ (execRunRules d).toDatabase.Contained db := by
  refine ⟨RunRules d.toDatabase, Relation.ReflTransGen.refl, ?_⟩
  set R : Database := RunRules d.toDatabase
  -- Values a match assigns are terms the database already holds, so extending `d.env`
  -- by one keeps `Inv`.
  have henvInv : ∀ {q : Query} {σ : Env}, σ ∈ matchQuery d q →
      ({ d with env := d.env ++ σ } : FDatabase).Inv := by
    intro q σ hσ
    refine h.setEnv ?_
    intro b hb
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.wf.envInTerms b hb'
    · have : σ ∈ assignments d.terms (Query.freeVars q d.env) :=
        (List.mem_filter.mp (by rwa [matchQuery] at hσ)).1
      exact (mem_assignments.mp this).2 b hb'
  -- One firing lands inside `RunRules`.
  have hone : ∀ (r : Rule), r ∈ d.rules → ∀ (σ : Env), σ ∈ matchQuery d r.query →
      ∀ acc : FDatabase, acc.toDatabase.Contained R →
      (fireInto d r acc σ).toDatabase.Contained R := by
    intro r hr σ hσ acc hacc
    rw [fireInto, execLocalActions]
    cases hv : execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using hacc
    | some e =>
      have hmemS : ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase ∈
          {D | ∃ r' ∈ d.toDatabase.rules, D ∈ RuleResults d.toDatabase r'} := by
        obtain ⟨τ, hτ, hag⟩ := matchQuery_validQuerySubst h hσ
        have hstep : evalActions
            ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database) r.actions
            = some e.toDatabase := by
          have := FDatabase.execActions_evalActions hv
          simpa using this
        have hEA : ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database).EnvAgree
            { d.toDatabase with env := d.toDatabase.env ++ τ } :=
          ⟨rfl, rfl, rfl, rfl, rfl, Env.Agree.append_left _ hag.symm⟩
        exact
          let ⟨e', hstep', hag'⟩ := evalActions_envAgree_exists hEA hstep
          ⟨r, hr, τ, hτ, by
            rw [evalLocalActions, hstep', Option.map_some, FDatabase.toDatabase_restore,
              ← hag'.eq_of_env_rules d.toDatabase.env d.toDatabase.rules]
            rfl⟩
      have hsub :
          ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase.Contained R :=
        Database.Contained.mem_sUnion hmemS
      simp only [Option.map_some]
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · rcases mem_terms_union.mp hx with hx' | hx'
        · exact hacc.terms hx'
        · exact hsub.terms hx'
      · rcases mem_rows_union.mp hx with hx' | hx'
        · exact hacc.rows hx'
        · exact hsub.rows hx'
      · rcases mem_eqs_union.mp hx with hx' | hx'
        · exact hacc.eqs hx'
        · exact hsub.eqs hx'
  -- The two folds.
  have hinner : ∀ (r : Rule), r ∈ d.rules → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ matchQuery d r.query) → ∀ acc : FDatabase,
      acc.toDatabase.Contained R →
      (σs.foldl (fireInto d r) acc).toDatabase.Contained R := by
    intro r hr σs
    induction σs with
    | nil => intro _ acc hacc; exact hacc
    | cons σ σs ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _
        (hone r hr σ (hall σ List.mem_cons_self) acc hacc)
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules) → ∀ acc : FDatabase,
      acc.toDatabase.Contained R → (l.foldl (fireRule d) acc).toDatabase.Contained R := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons r l ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_
      rw [fireRule]
      exact hinner r (hall r List.mem_cons_self) _ (fun _ hσ => hσ) acc hacc
  rw [execRunRules]
  exact houter d.rules (fun _ hr => hr) d (Database.Contained.sUnion _ _)

/-- **`execCmdM_contained`'s `.action` case**, with `CmdStep.action`'s two premises spelled
out rather than packaged.

It needs no transport at all: `execAction_evalAction` lands on the specification's
`evalAction` result exactly, and `mergeSaturateF_contained` continues from there. That
pairing *is* `CmdStep.action` — the specification's merge phase is what pays for the
interpreter's, and without it this statement is false. -/
theorem execCmdM_action_contained {d e : FDatabase} (h : d.Inv) {a : Action}
    (halegal : a.SetLegal d.sig)
    (hlegal : ∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig)
    (hs : d.execCmdM (.action a) = some e) :
    ∃ d₁ db, evalAction d.toDatabase a = some d₁ ∧ MergeClosure d₁ db ∧
      e.toDatabase.Recorded db := by
  rw [FDatabase.execCmdM] at hs
  obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
  have hsig₁ : d₁.sig = d.sig := execAction_sig hd₁
  have hlegal₁ : ∀ g body res, d₁.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d₁.sig := by rw [hsig₁]; exact hlegal
  obtain ⟨db, hcl, hcont⟩ :=
    mergeSaturateF_contained (h.execAction halegal hd₁) hlegal₁ hsat
  exact ⟨d₁.toDatabase, db, FDatabase.execAction_evalAction hd₁, hcl, hcont⟩

end FDatabase

/-! ### Containment for a whole program

`execRunRules_contained` and `mergeSaturateF_contained` cover the two phases of a round.
What is left is the bookkeeping that turns them into a statement about `execCmdM`,
`execProgramM` and `execM`, and it is bookkeeping of exactly two kinds.

**Transport.** The specification witness for a command is a state *containing* the
interpreter's, so the next command's witness has to be re-based onto it. `CmdStep.mono`
and `ProgramStep.mono` are that, and they are `ValidQuerySubst.mono` (a larger state
admits every match), `evalActions_mono` (a block re-run on a larger state lands
on a larger result) and `MergeClosure.transport` composed. They carry `sig`, `env` and
`rules` equalities alongside the containment because all three are read: `mono` needs the
signature, a rule fires in `d.env ++ σ`, and `RunRules` ranges over `rules`.

**Preservation.** The induction carries `FDatabase.Inv`, so every command has to
re-establish it. `.action` and `.run` are the lemmas above run to a fixpoint; `.rule`
touches no field `Inv` reads; `.decl` is the one that needs a hypothesis of its own, and
`Falsity.claim1` is why. -/

/-- A merge writes its combined row and then restores the caller's environment and rule
list, so neither field ever moves. `MergeStep.sig` is the third of these; it is in
`Proofs/Step.lean`, next to `MergeClosure.sig`. -/
theorem MergeStep.envRules {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  cases h with
  | collide _ _ _ _ _ _ => exact ⟨rfl, rfl⟩

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-- **A firing available at `A` is available at any `C` containing it.**
`ValidQuerySubst.mono` finds the same match and `evalActions_mono` re-runs the
head on the larger state. The result is an existential, not the join: that is all
containment needs, and it is all `evalActions_mono` gives. -/
theorem RuleResults.mono {A C : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) {r : Rule} {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Contained D := by
  obtain ⟨σ, hq, hstep⟩ := hd
  obtain ⟨d', hv, rfl⟩ := evalLocalActions_eq_some hstep
  have hc0 : ({ A with env := A.env ++ σ } : Database).Contained
      { C with env := C.env ++ σ } := ⟨hc.terms, hc.rows, hc.eqs⟩
  obtain ⟨D', hD', hcont, -, -⟩ := evalActions_mono hc0 hsig (by simp [henv]) hv
  exact ⟨{ D' with env := C.env, rules := C.rules },
    ⟨σ, ValidQuerySubst.mono hc hsig henv.symm hq,
      by rw [evalLocalActions, hD', Option.map_some]⟩,
    ⟨hcont.terms, hcont.rows, hcont.eqs⟩⟩

/-- **A round's rule phase is monotone.** Every database one rule contributes at `A` is
contained in one the same rule contributes at `C`, so the two unions are ordered. -/
theorem RunRules.mono {A C : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) :
    (RunRules A).Contained (RunRules C) := by
  have key : ∀ d ∈ {d | ∃ r ∈ A.rules, d ∈ RuleResults A r}, d.Contained (RunRules C) := by
    rintro d ⟨r, hr, hdr⟩
    obtain ⟨D, hD, hcd⟩ := RuleResults.mono hc hsig henv hdr
    exact hcd.trans (Database.Contained.mem_sUnion ⟨r, hrules ▸ hr, hD⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).terms (hc.terms hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).terms hx'
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).rows (hc.rows hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).rows hx'
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).eqs (hc.eqs hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).eqs hx'

/-- **A command available at `A` is available at any `C` containing it, and its result
still contains the smaller run's.** The four cases are `evalAction_mono`,
nothing, `RunRules.mono`, and nothing; `MergeClosure.transport` re-bases the merge phase
in the two that have one. -/
theorem CmdStep.mono {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) {c : Cmd} (h : CmdStep A c B) :
    ∃ D, CmdStep C c D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  cases h with
  | action ha hm =>
    obtain ⟨D₀, hD₀, hcont₀, hsig₀, henv₀⟩ := evalAction_mono hc hsig henv ha
    obtain ⟨D, hclD, hcontD, hsigD⟩ := MergeClosure.transport hcont₀ hsig₀ hm
    refine ⟨D, .action hD₀ hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hm).1, (MergeClosure.envRules hclD).1, henv₀]
    · rw [(MergeClosure.envRules hm).2, (MergeClosure.envRules hclD).2,
        evalAction_rules ha, evalAction_rules hD₀, hrules]
  | rule =>
    refine ⟨_, .rule, ⟨hc.terms, hc.rows, hc.eqs⟩, hsig, henv, ?_⟩
    show insert _ A.rules = insert _ C.rules
    rw [hrules]
  | run hrun =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ :=
      MergeClosure.transport (RunRules.mono hc hsig henv hrules) hsig hrun
    refine ⟨D, .run hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hrun).1, (MergeClosure.envRules hclD).1]; exact henv
    · rw [(MergeClosure.envRules hrun).2, (MergeClosure.envRules hclD).2]; exact hrules
  | decl =>
    refine ⟨_, .decl, ⟨hc.terms, hc.rows, hc.eqs⟩, ?_, henv, hrules⟩
    show Function.update A.sig _ _ = Function.update C.sig _ _
    rw [hsig]

/-- `CmdStep.mono` iterated. This is what makes the containment contract compose: the
specification witness for the tail of a program starts from the witness the head
produced, which contains — but need not equal — the interpreter's state. -/
theorem ProgramStep.mono {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) {p : Program}
    (h : ProgramStep A p B) :
    ∃ D, ProgramStep C p D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  induction h generalizing C with
  | nil => exact ⟨C, .nil, hc, hsig, henv, hrules⟩
  | cons hcmd _ ih =>
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀, hr₀⟩ := hcmd.mono hc hsig henv hrules
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁, hr₁⟩ := ih hc₀ hs₀ he₀ hr₀
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁, hr₁⟩

/-! #### The same, along `Recorded`

The re-keying contract needs every one of the four transport lemmas again. Two things are
new and both come from the same place — the specification finds a row at a *congruent* key
rather than at the same one. `ValidSubst.mono_recorded` composes that congruence into the
row atom's, and `MergeStep.transport_recorded` writes the combined row at the key it found,
which is what `Database.Solid` has to be carried for. `CmdStep.solid` is that carrying. -/

/-- `Solid` survives a rule firing: the head is an action block, run in the caller's
environment extended by a substitution whose values the database already holds. -/
theorem RuleResults.solid {db d : Database} (h : db.Solid) {r : Rule}
    (hd : d ∈ RuleResults db r) : d.Solid := by
  obtain ⟨σ, hq, hstep⟩ := hd
  obtain ⟨d', hv, rfl⟩ := evalLocalActions_eq_some hstep
  have h0 : ({ db with env := db.env ++ σ } : Database).Solid := by
    refine h.setEnv fun b hb => ?_
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.wf.envInTerms b hb'
    · exact hq.mem_terms b hb'
  have hd' : d'.Solid := evalActions_solid h0 hv
  exact ⟨⟨hd'.wf.subtermClosed, hd'.wf.eqsInTerms,
      fun b hb => (evalActions_contained hv).terms (h.wf.envInTerms b hb)⟩,
    hd'.rowsWF, hd'.rowsComplete⟩

/-- `Solid` survives the union a round takes: each field is a union of the same field over
databases that all have it. -/
theorem RunRules.solid {db : Database} (h : db.Solid) : (RunRules db).Solid := by
  set S : Set Database := {d | ∃ r ∈ db.rules, d ∈ RuleResults db r} with hS
  have key : ∀ d ∈ S, d.Solid := by
    rintro d ⟨r, -, hdr⟩
    exact RuleResults.solid h hdr
  have hsubT : ∀ d ∈ S, d.terms ⊆ (db.sUnion S).terms :=
    fun d hd => (Database.Contained.mem_sUnion hd).terms
  have hsubR : ∀ d ∈ S, d.rows ⊆ (db.sUnion S).rows :=
    fun d hd => (Database.Contained.mem_sUnion hd).rows
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro t (ht | ht)
    · exact (h.wf.subtermClosed t ht).trans Set.subset_union_left
    · obtain ⟨d, hd, ht'⟩ := Set.mem_iUnion₂.mp ht
      exact ((key d hd).wf.subtermClosed t ht').trans (hsubT d hd)
  · rintro p (hp | hp)
    · exact ⟨Or.inl (h.wf.eqsInTerms p hp).1, Or.inl (h.wf.eqsInTerms p hp).2⟩
    · obtain ⟨d, hd, hp'⟩ := Set.mem_iUnion₂.mp hp
      exact ⟨hsubT d hd ((key d hd).wf.eqsInTerms p hp').1,
        hsubT d hd ((key d hd).wf.eqsInTerms p hp').2⟩
  · exact fun b hb => Or.inl (h.wf.envInTerms b hb)
  · rintro r (hr | hr)
    · exact ⟨fun a ha => Or.inl ((h.rowsWF r hr).1 a ha),
        fun v hv => Or.inl ((h.rowsWF r hr).2 v hv)⟩
    · obtain ⟨d, hd, hr'⟩ := Set.mem_iUnion₂.mp hr
      exact ⟨fun a ha => hsubT d hd (((key d hd).rowsWF r hr').1 a ha),
        fun v hv => hsubT d hd (((key d hd).rowsWF r hr').2 v hv)⟩
  · rintro r ⟨hout, hm | hm⟩
    · exact Or.inl (h.rowsComplete ⟨hout, hm⟩)
    · obtain ⟨d, hd, hm'⟩ := Set.mem_iUnion₂.mp hm
      exact hsubR d hd ((key d hd).rowsComplete ⟨hout, hm'⟩)

/-- `Solid` survives a command: an action, a round and a merge phase all preserve it, and
`.rule`/`.decl` touch no field it reads. -/
theorem CmdStep.solid {A B : Database} (h : A.Solid) {c : Cmd} (hs : CmdStep A c B) :
    B.Solid := by
  cases hs with
  | action ha hm => exact MergeClosure.solid (evalAction_solid h ha) hm
  | rule =>
    exact ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.rowsWF, h.rowsComplete⟩
  | run hrun => exact MergeClosure.solid (RunRules.solid h) hrun
  | decl =>
    exact ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.rowsWF, h.rowsComplete⟩

/-- `RuleResults.mono` along `Recorded`. The signature equality comes out with it because
`RunRules.mono_recorded` needs it to re-base each firing onto the union. -/
theorem RuleResults.mono_recorded {A C : Database} (hc : A.Recorded C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) {r : Rule} {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Recorded D ∧ D.sig = C.sig := by
  obtain ⟨σ, hq, hstep⟩ := hd
  obtain ⟨d', hv, rfl⟩ := evalLocalActions_eq_some hstep
  have hc0 : ({ A with env := A.env ++ σ } : Database).Recorded
      { C with env := C.env ++ σ } := hc.setEnv _ _
  obtain ⟨D', hD', hcont, -, -⟩ := evalActions_mono_recorded hc0 hsig (by simp [henv]) hv
  refine ⟨{ D' with env := C.env, rules := C.rules },
    ⟨σ, ValidQuerySubst.mono_recorded hc hsig henv.symm hq,
      by rw [evalLocalActions, hD', Option.map_some]⟩,
    hcont.setEnvRules _ _ _ _, ?_⟩
  show D'.sig = C.sig
  simpa using evalActions_sig hD'

/-- `RunRules.mono` along `Recorded`. -/
theorem RunRules.mono_recorded {A C : Database} (hc : A.Recorded C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) :
    (RunRules A).Recorded (RunRules C) := by
  have key : ∀ d ∈ {d | ∃ r ∈ A.rules, d ∈ RuleResults A r}, d.Recorded (RunRules C) := by
    rintro d ⟨r, hr, hdr⟩
    obtain ⟨D, hD, hcd, hDsig⟩ := RuleResults.mono_recorded hc hsig henv hdr
    exact hcd.trans_contained (Database.Contained.mem_sUnion ⟨r, hrules ▸ hr, hD⟩)
  have hbase : A.Recorded (RunRules C) :=
    hc.trans_contained (Database.Contained.sUnion C _)
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact hbase.terms hx
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).terms hx'
  · rintro r (hr | hr)
    · exact hbase.rows r hr
    · obtain ⟨d, hd, hr'⟩ := Set.mem_iUnion₂.mp hr
      exact (key d hd).rows r hr'
  · rintro x (hx | hx)
    · exact hbase.eqs hx
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).eqs hx'

/-- `CmdStep.mono` along `Recorded`.

The `.decl` case asks nothing of the declaration: `Cong` reads neither `sig` nor `rows`,
so `Cong.mono_update` transports every derivation whatever the name already was. -/
theorem CmdStep.mono_recorded {A C B : Database} (hc : A.Recorded C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) (hsolid : A.Solid) {c : Cmd}
    (h : CmdStep A c B) :
    ∃ D, CmdStep C c D ∧ B.Recorded D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  cases h with
  | action ha hm =>
    obtain ⟨D₀, hD₀, hcont₀, hsig₀, henv₀⟩ := evalAction_mono_recorded hc hsig henv ha
    obtain ⟨D, hclD, hcontD, hsigD⟩ :=
      MergeClosure.transport_recorded hcont₀ hsig₀ (evalAction_solid hsolid ha) hm
    refine ⟨D, .action hD₀ hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hm).1, (MergeClosure.envRules hclD).1, henv₀]
    · rw [(MergeClosure.envRules hm).2, (MergeClosure.envRules hclD).2,
        evalAction_rules ha, evalAction_rules hD₀, hrules]
  | rule =>
    refine ⟨_, .rule, hc.setEnvRules _ _ _ _, hsig, henv, ?_⟩
    show insert _ A.rules = insert _ C.rules
    rw [hrules]
  | run hrun =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ :=
      MergeClosure.transport_recorded (RunRules.mono_recorded hc hsig henv hrules) hsig
        (RunRules.solid hsolid) hrun
    refine ⟨D, .run hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hrun).1, (MergeClosure.envRules hclD).1]; exact henv
    · rw [(MergeClosure.envRules hrun).2, (MergeClosure.envRules hclD).2]; exact hrules
  | @decl f dc =>
    refine ⟨_, .decl, ⟨hc.terms, fun r hr => ?_, hc.eqs⟩, ?_, henv, hrules⟩
    · obtain ⟨cs, hl, hrow⟩ := hc.rows r hr
      exact ⟨cs, CongList.mono_update hl, hrow⟩
    · show Function.update A.sig _ _ = Function.update C.sig _ _
      rw [hsig]

/-- `ProgramStep.mono` along `Recorded`. `CmdStep.solid` is what carries the extra
hypothesis across the induction. -/
theorem ProgramStep.mono_recorded {A C B : Database} (hc : A.Recorded C)
    (hsig : A.sig = C.sig) (henv : A.env = C.env) (hrules : A.rules = C.rules)
    (hsolid : A.Solid) {p : Program} (h : ProgramStep A p B) :
    ∃ D, ProgramStep C p D ∧ B.Recorded D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  induction h generalizing C with
  | nil => exact ⟨C, .nil, hc, hsig, henv, hrules⟩
  | @cons A d B c cs hcmd _ ih =>
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀, hr₀⟩ :=
      hcmd.mono_recorded hc hsig henv hrules hsolid
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁, hr₁⟩ :=
      ih hc₀ hs₀ he₀ hr₀ (hcmd.solid hsolid)
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁, hr₁⟩

/-! #### Declaring a fresh name

The facts a `.decl` needs, all of them about a name the signature does not yet mention. -/

/-- `Signature.mergeOf` is read pointwise, so a declaration at `f` is invisible at every
other name. -/
theorem Signature.mergeOf_update_of_ne {sig : Signature} {f g : FnName} {dc : FnDecl}
    (h : g ≠ f) :
    Signature.mergeOf (Function.update sig f (some dc)) g = Signature.mergeOf sig g := by
  unfold Signature.mergeOf
  rw [Function.update_of_ne h]

/-- An undeclared name has no merge specification either — which is *not* the same as
being a constructor, and is the half of the old reading that survives. -/
theorem Signature.mergeOf_of_none {sig : Signature} {f : FnName}
    (h : sig f = none) : Signature.mergeOf sig f = none := by
  rw [Signature.mergeOf, h]; rfl

/-- Declaring a name the signature does not yet mention can only make a `set` *more*
legal: `Action.SetLegal` asks for a merge specification and an undeclared name has none,
so no legal `set` names `f`. -/
theorem Action.SetLegal.update {a : Action} {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : a.SetLegal sig) :
    a.SetLegal (Function.update sig f (some dc)) := by
  cases a with
  | expr _ => trivial
  | letBind _ _ => trivial
  | union _ _ => trivial
  | set g _ _ =>
    have hg : g ≠ f := by
      rintro rfl
      exact h (Signature.mergeOf_of_none hf)
    show Signature.mergeOf (Function.update sig f (some dc)) g ≠ none
    rw [Signature.mergeOf_update_of_ne hg]
    exact h

theorem Actions.SetLegal.update {as : List Action} {sig : Signature} {f : FnName}
    {dc : FnDecl} (hf : sig f = none) (h : Actions.SetLegal as sig) :
    Actions.SetLegal as (Function.update sig f (some dc)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨Action.SetLegal.update hf h.1, ih h.2⟩

namespace FDatabase

/-! #### The interpreter's phases, field by field

`mergeRound_confined` records what a merge pass does to `terms`, `rows`, `eqs` and `sig`.
The transport lemmas above additionally read `env` and `rules`, and the same is needed of
`execRunRules`, so both folds are factored into an induction principle and instantiated
twice — once for the fields, once for `Inv`. -/

/-- Anything true of `d`, preserved by the rebuild and by one `mergeOneWith` firing, is
true after a whole pass. The rebuild and the two folds of `mergeRound`, factored out. -/
theorem mergeRound_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
    (hreb : P (FDatabase.rebuild d.closureF d))
    (hstep : ∀ x y : FDatabase, ∀ r₁ r₂ : Row, P x →
      FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y → P y) :
    P d.mergeRound := by
  have hstep' : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y => simpa [hy] using hstep x y r₁ r₂ hx hy
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep' x r₁ r₂ hx
  have houter : ∀ (m l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          m.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro m l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold m r₁ x hx)
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter _ _ _ hreb

/-- A firing restores the caller's environment and rule list. -/
theorem mergeOneOriented_envRules {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (h : d.mergeOneOriented cl r₁ r₂ = some e) :
    e.env = d.env ∧ e.rules = d.rules := by
  unfold FDatabase.mergeOneOriented at h
  match hmo : d.sig.mergeOf r₁.fn with
  | none => rw [hmo] at h; simp at h
  | some .noMerge => rw [hmo] at h; simp at h
  | some (.merge body res) =>
    rw [hmo] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue =>
      split at h
      case isTrue => rw [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      case isFalse =>
        cases hb : execActions { d with env := mergeEnv r₂.out r₁.out } body with
        | none => rw [hb] at h; simp at h
        | some eb =>
          rw [hb, Option.bind_some, Option.map_eq_some_iff] at h
          obtain ⟨vs, hv, rfl⟩ := h
          exact ⟨rfl, rfl⟩

/-- `mergeOneOriented_envRules` at whichever orientation the firing took. -/
theorem mergeOneWith_envRules {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) : e.env = d.env ∧ e.rules = d.rules := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂
  exact mergeOneOriented_envRules (he ▸ h)

/-- A merge pass touches neither the environment nor the rule list. -/
theorem mergeRound_envRules {d : FDatabase} :
    d.mergeRound.env = d.env ∧ d.mergeRound.rules = d.rules :=
  mergeRound_induction (P := fun x => x.env = d.env ∧ x.rules = d.rules) ⟨rfl, rfl⟩
    ⟨rebuild_envRules.1, rebuild_envRules.2⟩
    fun _ _ _ _ hx hy =>
      ⟨(mergeOneWith_envRules hy).1.trans hx.1, (mergeOneWith_envRules hy).2.trans hx.2⟩

/-- The merge phase leaves `sig`, `env` and `rules` alone. -/
theorem mergeSaturateF_fields {n : Nat} : ∀ {d e : FDatabase},
    d.mergeSaturateF n = some e → e.sig = d.sig ∧ e.env = d.env ∧ e.rules = d.rules := by
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hs
      exact ⟨h₁.trans mergeRound_confined.2.2.1, h₂.trans mergeRound_envRules.1,
        h₃.trans mergeRound_envRules.2⟩

/-- `Inv.mergeRound_of_legalMerges` run to a fixpoint. `mergeRound_confined` is what keeps
`hlegal` — a statement about the pre-phase signature — applicable at the next round. -/
theorem Inv.mergeSaturateF {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    (∀ g body res, d.sig.mergeOf g = some (MergeSpec.merge body res) →
      Actions.SetLegal body d.sig) →
    d.mergeSaturateF n = some e → e.Inv := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · refine ih (h.mergeRound_of_legalMerges hlegal) ?_ hs
      rw [mergeRound_confined.2.2.1]; exact hlegal

/-- Unioning two states preserves the refinement-chain invariant, provided they agree on
the signature: every field of `Inv` is a positive condition on `terms`, `rows` and `eqs`
relative to `sig`, and a union takes `sig`, `env` and `rules` from the left. -/
theorem Inv.union {d e : FDatabase} (hd : d.Inv) (he : e.Inv) (hsig : e.sig = d.sig) :
    (d.union e).Inv where
  wf := by
    refine ⟨fun t ht s hs => ?_, fun p hp => ?_, fun b hb => ?_⟩
    · rcases mem_terms_union.mp ht with ht' | ht'
      · exact mem_terms_union.mpr (Or.inl (hd.wf.subtermClosed t ht' hs))
      · exact mem_terms_union.mpr (Or.inr (he.wf.subtermClosed t ht' hs))
    · rcases mem_eqs_union.mp hp with hp' | hp'
      · exact ⟨mem_terms_union.mpr (Or.inl (hd.wf.eqsInTerms p hp').1),
          mem_terms_union.mpr (Or.inl (hd.wf.eqsInTerms p hp').2)⟩
      · exact ⟨mem_terms_union.mpr (Or.inr (he.wf.eqsInTerms p hp').1),
          mem_terms_union.mpr (Or.inr (he.wf.eqsInTerms p hp').2)⟩
    · exact mem_terms_union.mpr (Or.inl (hd.wf.envInTerms b hb))
  ctorTerms := by
    intro f as ht
    rcases mem_terms_union.mp ht with ht' | ht'
    · exact hd.ctorTerms f as ht'
    · show d.sig.IsCtor f
      rw [← hsig]
      exact he.ctorTerms f as ht'
  rowsComplete := by
    rintro r ⟨hout, hm⟩
    rcases mem_terms_union.mp hm with hm' | hm'
    · exact mem_rows_union.mpr (Or.inl (hd.rowsComplete ⟨hout, hm'⟩))
    · exact mem_rows_union.mpr (Or.inr (he.rowsComplete ⟨hout, hm'⟩))
  rowsWF := by
    intro r hr
    rcases mem_rows_union.mp hr with hr' | hr'
    · exact ⟨fun a ha => mem_terms_union.mpr (Or.inl ((hd.rowsWF r hr').1 a ha)),
        fun v hv => mem_terms_union.mpr (Or.inl ((hd.rowsWF r hr').2 v hv))⟩
    · exact ⟨fun a ha => mem_terms_union.mpr (Or.inr ((he.rowsWF r hr').1 a ha)),
        fun v hv => mem_terms_union.mpr (Or.inr ((he.rowsWF r hr').2 v hv))⟩
  ctorRows := by
    intro r hr hu
    rcases mem_rows_union.mp hr with hr' | hr'
    · exact ⟨(hd.ctorRows r hr' hu).1,
        mem_terms_union.mpr (Or.inl (hd.ctorRows r hr' hu).2)⟩
    · have hu' : e.sig.mergeOf r.fn = none := by rw [hsig]; exact hu
      exact ⟨(he.ctorRows r hr' hu').1,
        mem_terms_union.mpr (Or.inr (he.ctorRows r hr' hu').2)⟩

/-- Anything true of `d` and preserved by one rule firing is true of a whole round's rule
phase. The three folds of `execRunRules`, factored out. -/
theorem execRunRules_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
    (hstep : ∀ (acc e : FDatabase) (r : Rule) (σ : Env), P acc → r ∈ d.rules →
      σ ∈ matchQuery d r.query →
      execActions { d with env := d.env ++ σ } r.actions = some e →
      P (acc.union { e with env := d.env, rules := d.rules })) :
    P (execRunRules d) := by
  have hone : ∀ (r : Rule), r ∈ d.rules → ∀ (σ : Env), σ ∈ matchQuery d r.query →
      ∀ acc : FDatabase, P acc → P (fireInto d r acc σ) := by
    intro r hr σ hσ acc hacc
    rw [fireInto, execLocalActions]
    cases hv : execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using hacc
    | some e => simpa using hstep acc e r σ hacc hr hσ hv
  have hinner : ∀ (r : Rule), r ∈ d.rules → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ matchQuery d r.query) → ∀ acc : FDatabase, P acc →
      P (σs.foldl (fireInto d r) acc) := by
    intro r hr σs
    induction σs with
    | nil => intro _ acc hacc; exact hacc
    | cons σ σs ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _
        (hone r hr σ (hall σ List.mem_cons_self) acc hacc)
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules) → ∀ acc : FDatabase, P acc →
      P (l.foldl (fireRule d) acc) := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons r l ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_
      rw [fireRule]
      exact hinner r (hall r List.mem_cons_self) _ (fun _ hσ => hσ) acc hacc
  rw [execRunRules]
  exact houter d.rules (fun _ hr => hr) d hinit

/-- A round's rule phase leaves `sig`, `env` and `rules` alone: every firing is unioned
into the accumulator, and a union takes those three fields from the left. -/
theorem execRunRules_fields {d : FDatabase} :
    (execRunRules d).sig = d.sig ∧ (execRunRules d).env = d.env ∧
      (execRunRules d).rules = d.rules :=
  execRunRules_induction (P := fun x => x.sig = d.sig ∧ x.env = d.env ∧ x.rules = d.rules)
    ⟨rfl, rfl, rfl⟩ fun _ _ _ _ hacc _ _ _ => hacc

/-- Every value a match assigns is a term the database already holds, so extending `d.env`
by one keeps `Inv`. -/
theorem Inv.setEnvMatch {d : FDatabase} (h : d.Inv) {q : Query} {σ : Env}
    (hσ : σ ∈ matchQuery d q) : ({ d with env := d.env ++ σ } : FDatabase).Inv := by
  refine h.setEnv ?_
  intro b hb
  rcases List.mem_append.mp hb with hb' | hb'
  · exact h.wf.envInTerms b hb'
  · have : σ ∈ assignments d.terms (Query.freeVars q d.env) :=
      (List.mem_filter.mp (by rwa [matchQuery] at hσ)).1
    exact (mem_assignments.mp this).2 b hb'

/-- **A round's rule phase preserves `Inv`.** Each firing runs a rule head, which is an
action block like any other, so `hrules` is `Inv.execActions`'s premise per rule; the
result is unioned in, which `Inv.union` covers. -/
theorem Inv.execRunRules {d : FDatabase} (h : d.Inv)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) : (execRunRules d).Inv := by
  have := execRunRules_induction (d := d) (P := fun x => x.Inv ∧ x.sig = d.sig) ⟨h, rfl⟩
    (fun acc e r σ hacc hr hσ hv => ?_)
  · exact this.1
  refine ⟨hacc.1.union ?_ ?_, hacc.2⟩
  · refine Inv.setEnvRules ((h.setEnvMatch hσ).execActions (hrules r hr) hv) ?_
    exact fun b hb => (execActions_contained hv).terms (h.wf.envInTerms b hb)
  · show e.sig = acc.sig
    rw [execActions_sig hv, hacc.2]

@[simp] theorem addTerms_rules {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).rules = d.rules := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_rules {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).rules = d.rules := by
  show ((d.addTerms as).addTerms vs).rules = d.rules
  rw [addTerms_rules, addTerms_rules]

/-- No action touches the rule list; only `Cmd.rule` does. -/
theorem execAction_rules {d e : FDatabase} {a : Action} (h : execAction d a = some e) :
    e.rules = d.rules := by
  cases a with
  | expr e₀ =>
    rw [execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | letBind v e₀ =>
    rw [execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | union e₁ e₂ =>
    rw [execAction] at h
    obtain ⟨t₁, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    rfl
  | set f args out =>
    rw [execAction] at h
    obtain ⟨ts, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact addRow_rules

theorem execActions_rules {d e : FDatabase} {as : List Action}
    (h : execActions d as = some e) : e.rules = d.rules := by
  induction as generalizing d with
  | nil => rw [execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_rules hv)

/-- **`Inv` survives a declaration of a name the state does not yet mention.**

`Falsity.claim1` shows there is no unconditional preservation lemma: `CtorTerms` reads
`sig`, so declaring `g` `:merge` after `g ()` is already a term breaks it. The two
hypotheses are what rule that out — `hterms` keeps `ctorTerms`, and `hf` keeps
`ctorRows`, since an undeclared name has no merge specification and `ctorRows` speaks
about exactly the names that have none. -/
theorem Inv.decl {d : FDatabase} (h : d.Inv) {f : FnName} {dc : FnDecl}
    (hf : d.sig f = none) (hterms : ∀ as, Term.app f as ∉ d.terms) :
    ({ d with sig := Function.update d.sig f (some dc) } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := by
    intro g as hm
    have hg : g ≠ f := by rintro rfl; exact hterms as hm
    obtain ⟨e, he, hme⟩ := h.ctorTerms g as hm
    refine ⟨e, ?_, hme⟩
    show Function.update d.sig f (some dc) g = some e
    rw [Function.update_of_ne hg]
    exact he
  rowsComplete := h.rowsComplete
  rowsWF := h.rowsWF
  ctorRows := by
    intro r hr hu
    refine h.ctorRows r hr ?_
    show Signature.mergeOf d.sig r.fn = none
    by_cases hfn : r.fn = f
    · rw [hfn]
      exact Signature.mergeOf_of_none hf
    · rw [← Signature.mergeOf_update_of_ne (sig := d.sig) (dc := dc) hfn]
      exact hu

end FDatabase

/-! #### The side conditions

Two of them, and neither is avoidable. `Signature.MergesLegal` is what
`Falsity.mergeRound_inv_false` forces; `FDatabase.Unused` is what `Falsity.claim1`
forces. `FDatabase.ProgramLegal` checks both at the state each command runs in, which is
the weakest place to check them: a declaration only has to be fresh *when it happens*. -/

/-- Every declared `:merge` body obeys the `set` discipline every other action block
obeys. `Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about
merge bodies and this has to be carried separately. -/
def Signature.MergesLegal (sig : Signature) : Prop :=
  ∀ g body res, Signature.mergeOf sig g = some (MergeSpec.merge body res) →
    Actions.SetLegal body sig

/-- `f` is a name `d` does not mention: not declared, and not the head of any application
`d` holds. This is "declare before use", which egglog enforces in its front end. -/
def FDatabase.Unused (d : FDatabase) (f : FnName) : Prop :=
  d.sig f = none ∧ ∀ as, Term.app f as ∉ d.terms

/-- The one thing a command may not do to the state it runs in: declare a name that state
already uses. Only `.decl` is constrained. -/
def Cmd.DeclUnused : Cmd → FDatabase → Prop
  | .decl f _, d => d.Unused f
  | _, _ => True

/-- The side conditions a run has to satisfy, checked at the state each command actually
reaches: its head is a legal `set`, it declares nothing already in use, and the signature
it leaves behind has legal merge bodies. -/
def FDatabase.ProgramLegal (d : FDatabase) : Program → Prop
  | [] => True
  | c :: cs => c.SetLegal d.sig ∧ c.DeclUnused d ∧
      Signature.MergesLegal (c.sigBind d.sig) ∧
      ∀ d', d.execCmdM c = some d' → FDatabase.ProgramLegal d' cs

namespace FDatabase

/-- The signature after a command is the one `Cmd.sigBind` predicts: only `.decl` moves
it, and neither an action nor a merge phase does. -/
theorem execCmdM_sig {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    d'.sig = c.sigBind d.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, execAction_sig h₁]
    rfl
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl
  | run =>
    rw [FDatabase.execCmdM] at hs
    rw [(mergeSaturateF_fields hs).1, execRunRules_fields.1]
    rfl
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl

/-- **A legal run declares each name once, and freshly.**

`FDatabase.ProgramLegal` checks `Cmd.DeclUnused` at the state each command reaches, which
is a fact about the interpreter's database; `Program.DeclsFresh` is the same fact read off
the signature alone, which is the form `ProgramStep.mono_recorded` can carry across a
specification run. The two agree because `execCmdM` moves the signature exactly as
`Cmd.sigBind` predicts. -/
theorem ProgramLegal.declsFresh {p : Program} : ∀ {d d' : FDatabase},
    d.ProgramLegal p → d.execProgramM p = some d' → Program.DeclsFresh p d.sig := by
  induction p with
  | nil => intro _ _ _ _; trivial
  | cons c cs ih =>
    intro d d' hp hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, hd₁, hcs⟩ := Option.bind_eq_some_iff.mp hs
    refine ⟨?_, ?_⟩
    · cases c with
      | decl f dc => exact hp.2.1.1
      | action a => trivial
      | rule r =>
        -- `DeclsFresh` asks nothing of a rule, but the walk still visits its head.
        refine ⟨fun _ _ => trivial, ?_⟩
        induction r.actions with
        | nil => trivial
        | cons a as ih => exact ⟨trivial, ih⟩
      | run => trivial
    · show Program.DeclsFresh cs (c.sigBind d.sig)
      rw [← execCmdM_sig hd₁]
      exact ih (hp.2.2.2 d₁ hd₁) hcs

/-- **`Inv` through one command.** `.action` and `.run` are the phase lemmas composed with
`Inv.mergeSaturateF`; `.rule` touches no field `Inv` reads; `.decl` is `Inv.decl`, and is
the only case with a side condition of its own. -/
theorem Inv.execCmdM {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') : d'.Inv := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine Inv.mergeSaturateF (h.execAction hlegal h₁) ?_ h₂
    rw [execAction_sig h₁]; exact hmerges
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.ctorTerms,
      h.rowsComplete, h.rowsWF, h.ctorRows⟩
  | run =>
    rw [FDatabase.execCmdM] at hs
    refine Inv.mergeSaturateF (h.execRunRules hrules) ?_ hs
    rw [execRunRules_fields.1]; exact hmerges
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.decl hunused.1 hunused.2

/-- Rule-head legality is preserved: `.rule` installs a head `Cmd.SetLegal` has already
checked, and `.decl` only ever declares a name no head can legally have `set`
(`Actions.SetLegal.update`). -/
theorem execCmdM_rulesLegal {d d' : FDatabase} {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∀ r ∈ d'.rules, Actions.SetLegal r.actions d'.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, (mergeSaturateF_fields h₂).2.2,
      execAction_sig h₁, execAction_rules h₁]
    exact hrules
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact hlegal.2
    · exact hrules r' hr''
  | run =>
    rw [FDatabase.execCmdM] at hs
    rw [(mergeSaturateF_fields hs).1, (mergeSaturateF_fields hs).2.2,
      execRunRules_fields.1, execRunRules_fields.2.2]
    exact hrules
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    exact fun r hr => Actions.SetLegal.update hunused.1 (hrules r hr)

/-! #### The three containment theorems -/

/-- `execCmdM_contained` with the three fields `Database.Contained` ignores. The extra
equalities are what `CmdStep.mono` consumes, so the program induction can start its tail
from the witness the head produced. -/
theorem execCmdM_contained' {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Recorded db ∧
      d'.toDatabase.sig = db.sig ∧ d'.toDatabase.env = db.env ∧
      d'.toDatabase.rules = db.rules := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
    have hmerges₁ : Signature.MergesLegal d₁.sig := by
      rw [execAction_sig hd₁]; exact hmerges
    obtain ⟨db, hcl, hcont⟩ :=
      mergeSaturateF_contained (h.execAction hlegal hd₁) hmerges₁ hsat
    refine ⟨db, .action (FDatabase.execAction_evalAction hd₁) hcl, hcont, ?_, ?_, ?_⟩
    · show d'.sig = db.sig
      rw [MergeClosure.sig hcl]; exact (mergeSaturateF_fields hsat).1
    · show d'.env = db.env
      rw [(MergeClosure.envRules hcl).1]; exact (mergeSaturateF_fields hsat).2.1
    · show ({r | r ∈ d'.rules} : Set Rule) = db.rules
      rw [(MergeClosure.envRules hcl).2, (mergeSaturateF_fields hsat).2.2]
      rfl
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    refine ⟨{ d.toDatabase with rules := insert r d.toDatabase.rules }, .rule,
      (Database.Recorded.refl h.rowsWF).setEnvRules _ _ _ _, rfl, rfl, ?_⟩
    show ({r' | r' ∈ r :: d.rules} : Set Rule) = insert r {r' | r' ∈ d.rules}
    ext r'
    simp
  | run =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨R, hRstep, hRcont⟩ := execRunRules_contained h
    have hRsig : R.sig = d.sig := MergeClosure.sig hRstep
    have hRenv : R.env = d.env := (MergeClosure.envRules hRstep).1
    have hRrules : R.rules = d.toDatabase.rules := (MergeClosure.envRules hRstep).2
    have hmerges₁ : Signature.MergesLegal (execRunRules d).sig := by
      rw [execRunRules_fields.1]; exact hmerges
    obtain ⟨db₂, hcl₂, hcont₂⟩ :=
      mergeSaturateF_contained (h.execRunRules hrules) hmerges₁ hs
    obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
      MergeClosure.transport hRcont (by rw [hRsig]; exact execRunRules_fields.1) hcl₂
    refine ⟨db₃, .run (hRstep.trans hcl₃), hcont₂.trans_contained hcont₃, ?_, ?_, ?_⟩
    · show d'.sig = db₃.sig
      rw [MergeClosure.sig hcl₃, hRsig, (mergeSaturateF_fields hs).1,
        execRunRules_fields.1]
    · show d'.env = db₃.env
      rw [(MergeClosure.envRules hcl₃).1, hRenv, (mergeSaturateF_fields hs).2.1,
        execRunRules_fields.2.1]
    · show ({r | r ∈ d'.rules} : Set Rule) = db₃.rules
      rw [(MergeClosure.envRules hcl₃).2, hRrules, (mergeSaturateF_fields hs).2.2,
        execRunRules_fields.2.2]
      rfl
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    refine ⟨{ d.toDatabase with sig := Function.update d.toDatabase.sig f (some dc) },
      .decl, ⟨subset_rfl, fun r hr => ?_, subset_rfl⟩, rfl, rfl, rfl⟩
    -- The interpreter's own state is `Recorded` in it *syntactically*: no row has moved,
    -- so the key congruence is reflexivity and the signature change cannot touch it. This
    -- is the case `CmdStep.mono_recorded` cannot do, and the reason is that it starts from
    -- a witness whose rows have moved.
    exact Database.out_self hr fun a ha => (h.rowsWF r hr).1 a ha

/-- **The interpreter's answer to one command is contained in one the specification
reaches.**

`.action` is `execAction_evalAction` followed by `mergeSaturateF_contained`, which is
`CmdStep.action`'s two premises exactly — the specification's merge phase is what pays
for the interpreter's, and before `CmdStep.action` had one this theorem was **false**
(the deleted `Falsity.claim2`). `.run` is `execRunRules_contained` re-based by
`MergeClosure.transport`. `.rule` and `.decl` land on the specification's state on the
nose.

`hlegal` and `hrules` are `Inv.execAction`'s and `Inv.execActions`'s premises; `hmerges`
is what a merge body needs and `Program.SetLegal` does not supply. -/
theorem execCmdM_contained {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Recorded db := by
  obtain ⟨db, hstep, hcont, -, -, -⟩ := execCmdM_contained' h hlegal hmerges hrules hs
  exact ⟨db, hstep, hcont⟩

theorem execProgramM_contained_aux {p : Program} : ∀ {d d' : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig →
    (∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) →
    d.ProgramLegal p → d.execProgramM p = some d' →
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Recorded db := by
  induction p with
  | nil =>
    intro d d' hinv _ _ _ hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact ⟨d.toDatabase, .nil, hs ▸ Database.Recorded.refl hinv.rowsWF⟩
  | cons c cs ih =>
    intro d d' h hmerges hrules hp hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, hd₁, hcs⟩ := Option.bind_eq_some_iff.mp hs
    rw [FDatabase.ProgramLegal] at hp
    obtain ⟨hlegal, hunused, hmerges', hnext⟩ := hp
    obtain ⟨db₁, hstep₁, hcont₁, hsig₁, henv₁, hrules₁⟩ :=
      execCmdM_contained' h hlegal hmerges hrules hd₁
    obtain ⟨db₂, hstep₂, hcont₂⟩ :=
      ih (h.execCmdM hlegal hmerges hunused hrules hd₁)
        (by rw [execCmdM_sig hd₁]; exact hmerges')
        (execCmdM_rulesLegal hlegal hunused hrules hd₁) (hnext d₁ hd₁) hcs
    obtain ⟨db₃, hstep₃, hcont₃, hsig₃, -, -⟩ :=
      ProgramStep.mono_recorded hcont₁ hsig₁ henv₁ hrules₁
        (h.execCmdM hlegal hmerges hunused hrules hd₁).solid hstep₂
    exact ⟨db₃, .cons hstep₁ hstep₃, hcont₂.trans hcont₃⟩

/-- **The interpreter's answer to a whole program is contained in one the specification
reaches.**

`execCmdM_contained'` per command, with `ProgramStep.mono` re-basing the tail's witness
onto the head's — which is where `ValidSubst.mono` is spent, read forwards: a larger
specification state still admits every match, so the specification can follow along.

`hp` is the per-command bundle. It is what carries the induction across a `.decl`:
`FDatabase.Inv` is not preserved by an arbitrary declaration (`Falsity.claim1`), and
`FDatabase.Unused` is the weakest thing that restores it — the declaration names
something the state does not yet mention, which is what egglog's front end requires
anyway. It does not restrict which `:merge` functions a program may declare, so the
merge fragment is not excluded. -/
theorem execProgramM_contained {d d' : FDatabase} (h : d.Inv) {p : Program}
    (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hp : d.ProgramLegal p) (hs : d.execProgramM p = some d') :
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Recorded db :=
  execProgramM_contained_aux h hmerges hrules hp hs

end FDatabase

/-- **The contract for `execM`.** `execProgramM_contained` from `FDatabase.empty`, whose
two global side conditions discharge themselves: the empty signature declares no merge
body and the empty state has no rules. `hp` is what remains, and `FDatabase.ProgramLegal`
is stated so that a front end which declares before use and type-checks its merge bodies
satisfies it.

See the section header above for why the contract is `Database.Recorded` rather than the
equality `exec_programStep` enjoys, and `Spec/Merge.lean` for why it is that rather than
`Database.Contained`. -/
theorem execM_contained {p : Program} (hp : FDatabase.empty.ProgramLegal p)
    {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Recorded db :=
  FDatabase.execProgramM_contained FDatabase.Inv.empty
    (fun g body res hg => by
      rw [Signature.mergeOf_of_none (show FDatabase.empty.sig g = none from rfl)] at hg
      exact absurd hg (by simp))
    (fun r hr => absurd hr (by simp [FDatabase.empty])) hp h

end Egglog
