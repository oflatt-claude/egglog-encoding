import EgglogSemantics.Spec.Merge
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Interp

/-!
# What M9 has to prove

`MERGE.md` says which theorem buys what. Five are still unproved; the rest are proved.

The load-bearing one is `mcong_iff_cong`: where the rows are the constructor rows
(`Database.CtorRows`) and the signature is all constructors, the generalized relation is
exactly M2's `Cong`. That is what makes replacing `Cong` by `MCong` a refactor rather
than a rewrite — without it every M2–M8 theorem would have to be reproved rather than
transported.

Four statements needed repair, and the repairs are the interesting output:

* `execM_reachable` is false without side conditions — a `set` on a constructor breaks
  `CtorRows`, which is the only route from `ValidSubst` to `MValidSubst`. It carries
  `Program.CtorDecls` and `Program.SetLegal` and is **proved**; its docstring justifies
  both, and `Proofs/Counterexamples.lean`'s `execM_reachable_needs_setLegal` shows the
  second cannot be dropped.
* `MCong.mono`, `MCongList.mono` and `Database.Out.mono` are **false** as stated:
  `Contained` ignores `sig` and `fd` fires only at `.union`. See
  `mcong_mono_needs_sig`. They carry `d₁.sig = d₂.sig`.
* `MergeStep.self_id` and `MergeStep.wf` need the row half of well-formedness
  (`Database.RowsWF`), which `Database.WF` deliberately omits, and `self_id`
  additionally needs `ctorRowsOf db.terms ⊆ db.rows`.
* `FDatabase.closureF_ok`'s `←` direction is false without "every application the
  database holds is a `.union` function's".

`MergeStep.diamond_of_join` and `RunStep.unique_of_confluent` are the two `MERGE.md`
flags as guesses, and both have hypotheses that cannot be used; their docstrings say
what replaces them.
-/

namespace Egglog
/-! ### Constructor-determined rows

`Database.toM` is gone: `Database` *is* the M9 database now, so the embedding it named
is the identity and `CtorRows` is what the theorem below quantifies over instead. -/
theorem Database.mem_rows_iff {db : Database} (h : db.CtorRows) {f : FnName}
    {as vs : List Term} :
    Row.mk f as vs ∈ db.rows ↔ vs = [.app f as] ∧ Term.app f as ∈ db.terms := by
  rw [h]; exact Iff.rfl

/-! ### The generalized relation is the old one

Two directions, two hypotheses. `MCong → Cong` needs only that the rows are constructor
rows, because a constructor row is one whatever the signature says. `Cong → MCong` also
needs `AllConstructors`, which is what licenses `fd`. -/
mutual

/-- Every functional-dependency derivation over constructor rows is an M2 derivation.

`fd` is the only interesting case: its two rows are constructor rows, so their outputs
are `.app f as` and `.app f bs` and both applications are in `db.terms` — the two
premises `Cong.congr` wants. -/
theorem MCong.toCong {db : Database} (hrows : db.CtorRows) {a b : Term}
    (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong hrows h)
  | .trans h₁ h₂ => exact .trans (MCong.toCong hrows h₁) (MCong.toCong hrows h₂)
  | .fd ha hb _ hl hxy =>
    obtain ⟨rfl, hma⟩ := (Database.mem_rows_iff hrows).mp ha
    obtain ⟨rfl, hmb⟩ := (Database.mem_rows_iff hrows).mp hb
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList hrows hl)

theorem MCongList.toCongList {db : Database} (hrows : db.CtorRows) {as bs : List Term}
    (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.toCong hrows hab) (MCongList.toCongList hrows hl)

end

mutual

/-- Every M2 derivation is a functional-dependency derivation.

`congr` is the only interesting case, and its two membership premises are exactly what is
needed: `RowsComplete` turns each into a row `fd` can use, and `CtorTerms` says the
function they are applications of is a constructor, which is what lets `fd` fire.

Stated over `CtorTerms`/`RowsComplete` rather than `AllConstructors`/`CtorRows` because
those two **survive merging** — they constrain `terms` and the constructor rows, neither
of which a merge touches (`FDatabase.mergeRound_confined`) — whereas `CtorRows` fails at
the first `:merge` declaration. That is what lets the interpreter's `closureF`, which
computes `Cong`, be read as `MCong` in a database that has merge functions in it, and it
is the reason the refinement chain below can exist at all. -/
theorem Cong.toMCong' {db : Database} (hterms : db.CtorTerms) (hrows : db.RowsComplete)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong' hterms hrows h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong' hterms hrows h₁) (Cong.toMCong' hterms hrows h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs])
      (hrows ⟨rfl, hma⟩) (hrows ⟨rfl, hmb⟩) (hterms f as hma)
      (CongList.toMCongList' hterms hrows hl) (by simp)

theorem CongList.toMCongList' {db : Database} (hterms : db.CtorTerms)
    (hrows : db.RowsComplete) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong' hterms hrows hab) (CongList.toMCongList' hterms hrows hl)

end

/-- `AllConstructors` gives `CtorTerms`: `mergeOf` defaults an undeclared name to `.union`
and `AllConstructors` says every declared one is `.union` too. -/
theorem Signature.AllConstructors.ctorTerms {db : Database}
    (hsig : db.sig.AllConstructors) : db.CtorTerms :=
  fun f _ _ => Signature.mergeOf_eq_union hsig f

/-- `CtorRows` gives `RowsComplete`: it is the equality, this is one inclusion of it.

Written with `▸` rather than `h.ge`: the latter goes through `Set`'s order instances and
puts `Classical.choice` into the axiom set of everything downstream, including
`mcong_iff_cong`, which is otherwise `propext` alone. -/
theorem Database.CtorRows.rowsComplete {db : Database} (h : db.CtorRows) :
    db.RowsComplete := fun _ hr => h.symm ▸ hr

theorem Cong.toMCong {db : Database} (hsig : db.sig.AllConstructors) (hrows : db.CtorRows)
    {a b : Term} (h : Cong db a b) : MCong db a b :=
  Cong.toMCong' hsig.ctorTerms hrows.rowsComplete h

theorem CongList.toMCongList {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs :=
  CongList.toMCongList' hsig.ctorTerms hrows.rowsComplete h

/-- **The compatibility theorem.** Where the rows are the constructor rows and every
function is a constructor, the functional dependency *is* congruence.

This is what `PLAN.md` M9 asks for, and the reason `MCong` has no `congr` constructor:
congruence is not lost, it is `fd` read at constructor rows.

It replaces `mcong_toM_iff`, which quantified over the embedding `Database.toM` of an
M2 database into a separate `MDatabase`. Now that the two states are one structure that
embedding is the identity, so the *hypothesis* `CtorRows` carries what the embedding
used to: it says the state is in the constructor-only fragment. The theorem's content is
unchanged and its proof is the same four `match` cases. -/
theorem mcong_iff_cong {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {a b : Term} : MCong db a b ↔ Cong db a b :=
  ⟨MCong.toCong hrows, Cong.toMCong hsig hrows⟩

/-- **The compatibility theorem, at a state a program can reach.** A program that declares
only constructors and never `set`s one runs to a database where the two relations agree.

`Proofs/Step.lean`'s `ProgramStep.ctorState` supplies both hypotheses; this is the
composition, which lives here because that is where `mcong_iff_cong` is. -/
theorem ProgramStep.mcong_iff_cong {p : Program} {db : Database}
    (hstep : ProgramStep Database.empty p db) (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) {a b : Term} : MCong db a b ↔ Cong db a b :=
  let hc := ProgramStep.ctorState Database.CtorState.empty hdecl hlegal hstep
  Egglog.mcong_iff_cong hc.sig hc.rows

/-- Congruence, recovered as a derived rule rather than a constructor. -/
theorem MCong.congr {db : Database} {f : FnName} {as bs : List Term}
    (ha : Row.mk f as [.app f as] ∈ db.rows) (hb : Row.mk f bs [.app f bs] ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.union) (hl : MCongList db as bs) :
    MCong db (.app f as) (.app f bs) :=
  .fd ha hb hsig hl (by simp)

/-! ### The constructor fragment collapses

`mcong_iff_cong` says the generalized congruence is the old one there. These say the
same of the *step* relations: no merge fires, so a round is `RunRules` and nothing
else. -/
/-- The rest of M9 collapses too: with no `.merge` function there is no collision to
resolve, so a round is `RunRules` and nothing else. Companion to `mcong_iff_cong` on
the *step* side — together they say M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : Database}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  cases h with
  | collide _ _ _ hm _ _ =>
    rw [Signature.mergeOf_eq_union hsig] at hm
    exact absurd hm (by simp)

/-! ### The least-congruence principle

How every negative fact about the closure gets proved, and the shape the M11
checker-soundness argument takes. `Cong.le` with the `congr` hypothesis replaced by an
`fd` one. -/
mutual

/-- `MCong db` is the least relation closed under `db`'s assertions, reflexivity on its
terms, symmetry, transitivity and the functional dependency. -/
theorem MCong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {a b : Term} (h : MCong db a b) : R a b := by
  match h with
  | .assert hm => exact hassert _ _ hm
  | .refl hm => exact hrefl _ hm
  | .symm h => exact hsymm _ _ (MCong.le hassert hrefl hsymm htrans hfd h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (MCong.le hassert hrefl hsymm htrans hfd h₁)
      (MCong.le hassert hrefl hsymm htrans hfd h₂)
  | .fd hra hrb hu hl hxy =>
    exact hfd _ _ _ _ _ _ _ hra hrb hu (MCongList.le hassert hrefl hsymm htrans hfd hl) hxy

/-- `MCong.le` over key tuples; the companion `MCong.le`'s `fd` case recurses into. -/
theorem MCongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {as bs : List Term} (h : MCongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.le hassert hrefl hsymm htrans hfd hab)
      (MCongList.le hassert hrefl hsymm htrans hfd hl)

end

/-- `MCong db` is an equivalence on `db.terms`, as `Cong.setoid`. Its quotient is the
e-class set, and the bridge to M11: an e-class here is an `@UF` leader there. -/
def MCong.setoid (db : Database) : Setoid {t : Term // t ∈ db.terms} where
  r a b := MCong db a.val b.val
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

/-! ### `MCongList` is an equivalence

`MCong.setoid` pointwise. `Out.union_cong` needs it: two lookups at one key class reach
their rows through *different* congruent keys, and `fd` compares those two directly. -/
theorem MCongList.symm {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    MCongList db bs as := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab.symm (MCongList.symm hl)

theorem MCongList.trans {db : Database} {as bs cs : List Term} (h₁ : MCongList db as bs)
    (h₂ : MCongList db bs cs) : MCongList db as cs := by
  match h₁, h₂ with
  | .nil, .nil => exact .nil
  | .cons hab hl₁, .cons hbc hl₂ => exact .cons (hab.trans hbc) (MCongList.trans hl₁ hl₂)

theorem MCongList.forall₂ {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    List.Forall₂ (MCong db) as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab (MCongList.forall₂ hl)

theorem MCongList.ofForall₂ {db : Database} {as bs : List Term}
    (h : List.Forall₂ (MCong db) as bs) : MCongList db as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

/-! ### Monotonicity

Constraint (3). That a merge *adds* the combined row instead of replacing the two it
combined is exactly what these need.

All three carry an **added hypothesis** `d₁.sig = d₂.sig`, and it is not decoration:
`Database.Contained` ignores `sig`, while `MCong.fd` fires only where
`mergeOf f = .union`, so redeclaring `f` as `:no-merge` destroys a derivation without
removing anything. `mcong_mono_needs_sig` below is the counterexample. Every use in this
file has it — `MergeStep.sig` and `MergeClosure.sig` — because only `Cmd.decl` writes
`sig`. -/
mutual

/-- Adding terms, rows and equalities only adds derivations. `Cong.mono`, with the
`fd` case in place of `congr`. -/
theorem MCong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {a b : Term} (hc : MCong d₁ a b) : MCong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .refl hm => exact .refl (h.terms hm)
  | .symm hc => exact .symm (MCong.mono h hsig hc)
  | .trans h₁ h₂ => exact .trans (MCong.mono h hsig h₁) (MCong.mono h hsig h₂)
  | .fd hra hrb hu hl hxy =>
    exact .fd (h.rows hra) (h.rows hrb) (hsig ▸ hu) (MCongList.mono h hsig hl) hxy

theorem MCongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {as bs : List Term} (hc : MCongList d₁ as bs) : MCongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.mono h hsig hab) (MCongList.mono h hsig hl)

end

/-- **Why `MCong.mono` needs the signature hypothesis.** Two rows of `f` recording
different outputs at one key make those outputs `fd`-equal while `f` is a constructor.
Declaring `f` `:no-merge` adds no term, row or equality — so `Contained` still holds —
and takes the derivation away. -/
theorem mcong_mono_needs_sig : ∃ d₁ d₂ : Database, ∃ a b : Term,
    d₁.Contained d₂ ∧ MCong d₁ a b ∧ ¬ MCong d₂ a b := by
  classical
  let x : Term := .lit (.int 0)
  let y : Term := .lit (.int 1)
  let rows : Set Row := {Row.mk "f" [] [x], Row.mk "f" [] [y]}
  let d₁ : Database := ⟨fun _ => none, ∅, rows, ∅, [], ∅⟩
  let d₂ : Database := ⟨fun _ => some ⟨0, 1, .noMerge⟩, ∅, rows, ∅, [], ∅⟩
  refine ⟨d₁, d₂, x, y, ⟨subset_rfl, subset_rfl, subset_rfl⟩, ?_, ?_⟩
  · exact MCong.fd (f := "f") (as := []) (bs := []) (a := [x]) (b := [y])
      (by simp [d₁, rows]) (by simp [d₁, rows]) rfl .nil (by simp)
  · intro h
    have hxy : x = y :=
      MCong.le (R := fun a b => a = b) (by simp [d₂]) (by simp [d₂]) (fun _ _ h => h.symm)
        (fun _ _ _ h₁ h₂ => h₁.trans h₂)
        (fun _ _ _ _ _ _ _ _ _ hu _ _ => absurd hu (by simp [d₂, Signature.mergeOf])) h
    simp [x, y] at hxy

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, MCongList.mono h hsig hl, h.rows hrow⟩

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `MCong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
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
    (hsig : db.sig.mergeOf f = MergeSpec.merge body res)
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

/-- **A `.union` function's outputs are all congruent.**

The functional dependency, stated as what it buys: however many rows a `.union`
function accumulates at one key class, they are one e-class. For `@UF_<Sort>` this is
"every parent a term ever had is equal to it"; for `@<C>View` it is congruence. -/
theorem Database.Out.union_cong {db : Database} {f : FnName} {as v w : List Term}
    {x y : Term} (hsig : db.sig.mergeOf f = MergeSpec.union) (hv : db.Out f as v)
    (hw : db.Out f as w) (hxy : (x, y) ∈ v.zip w) : MCong db x y := by
  obtain ⟨bs, hlb, hrb⟩ := hv
  obtain ⟨cs, hlc, hrc⟩ := hw
  exact .fd hrb hrc hsig (hlb.symm.trans hlc) hxy

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
theorem MValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : MValidSubst d₁ p σ) :
    MValidSubst d₂ p σ := by
  have hsig₁ : ∀ t : Term, (d₁.addTerm t).sig = (d₂.addTerm t).sig := fun _ => hsig
  cases h with
  | expr hv hw he hcong =>
    refine .expr ?_ (hc.terms hw) ?_ (MCong.mono (hc.addTerm_mono _) (hsig₁ _) hcong)
    · rw [henv]; exact hv.mono hc
    · rw [henv, ← hsig]; exact he
  | eq hv hw he₁ he₂ hc₁ hc₂ =>
    refine .eq ?_ (hc.terms hw) ?_ ?_
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₁)
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₂)
    · rw [henv]; exact hv.mono hc
    · rw [henv, ← hsig]; exact he₁
    · rw [henv, ← hsig]; exact he₂
  | @values vs f as σ us ts ws bs hv hu ht hk hw hrow =>
    refine .values ?_ ?_ ?_
      (MCongList.mono ((hc.addTerms_mono ts).addTerms_mono us) (by simp [hsig]) hk)
      (MCongList.mono ((hc.addTerms_mono ts).addTerms_mono us) (by simp [hsig]) hw)
      (hc.rows hrow)
    · rw [henv]; exact hv.mono hc
    · rw [henv, ← hsig]; exact hu
    · rw [henv, ← hsig]; exact ht

theorem MValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : MValidQuerySubst d₁ q σ) : MValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => MValidSubst.mono hc hsig henv hv, hu⟩

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

/-- **A merge collision available at `A` is available at any `C` containing it.**

No `env`/`rules` hypothesis is needed: a `MergeStep` overwrites the environment with
`mergeEnv a b` before running the body and restores the caller's `env`/`rules`
afterwards, so neither field is ever read. `sig` is needed, because `MCongList.mono` is.
-/
theorem MergeStep.transport {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (h : MergeStep A B) : ∃ D, MergeStep C D ∧ B.Contained D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f as bs a b vs body res hra hrb hcong hm hbody hres =>
    have hc0 : ({ A with env := mergeEnv a b } : Database).Contained
        { C with env := mergeEnv a b } := ⟨hc.terms, hc.rows, hc.eqs⟩
    obtain ⟨dC, hstepC, hcont, hsig', henv'⟩ := evalActions_mono hc0 hsig rfl hbody
    refine ⟨{ dC.addRow f as vs with env := C.env, rules := C.rules },
      .collide (hc.rows hra) (hc.rows hrb) (MCongList.mono hc hsig hcong)
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

/-! ### The relational semantics is the functional one, on the constructor fragment

`Spec/Step.lean`'s `runProgram` and `Spec/Merge.lean`'s `ProgramStep` are the same
semantics written twice, and on a program that declares only constructors and never
`set`s one they agree exactly. That is what `execM_reachable` needs.

**Actions are no longer part of this.** `CmdStep.action`, `RuleResults` and
`MergeStep.collide` all read `evalAction`/`evalActions` directly, so the layer that used
to need two bridge theorems and a primitive-free hypothesis in each direction needs none.
What
is left is the layer that really does have two readings — e-matching, where `MCong`
replaces `Cong` — and the round above it, and both directions are needed: `RunStep` pins
`db'` to `RunRules db` on a constructor signature, so `stepCmd`'s `runRules db` has to be
*equal* to `RunRules db` rather than merely contained in it. -/
/-- `ValidSubst → MValidSubst`. `mcong_iff_cong` is applied at the *extended* database the
witness premises ask over, which is why `CtorRows.addTerm` appears. -/
theorem MValidSubst.of_validSubst {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {p : Pattern} {σ : Env} (h : ValidSubst db p σ) :
    MValidSubst db p σ := by
  cases h with
  | @expr e σ w t hve hw heval hcong =>
    exact .expr hve hw heval (Cong.toMCong (db := db.addTerm t) hsig (hrows.addTerm t) hcong)
  | @eq e₁ e₂ σ w t₁ t₂ hve hw hev₁ hev₂ hcw hct =>
    exact .eq hve hw hev₁ hev₂
      (Cong.toMCong (db := (db.addTerm t₁).addTerm t₂) hsig
        ((hrows.addTerm t₁).addTerm t₂) hcw)
      (Cong.toMCong (db := (db.addTerm t₁).addTerm t₂) hsig
        ((hrows.addTerm t₁).addTerm t₂) hct)
  | @values vs f as σ us ts ws bs hve hev₁ hev₂ hct hcu hrow =>
    have hsig' : ((db.addTerms ts).addTerms us).sig.AllConstructors := by simpa using hsig
    have hrows' : ((db.addTerms ts).addTerms us).CtorRows := (hrows.addTerms ts).addTerms us
    exact .values hve hev₁ hev₂
      (CongList.toMCongList hsig' hrows' hct) (CongList.toMCongList hsig' hrows' hcu) hrow

theorem ValidSubst.of_mvalidSubst {db : Database} (hrows : db.CtorRows) {p : Pattern}
    {σ : Env} (h : MValidSubst db p σ) : ValidSubst db p σ := by
  cases h with
  | @expr e σ w t hve hw heval hcong =>
    exact .expr hve hw heval (MCong.toCong (hrows.addTerm t) hcong)
  | @eq e₁ e₂ σ w t₁ t₂ hve hw hev₁ hev₂ hcw hct =>
    exact .eq hve hw hev₁ hev₂
      (MCong.toCong ((hrows.addTerm t₁).addTerm t₂) hcw)
      (MCong.toCong ((hrows.addTerm t₁).addTerm t₂) hct)
  | @values vs f as σ us ts ws bs hve hev₁ hev₂ hct hcu hrow =>
    have hrows' : ((db.addTerms ts).addTerms us).CtorRows := (hrows.addTerms ts).addTerms us
    exact .values hve hev₁ hev₂
      (MCongList.toCongList hrows' hct) (MCongList.toCongList hrows' hcu) hrow

theorem forall₂_mvalidSubst {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {q : Query} {σs : List Env}
    (h : List.Forall₂ (ValidSubst db) q σs) : List.Forall₂ (MValidSubst db) q σs := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons (MValidSubst.of_validSubst hsig hrows hp) ih

theorem forall₂_validSubst {db : Database} (hrows : db.CtorRows) {q : Query}
    {σs : List Env} (h : List.Forall₂ (MValidSubst db) q σs) :
    List.Forall₂ (ValidSubst db) q σs := by
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons (ValidSubst.of_mvalidSubst hrows hp) ih

theorem MValidQuerySubst.of_validQuerySubst {db : Database}
    (hsig : db.sig.AllConstructors) (hrows : db.CtorRows) {q : Query} {σ : Env}
    (h : ValidQuerySubst db q σ) : MValidQuerySubst db q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, forall₂_mvalidSubst hsig hrows hall, hu⟩

theorem ValidQuerySubst.of_mvalidQuerySubst {db : Database} (hrows : db.CtorRows)
    {q : Query} {σ : Env} (h : MValidQuerySubst db q σ) : ValidQuerySubst db q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, forall₂_validSubst hrows hall, hu⟩

/-- One rule contributes the same databases either way. Both sides run
`evalLocalActions` on the substitutions their matcher admits, so identifying the matchers
is the whole proof. -/
theorem ruleResults_eq {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {r : Rule} : RuleResults db r = ruleResults db r := by
  ext d
  exact ⟨fun ⟨σ, hq, hd⟩ => ⟨σ, ValidQuerySubst.of_mvalidQuerySubst hrows hq, hd⟩,
    fun ⟨σ, hq, hd⟩ => ⟨σ, MValidQuerySubst.of_validQuerySubst hsig hrows hq, hd⟩⟩

/-- **A round is the same round.** Both sides are `db.sUnion` of a family indexed by
`db.rules`, and `ruleResults_eq` identifies the families. -/
theorem runRules_eq {db : Database} (h : db.CtorState) : RunRules db = runRules db := by
  have hre : ∀ r : Rule, RuleResults db r = ruleResults db r :=
    fun r => ruleResults_eq h.sig h.rows
  have hset : {d | ∃ r ∈ db.rules, d ∈ RuleResults db r}
      = {d | ∃ r ∈ db.rules, d ∈ ruleResults db r} := by
    ext d
    exact ⟨fun ⟨r, hr, hd⟩ => ⟨r, hr, hre r ▸ hd⟩, fun ⟨r, hr, hd⟩ => ⟨r, hr, (hre r).symm ▸ hd⟩⟩
  rw [RunRules, runRules, hset]

/-- `stepCmd → CmdStep`. The `MergeClosure` phase `CmdStep.action` carries is supplied by
*zero* steps: `MergeStep` never fires on a constructor signature, so the merge leg is the
identity and `Relation.ReflTransGen.refl` is the whole of it. -/
theorem CmdStep.of_stepCmd {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hv : stepCmd db c = some db') : CmdStep db c db' := by
  cases c with
  | action a => exact .action hv Relation.ReflTransGen.refl
  | rule r => simp only [stepCmd, Option.some.injEq] at hv; exact hv ▸ .rule
  | run =>
    simp only [stepCmd, Option.some.injEq] at hv
    refine .run ?_
    rw [RunStep, runRules_eq h, ← hv]
    exact Relation.ReflTransGen.refl
  | decl f d => simp only [stepCmd, Option.some.injEq] at hv; exact hv ▸ .decl

/-- The converse, away from `(run)` — the one command whose two readings can come apart,
since a `MergeClosure` of length zero is a choice the relation makes and the function does
not. Reading a concrete run backwards is what needs it. -/
theorem CmdStep.stepCmd_eq {db db' : Database} {c : Cmd} (h : CmdStep db c db')
    (hsig : db.sig.AllConstructors) (hrun : c ≠ Cmd.run) : stepCmd db c = some db' := by
  cases h with
  | action ha hm =>
    have hd := hm.eq_of_allConstructors (by rw [evalAction_sig ha]; exact hsig)
    subst hd
    exact ha
  | rule => rfl
  | run _ => exact absurd rfl hrun
  | decl => rfl

theorem ProgramStep.of_runProgram {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig)
    (hv : runProgram db p = some db') : ProgramStep db p db' := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ hv : db = db') ▸ .nil
  | cons c cs ih =>
    cases hc : stepCmd db c with
    | none => simp [hc] at hv
    | some db₁ =>
      simp only [runProgram_cons, hc, Option.bind_some] at hv
      exact .cons (CmdStep.of_stepCmd h hc)
        (ih (stepCmd_ctorState h (hdecl c (by simp)) hlegal.1 hc)
          (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
          (by rw [stepCmd_sig hc]; exact hlegal.2) hv)

/-- The bridge from the initial state, where every side condition is discharged by
`Database.CtorState.empty`. -/
theorem run_programStep {p : Program} {D : Database} (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) (h : run p = some D) :
    ProgramStep Database.empty p D :=
  ProgramStep.of_runProgram Database.CtorState.empty hdecl hlegal h


/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than M10's on purpose:
the spec admits several results, so the interpreter's is one of them rather than *the*
one. -/
/-- **The M9 refinement: reachability, not equality.**

`exec_toDatabase` says the constructor interpreter computes exactly `run p`. Here the
spec is a relation, so the statement is that the interpreter lands on a state the spec
reaches. Nothing stronger is available, and nothing stronger is wanted — pinning a
single result would mean pinning the merge order, which is the thing `MERGE.md` argues
the semantics should decline to pin.

**The two hypotheses**, neither removable:

* `Program.CtorDecls` gives `Signature.AllConstructors` at every intermediate state
  (`Signature.AllConstructors.sigBind`), which is what makes `MergeStep` vacuous and so
  how the `MergeClosure` phase of `CmdStep.action` gets discharged
  (`MergeClosure.eq_of_allConstructors`).
* `Program.SetLegal` keeps `Database.CtorRows`, which with the above is `mcong_iff_cong`,
  which is the only route from `ValidSubst` to `MValidSubst` — so it is what makes a
  *round* agree. It is not decoration:
  `Proofs/Counterexamples.lean`'s `execM_reachable_needs_setLegal` is a program satisfying
  the other whose `exec` state no `ProgramStep` reaches.

**The primitive-free hypothesis is gone**, and with it the whole action bridge. It was
there because
`Expr.eval` built the term `ordering-min 1 2` where `MEval.prim` computed `1`; with one
evaluator resolving primitives itself the two readings of an action are the same call, so
`CmdStep.action` and `RuleResults` need nothing proved about them. What is left needing
proof is e-matching, where `MCong` really does replace `Cong`, and the round above it. -/
theorem execM_reachable {p : Program} {d : FDatabase} (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) (h : exec p = some d) :
    ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  rw [FDatabase.toDatabase_empty]
  refine run_programStep hdecl hlegal ?_
  rw [← exec_toDatabase, h, Option.map_some]

/-! ### The contract for `execM`: containment, not reachability

`execM_reachable`'s shape is unavailable for `execM`, and not because it is hard —
because it is **false**. The implementation's merge phase deletes the rows it merged and
the specification never deletes, so no `ProgramStep` state equals the implementation's:
a spec run that performed the same merges still holds the two originals, and a spec run
that performed none holds no combined row. `execM_reachable` above survives only because
`exec` is `Impl/Interp.lean`'s constructor interpreter, which has no merge phase at all
(`FDatabase.mergeRound_eq_self` and `hasMergeRow_eq_false`) — the layering is intact.

What replaces it is that the implementation's state is *contained* in one the spec
reaches: the implementation may find **fewer** results, never more. That is the safe
direction, because everything the M11 safety theorem reads is positive in the state, so
safety transfers downward. `MValidSubst.mono` is the step that makes "fewer rows" mean
"fewer matches" rather than merely "a different database".

The deletion adds one obligation on top of the plain refinement — that the witness `db`
can be chosen to have performed *at least* the merges the implementation did — which is
where `MergeClosure`'s freedom to take any number of steps is spent.

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

The chain has one prerequisite that is not obvious, and it is why `Cong.toMCong'` exists.
`patternHolds` compares keys with `congrKeys` at the closure of the database
extended with the atom's operands, and `closureF`
computes **`Cong`** — it closes over `eqsF` and `congrPair`, with no notion of a row. The
specification's row atom compares them with **`MCong`**. So every read the interpreter
performs has to be re-read as a specification read, and that is exactly `Cong.toMCong'`:
`CtorTerms` and `RowsComplete` are what license it, and unlike `CtorRows` they survive a
`:merge` declaration.

Hence `Inv`, which is what the induction actually carries. Prove its preservation lemmas
first; the rest of the chain is structural recursion once they are available. -/

/-- A term built only from constructor applications.

`CtorTerms` says the database holds only such terms; this is the same condition on one
term, which is what the operations that *insert* a term have to be given. -/
def Term.CtorTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → sig.mergeOf f = MergeSpec.union

/-- The invariant the refinement chain carries.

`wf` is what `mem_closureF_iff_of_wf` needs; `ctorTerms` and `rowsComplete` are what
`Cong.toMCong'` needs; `rowsWF` says a row talks only about terms the database holds, and
`ctorRows` is `closureF_ok`'s `hrow`. All five hold of `FDatabase.empty`.

The last two are not decoration. `ctorRows` is the reverse inclusion `RowsComplete` omits,
restricted to the `.union` functions where it survives a `:merge` declaration, and
`Action.SetLegal` is what preserves it. `rowsWF` was what kept `Expr.eval`'s lookup branch
inside the constructor fragment; with reading confined to the query it is no longer load
bearing for `execAction`, and is kept because it is the row half of `WF` and
`mergeOneWith` re-establishes it. -/
structure FDatabase.Inv (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete
  rowsWF : d.toDatabase.RowsWF
  ctorRows : ∀ r ∈ d.toDatabase.rows, d.sig.mergeOf r.fn = MergeSpec.union →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.toDatabase.terms

/-- The `sig`/`terms`/`rows` half of `FDatabase.Inv`, on a spec database. Everything but
`wf` constrains only those three fields, so it is proved once here and transported through
the `toDatabase_*` bridges. -/
structure Database.Inv0 (db : Database) : Prop where
  ctorTerms : db.CtorTerms
  rowsComplete : db.RowsComplete
  rowsWF : db.RowsWF
  ctorRows : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms

namespace Database

/-- Every listed term is held by `addTerms`. -/
theorem mem_terms_addTerms {db : Database} {ts : List Term} {t : Term} (h : t ∈ ts) :
    t ∈ (db.addTerms ts).terms := by
  induction ts generalizing db with
  | nil => simp at h
  | cons s ts ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact (Contained.addTerms ts (db.addTerm t)).terms (Or.inr t.self_mem_subterms)
    · exact ih h'

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
    (hf : db.sig.mergeOf f ≠ MergeSpec.union)
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

/-- `hf` is what keeps `ctorRows` true — a `set` on a constructor would add a row of a
`.union` function that is not that function's constructor row, which is exactly what
`Action.SetLegal` rules out. `has`/`hvs` are `addTerm`'s condition on the operands. -/
theorem FDatabase.Inv.addRow {d : FDatabase} (h : d.Inv) {f : FnName} {as vs : List Term}
    (hf : d.sig.mergeOf f ≠ MergeSpec.union)
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

/-- A literal mentions no application. -/
theorem Term.ctorTerm_lit {sig : Signature} {l : Lit} : Term.CtorTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

/-- A primitive returns one of its operands or a fresh literal, so it cannot introduce a
non-constructor application. -/
theorem Prim.apply_ctorTerm {sig : Signature} {p : Prim} {ts : List Term} {v : Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm sig t) (h : p.apply ts = some v) :
    Term.CtorTerm sig v := by
  unfold Prim.apply at h
  split at h
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMin
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMax
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · exact absurd h (by simp)

mutual

/-- **Evaluation only ever builds constructor terms.**

Each branch that produces a term stays inside the constructor fragment: the `.union`
branch's head is a constructor by the guard the evaluator just tested, and a primitive
returns an operand or a literal. Nothing reads a row, so no case has to place a recorded
output back in `terms`. This is what `Inv.execAction` needs. -/
theorem Expr.eval_ctorTerm {sig : Signature} {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm sig b.2) {e : Expr} {t : Term}
    (hs : e.eval sig σ = some t) : Term.CtorTerm sig t := by
  match e with
  | .lit l =>
    rw [Expr.eval_lit, Option.some_inj] at hs
    subst hs; exact Term.ctorTerm_lit
  | .var v =>
    rw [Expr.eval_var] at hs
    exact hσ (v, t) (Env.mem_of_lookup hs)
  | .app f args =>
    cases hp : Prim.ofName f with
    | some p =>
      rw [Expr.eval_app_prim hp, Option.bind_eq_some_iff] at hs
      obtain ⟨ts, hts, happ⟩ := hs
      exact Prim.apply_ctorTerm (Expr.evalList_ctorTerm hσ hts) happ
    | none =>
      cases hu : sig.mergeOf f with
      | union =>
        rw [Expr.eval_app_ctor hp hu, Option.map_eq_some_iff] at hs
        obtain ⟨ts, hts, rfl⟩ := hs
        have hts' := Expr.evalList_ctorTerm hσ hts
        intro g bs hsub
        rw [Term.subterms_app] at hsub
        rcases Set.mem_insert_iff.mp hsub with heq | hmem
        · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
          exact hu
        · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
          exact hts' x hx g bs hxs
      | merge body res => rw [Expr.eval_app_merge hp hu] at hs; exact absurd hs (by simp)
      | noMerge => rw [Expr.eval_app_noMerge hp hu] at hs; exact absurd hs (by simp)

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

/-- **`patternHolds` is sound for `MValidSubst`.**

`ValidEnv (p.freeVars d.env) d.toDatabase σ` is load-bearing, not decoration.
`patternHolds` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the
pattern never mentions still passes the test, while every `MValidSubst` constructor pins
`Env.dom σ` to a permutation of the pattern's free variables —
`Falsity.patternHolds_MValidSubst_false` is the witness. Nothing is lost by requiring
it: it is a *consequence* of the conclusion (`MValidSubst.validEnv`), so this is the
strongest statement whose conclusion can hold, and it is the hypothesis
`Proofs/Interp.lean`'s `patternHolds_iff` already carries.

`Interp.lean`'s `patternHolds_iff`, forward direction, with `Expr.eval` for `Expr.eval`
and `MValidSubst` for `ValidSubst`. Three gaps to bridge beyond that proof:

* `congrKeys` computes `Cong`, while `MValidSubst` wants `MCong` — `Cong.toMCong'` and
  `CongList.toMCongList'` close that, and their `CtorTerms`/`RowsComplete` hypotheses are
  `Inv` fields;
* every case closes over an *extended* database — `d.addTerm t` for `.expr`, and
  `(d.addTerms ts).addTerms us` for the row atom's key and value operands — so the bridge
  is applied at that database's `Inv`, from `Inv.addTerm`/`Inv.addTerms`;
* those need the instance to be a constructor term, which is
  `Expr.eval_ctorTerm`/`Expr.evalList_ctorTerm`, which in turn need the `ValidEnv`. -/
theorem FDatabase.patternHolds_MValidSubst {d : FDatabase} (h : d.Inv) {p : Pattern}
    {σ : Env} (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ)
    (hs : patternHolds d p σ = true) : MValidSubst d.toDatabase p σ := by
  have hσ := FDatabase.envAppend_ctorTerm h hv.2
  cases p with
  | expr e =>
    rw [patternHolds] at hs
    split at hs
    · exact absurd hs (by simp)
    · next t hev =>
      rw [decide_eq_true_eq] at hs
      obtain ⟨w, hwm, hcl⟩ := hs
      have ht : Term.CtorTerm d.sig t := Expr.eval_ctorTerm hσ hev
      have hInv := h.addTerm ht
      have hct := hInv.ctorTerms
      have hrc := hInv.rowsComplete
      rw [FDatabase.toDatabase_addTerm] at hct hrc
      exact .expr hv hwm (hev)
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm h.wf).mp hcl))
  | eq e₁ e₂ =>
    rw [patternHolds] at hs
    split at hs
    · next t₁ t₂ hev₁ hev₂ =>
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hs
      obtain ⟨heq, w, hwm, hcl⟩ := hs
      have ht₁ : Term.CtorTerm d.sig t₁ := Expr.eval_ctorTerm hσ hev₁
      have ht₂ : Term.CtorTerm d.sig t₂ := Expr.eval_ctorTerm hσ hev₂
      have hInv := (h.addTerm ht₁).addTerm ht₂
      have hct := hInv.ctorTerms
      have hrc := hInv.rowsComplete
      rw [FDatabase.toDatabase_addTerm, FDatabase.toDatabase_addTerm] at hct hrc
      exact .eq hv hwm (hev₁) (hev₂)
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm₂ h.wf).mp hcl))
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm₂ h.wf).mp heq))
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
      have hts : ∀ x ∈ ts, Term.CtorTerm d.sig x := Expr.evalList_ctorTerm hσ ht
      have hus : ∀ x ∈ us, Term.CtorTerm (d.addTerms ts).sig x := by
        simpa using Expr.evalList_ctorTerm hσ hu
      have hInv := (h.addTerms hts).addTerms hus
      have hct := hInv.ctorTerms
      have hrc := hInv.rowsComplete
      rw [FDatabase.toDatabase_addTerms, FDatabase.toDatabase_addTerms] at hct hrc
      exact .values hv (hu)
        (ht)
        (CongList.toMCongList' hct hrc ((FDatabase.congrTuple_addTerms_iff h.wf).mp hkey))
        (CongList.toMCongList' hct hrc ((FDatabase.congrTuple_addTerms_iff h.wf).mp hval))
        hr
    · exact absurd hs (by simp)

/-- The hypothesis `patternHolds_MValidSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. -/
theorem MValidSubst.validEnv {db : Database} {p : Pattern} {σ : Env}
    (h : MValidSubst db p σ) : ValidEnv (p.freeVars db.env) db σ := by
  cases h with
  | expr hv _ _ _ => exact hv
  | eq hv _ _ _ _ _ => exact hv
  | values hv _ _ _ _ _ => exact hv

/-- **Every substitution the enumerator produces is, up to `Env.Agree`, one
`MValidQuerySubst` admits.**

The `Env.Agree` is forced, and not by the `ValidEnv` defect above. `Query.freeVars`
deduplicates, so `matchQuery` binds a variable two patterns share exactly **once**;
`MValidQuerySubst` instead demands `Env.UnionAll σs σ`, which is literal
*concatenation* of one substitution per pattern, each binding its own pattern's free
variables. A query with a repeated variable therefore admits no `σ` on the nose — the
lengths cannot match — and `Falsity.matchQuery_MValidQuerySubst_false` is the witness.
`Proofs/Interp.lean`'s `validQuerySubst_of_mem_matchQuery` already concludes up to
`Env.Agree` for the same reason. -/
theorem FDatabase.matchQuery_MValidQuerySubst {d : FDatabase} (h : d.Inv) {q : Query}
    {σ : Env} (hs : σ ∈ matchQuery d q) :
    ∃ τ, MValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  rw [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at hs
  obtain ⟨⟨hdom, hval⟩, hall⟩ := hs
  have hall' : ∀ p ∈ q, MValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) :=
    fun p hp =>
      FDatabase.patternHolds_MValidSubst h (validEnv_canon hp hdom hval) (hall p hp)
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
superseded output and `MValidSubst.values` lets a rule read one, writing rows the
implementation never had. That last part is unverified — `closureF` does not reduce in the
kernel, so no program containing a rule has an `execM` that evaluates by `rfl`. -/
theorem execM_current_of_lattice {p : Program} {d : FDatabase}
    {le : List Term → List Term → Prop} (hexec : execM p = some d)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (hjoin : ∀ (f : FnName) (body : List Action) (res : List Expr) (a b vs : List Term),
      d.sig.mergeOf f = MergeSpec.merge body res →
      (∃ e, evalActions { d.toDatabase with env := mergeEnv a b } body = some e ∧
        Expr.evalList e.sig res e.env = some vs) → le a vs ∧ le b vs)
    {f : FnName} {as vs : List Term} {body : List Action} {res : List Expr}
    (hmerge : d.sig.mergeOf f = MergeSpec.merge body res)
    (hrow : Row.mk f as vs ∈ d.rows) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ db.Current le f as vs := by
  sorry

/-- The interpreter's merge phase against the specification's.

**False as stated, once the implementation deletes.** `MergeClosure` is
`Relation.ReflTransGen MergeStep` and `MergeStep.contained` says every step only grows the
state, so no `MergeClosure` can reach a database with *fewer* rows — which is exactly what
a pass now produces. The containment form below is what survives, and it is the merge-phase
instance of `execM_contained`.

Stated here with **no** hypothesis, which is why it is still open:
`FDatabase.mergeRound_contained` is this statement under `d.Inv` and `hlegal`, and both
are forced. `mergeOne` gates on `congrKeys d.closureF`, and `closureF` decides `Cong`
only for a well-formed database (`mem_closureF_iff_of_wf`), while `MergeStep` gates on
`MCongList`; and without `hlegal` the accumulator's `Inv` fails at the first merge body
that writes an illegal `set` (`Falsity.mergeRound_inv_false`). What `mergeRound_confined`
gives unconditionally is only that the rows the pass drops are merge rows and nothing
else. -/
theorem mergeRound_closure {d : FDatabase} :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  sorry

/-! #### `mcong_iff_cong` without `CtorRows`

`CtorRows` is an equality of row *sets*, which the interpreter's databases do not
satisfy once a `:merge` function has a row. The two halves it is used for are separated
here so `closureF_ok` can have only the halves that hold. -/
/-- `hrow` in reduced form. Stating it separately is the same trick
`Database.mem_rows_iff` plays: applied to a row *literal* the projections
`{fn := f, args := as, out := vs}.out` do not reduce on their own, and `obtain ⟨rfl, _⟩`
then sees `vs` occurring in its own definition. -/
theorem Database.ctor_row {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {f : FnName} {as vs : List Term} (h : Row.mk f as vs ∈ db.rows)
    (hu : db.sig.mergeOf f = MergeSpec.union) :
    vs = [.app f as] ∧ Term.app f as ∈ db.terms := hrow _ h hu

mutual

/-- `MCong.toCong` needing only that a `.union` function's rows are constructor rows. -/
theorem MCong.toCong_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {a b : Term} (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong_of_rows hrow h)
  | .trans h₁ h₂ =>
    exact .trans (MCong.toCong_of_rows hrow h₁) (MCong.toCong_of_rows hrow h₂)
  | .fd hra hrb hu hl hxy =>
    obtain ⟨rfl, hma⟩ := Database.ctor_row hrow hra hu
    obtain ⟨rfl, hmb⟩ := Database.ctor_row hrow hrb hu
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList_of_rows hrow hl)

theorem MCongList.toCongList_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {as bs : List Term} (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.toCong_of_rows hrow hab) (MCongList.toCongList_of_rows hrow hl)

end

mutual

/-- `Cong.toMCong` needing only that every application the database holds is a `.union`
function's and has its constructor row. -/
theorem Cong.toMCong_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong_of_terms hterm hunion h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong_of_terms hterm hunion h₁)
      (Cong.toMCong_of_terms hterm hunion h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs]) (hterm f as hma)
      (hterm f bs hmb) (hunion f as hma)
      (CongList.toMCongList_of_terms hterm hunion hl) (by simp)

theorem CongList.toMCongList_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {as bs : List Term} (h : CongList db as bs) : MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong_of_terms hterm hunion hab)
      (CongList.toMCongList_of_terms hterm hunion hl)

end

/-- **The congruence closure needs no `fd` disjunct.**

`MCong.fd` fires only at a `.union` function, and in a database the interpreter builds a
`.union` function's rows are exactly the constructor rows of its terms — the two
hypotheses. So `MCong` coincides with `Cong` on the row-free projection, and
`Impl/Closure.lean`'s `closure` decides it unchanged. This is what licenses
`FDatabase.closureF` reusing `closureTotal`.

`hunion` is an **added hypothesis** and the `←` direction is false without it: with
`sig g = .merge …`, terms `g x`, `g y` and an asserted `x = y`, `Cong` relates
`g x` and `g y` by `congr` while `MCong` has no rule that can — `fd` fires only at
`.union`. It says what `Impl/Merge.lean`'s comment means by "every declared function is
`.merge` or `.noMerge`": a `:merge` function's application is never itself a term,
because `Expr.eval` resolves it to its recorded output. -/
theorem FDatabase.closureF_ok {d : FDatabase}
    (hrow : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.terms)
    (hterm : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union →
      Row.mk f as [.app f as] ∈ d.rows)
    (hunion : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union)
    {a b : Term} : MCong d.toDatabase a b ↔ Cong d.toDatabase a b :=
  ⟨MCong.toCong_of_rows hrow,
    Cong.toMCong_of_terms (fun f as h => hterm f as h (hunion f as h)) hunion⟩

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
`MValidSubst.mono`, that fewer rows really do mean fewer matches. -/
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
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ e.rows := by
  unfold FDatabase.mergeOneOriented at h
  cases hm : d.sig.mergeOf r₁.fn with
  | union => rw [hm] at h; simp at h
  | noMerge => rw [hm] at h; simp at h
  | merge body res =>
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
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ e.rows := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂
  exact mergeOneOriented_confined (he ▸ h)

/-- **A merge pass removes nothing it must not.** `mergeOneWith_confined` through the two
folds. This is the formal content of "`Impl/` deletes merge rows only". -/
theorem mergeRound_confined {d : FDatabase} :
    d.toDatabase.terms ⊆ d.mergeRound.toDatabase.terms ∧
      d.toDatabase.eqs ⊆ d.mergeRound.toDatabase.eqs ∧ d.mergeRound.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ d.mergeRound.rows := by
  -- The invariant is exactly the conclusion, relative to the fixed starting database.
  let P : FDatabase → Prop := fun x =>
    d.toDatabase.terms ⊆ x.toDatabase.terms ∧ d.toDatabase.eqs ⊆ x.toDatabase.eqs ∧
      x.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) → r ∈ x.rows
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
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d := ⟨subset_rfl, subset_rfl, rfl, fun r hr _ => hr⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter d.rows d hinit

/-- **On the constructor fragment nothing is deleted, because nothing merges.** With every
function a constructor no row belongs to a `.merge` function, `hasMergeRow` is false and
the pass is the identity — which is why `Impl/Interp.lean`'s `exec` and the equality
`exec_toDatabase` are untouched by any of this. -/
theorem hasMergeRow_eq_false {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.hasMergeRow = false := by
  simp only [FDatabase.hasMergeRow, List.any_eq_false]
  intro r _
  rw [Signature.mergeOf_eq_union hsig]
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

`hpure` holds (the only block is `[]`). The row collides with itself — `MCongList` is
reflexive and `closureF` has `(k, k)` — so `mergeRound` fires, the result evaluates to
`F k`, and `addRow "f" [k] [F k]` writes the constructor row `⟨F, [k], [F k]⟩`. Then
`d.mergeRound.keyRowCount "F" = 1` while `d.keyRowCount "F" = 0`.

The theorem the difftest actually relies on is the same statement with `hpure`
strengthened to "the merge result is a term the database already holds" — under which
`addRow` adds no key class anywhere, which is the argument the docstring gives. Every
generated merge case satisfies it (results are `i64` literals). -/
theorem FDatabase.mergeRound_rowCount {d : FDatabase} (f : FnName)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
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
    (h₁ : d.sig.mergeOf r₁.fn ≠ MergeSpec.union)
    (h₂ : d.sig.mergeOf r₂.fn ≠ MergeSpec.union)
    (hargs : ∀ a ∈ r₂.args, a ∈ d.toDatabase.terms)
    (hvs : ∀ v ∈ vs, v ∈ d.toDatabase.terms) :
    ({ d with rows := (d.rows.filter fun r => r ≠ r₁).map fun r =>
        if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hu : d.sig.mergeOf r.fn = MergeSpec.union := h.ctorTerms r.fn r.args hr.2
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
    (h₁ : d.sig.mergeOf r₁.fn ≠ MergeSpec.union) :
    ({ d with rows := d.rows.filter fun r => r ≠ r₁ } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hu : d.sig.mergeOf r.fn = MergeSpec.union := h.ctorTerms r.fn r.args hr.2
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
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hm : d.mergeOneOriented cl r₁ r₂ = some e) : e.Inv := by
  unfold FDatabase.mergeOneOriented at hm
  cases hmo : d.sig.mergeOf r₁.fn with
  | union => rw [hmo] at hm; simp at hm
  | noMerge => rw [hmo] at hm; simp at hm
  | merge body res =>
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
        have hne₁ : ((eb.addTerms r₂.args).addTerms vs).sig.mergeOf r₁.fn
            ≠ MergeSpec.union := by rw [hsig₀, hmo]; simp
        have hne₂ : ((eb.addTerms r₂.args).addTerms vs).sig.mergeOf r₂.fn
            ≠ MergeSpec.union := by rw [← hfn]; exact hne₁
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
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
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
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
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
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d := ⟨h, rfl⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit.1
  · exact (houter d.rows d hinit).1

/-- The special case the task names: merge bodies are `[]`, which is `SetLegal` outright. -/
theorem Inv.mergeRound_of_pureMerges {d : FDatabase} (h : d.Inv)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
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
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Contained D)
    (hm : FDatabase.mergeOneOriented d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Contained D' := by
  have hDsig : D.sig = d.sig := MergeClosure.sig hcl
  unfold FDatabase.mergeOneOriented at hm
  cases hmo : x.sig.mergeOf r₁.fn with
  | union => rw [hmo] at hm; simp at hm
  | noMerge => rw [hmo] at hm; simp at hm
  | merge body res =>
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
          hxc.terms, fun r hr => hxc.rows (mem_dropRow hr), hxc.eqs⟩
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
          evalActions_mono
            (db := ({ x with env := mergeEnv r₂.out r₁.out } : FDatabase).toDatabase)
            (D := { D with env := mergeEnv r₂.out r₁.out })
            ⟨hxc.terms, hxc.rows, hxc.eqs⟩ (hxs.trans hDsig.symm) rfl hbodyStep
        have hebInv : eb.Inv := h₀.execActions hlx hb
        have hml : Expr.evalList eb.toDatabase.sig res eb.toDatabase.env = some vs := hv
        have hmlD : Expr.evalList D₁.sig res D₁.env = some vs := by
          rw [← hD₁env, ← hD₁sig]
          exact hml
        have hr₂D : Row.mk r₂.fn r₂.args r₂.out ∈ D.rows := hxc.rows hr₂
        have hr₁D : Row.mk r₂.fn r₁.args r₁.out ∈ D.rows := by
          rw [← hfn]; exact hxc.rows hr₁
        have hcongD : MCongList D r₂.args r₁.args :=
          (MCongList.mono (MergeClosure.contained hcl) hDsig.symm
            (CongList.toMCongList' h.ctorTerms h.rowsComplete
              ((FDatabase.congrTuple_iff h.wf).mp hck))).symm
        have hmoD : D.sig.mergeOf r₂.fn = MergeSpec.merge body res := by
          rw [← hfn, hDsig, ← hxs]; exact hmo
        refine ⟨{ D₁.addRow r₂.fn r₂.args vs with env := D.env, rules := D.rules },
          Relation.ReflTransGen.single
            (MergeStep.collide hr₂D hr₁D hcongD hmoD hD₁step hmlD), ?_⟩
        have hc₀ : ((eb.addTerms r₂.args).addTerms vs).toDatabase.Contained
            (D₁.addRow r₂.fn r₂.args vs) := by
          have h₂ := (hD₁c.addTerms_mono r₂.args).addTerms_mono vs
          simp only [FDatabase.toDatabase_addTerms]
          exact h₂.trans ⟨subset_rfl, Set.subset_insert _ _, subset_rfl⟩
        refine ⟨hc₀.terms, fun r hr => ?_, hc₀.eqs⟩
        rcases mem_mergeRows hr with hr' | rfl
        · exact hc₀.rows hr'
        · exact Set.mem_insert _ _

/-- **Either orientation stays inside the closure, so the choice between them is free.**

`mergeOneOriented_mergeStep` instantiates `MergeStep.collide` with the two rows in one
order; `collide` takes them in both, so `swapForCanon`'s answer never has to be justified
against the specification. That is what makes matching egglog's `old`/`new` an
implementation question — settled by `Impl/Merge.lean`'s `canonTerm` against the binary —
rather than a change to the semantics. -/
theorem mergeOneWith_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Contained D)
    (hm : FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeClosure D D' ∧ y.toDatabase.Contained D' := by
  obtain ⟨a, b, he⟩ := mergeOneWith_eq_oriented (cl := d.closureF) (d := x) r₁ r₂
  exact mergeOneOriented_mergeStep h hlegal hx hxs hcl hxc (he ▸ hm)

/-- **The merge pass lands inside a state the merge closure reaches.**

The pass deletes the two rows it merged, so its result is not itself a `MergeClosure`
state; the witness is a specification state that took the same collisions and kept the
originals. The fold invariant is "the accumulator is `Inv`, has the pre-pass signature,
and is contained in some state the closure has reached"; each firing extends the closure
by one `MergeStep.collide`. -/
theorem mergeRound_contained {d : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig ∧
    ∃ D, MergeClosure d.toDatabase D ∧ x.toDatabase.Contained D
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
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d :=
    ⟨h, rfl, d.toDatabase, Relation.ReflTransGen.refl, Database.Contained.refl _⟩
  unfold FDatabase.mergeRound
  split
  · exact ⟨d.toDatabase, Relation.ReflTransGen.refl, Database.Contained.refl _⟩
  · obtain ⟨-, -, D, hcl, hc⟩ := houter d.rows d hinit
    exact ⟨D, hcl, hc⟩

/-- `mergeSaturateF_contained`, with the fuel first so the induction can generalize the
database. -/
theorem mergeSaturateF_contained_aux {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    (∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) →
    d.mergeSaturateF n = some e →
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Contained db := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Contained.refl _⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Contained.refl _⟩
    · have hsigR : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
      have hlegal' : ∀ g body res, d.mergeRound.sig.mergeOf g = MergeSpec.merge body res →
          Actions.SetLegal body d.mergeRound.sig := by
        rw [hsigR]; exact hlegal
      obtain ⟨db₂, hcl₂, hcont₂⟩ := ih (h.mergeRound_of_legalMerges hlegal) hlegal' hs
      obtain ⟨db₁, hcl₁, hcont₁⟩ := mergeRound_contained h hlegal
      have hsig₁ : d.mergeRound.toDatabase.sig = db₁.sig := by
        show d.mergeRound.sig = db₁.sig
        rw [hsigR]
        exact (MergeClosure.sig hcl₁).symm
      obtain ⟨db₃, hcl₃, hcont₃, _⟩ := MergeClosure.transport hcont₁ hsig₁ hcl₂
      exact ⟨db₃, hcl₁.trans hcl₃, hcont₂.trans hcont₃⟩

/-- **The merge phase run to a fixpoint stays inside the merge closure.**

`mergeRound_contained` once per round, with `MergeClosure.transport` re-basing the tail's
closure onto the head's witness. `mergeRound_confined` is what keeps `hlegal` applicable
at the next round: a pass does not touch `sig`. -/
theorem mergeSaturateF_contained {d e : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    {n : Nat} (hs : d.mergeSaturateF n = some e) :
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Contained db :=
  mergeSaturateF_contained_aux h hlegal hs

/-- **A round's rule firings stay inside `RunRules`.**

The witness is `RunRules d.toDatabase` itself and the merge closure is the reflexive one:
`execRunRules` runs no merge phase (`Impl/Merge.lean` defers it to `execCmdM`), so
nothing has to be re-based here.

`hrules` is `execActions_evalActions`'s premise, per rule: a rule head is an action block
like any other, and without legality `Inv` does not survive it. It is `Rule.SetLegal` at
`d.sig`, which is what `Program.SetLegal` gives for every rule a program installs.

The enumerator's substitution is transported to the specification's by
`evalActions_envAgree`: `matchQuery_MValidQuerySubst` only produces one that
`Env.Agree`s, and `Database.EnvAgree.eq_of_env_rules` turns that back into equality once
`fireInto` restores the caller's environment. -/
theorem execRunRules_contained {d : FDatabase} (h : d.Inv)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) :
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
        obtain ⟨τ, hτ, hag⟩ := matchQuery_MValidQuerySubst h hσ
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
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hs : d.execCmdM (.action a) = some e) :
    ∃ d₁ db, evalAction d.toDatabase a = some d₁ ∧ MergeClosure d₁ db ∧
      e.toDatabase.Contained db := by
  rw [FDatabase.execCmdM] at hs
  obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
  have hsig₁ : d₁.sig = d.sig := execAction_sig hd₁
  have hlegal₁ : ∀ g body res, d₁.sig.mergeOf g = MergeSpec.merge body res →
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
and `ProgramStep.mono` are that, and they are `MValidQuerySubst.mono` (a larger state
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
`MValidQuerySubst.mono` finds the same match and `evalActions_mono` re-runs the
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
    ⟨σ, MValidQuerySubst.mono hc hsig henv.symm hq,
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

/-! #### Declaring a fresh name

The three facts a `.decl` needs, all of them about `Signature.mergeOf` sending an
undeclared name to `.union`. -/

/-- `Signature.mergeOf` is read pointwise, so a declaration at `f` is invisible at every
other name. -/
theorem Signature.mergeOf_update_of_ne {sig : Signature} {f g : FnName} {dc : FnDecl}
    (h : g ≠ f) :
    Signature.mergeOf (Function.update sig f (some dc)) g = Signature.mergeOf sig g := by
  unfold Signature.mergeOf
  rw [Function.update_of_ne h]

/-- An undeclared name is a constructor. -/
theorem Signature.mergeOf_eq_union_of_none {sig : Signature} {f : FnName}
    (h : sig f = none) : Signature.mergeOf sig f = MergeSpec.union := by
  unfold Signature.mergeOf
  rw [h]

/-- Declaring a name the signature does not yet mention can only make a `set` *more*
legal: `Action.SetLegal` forbids exactly one value of `mergeOf`, `.union`, and that is
the value an undeclared name already has — so no legal `set` names `f`. -/
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
      exact h (Signature.mergeOf_eq_union_of_none hf)
    show Signature.mergeOf (Function.update sig f (some dc)) g ≠ MergeSpec.union
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

/-- Anything true of `d` and preserved by one `mergeOneWith` firing is true after a whole
pass. The two folds of `mergeRound`, factored out. -/
theorem mergeRound_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
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
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter d.rows d hinit

/-- A firing restores the caller's environment and rule list. -/
theorem mergeOneOriented_envRules {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (h : d.mergeOneOriented cl r₁ r₂ = some e) :
    e.env = d.env ∧ e.rules = d.rules := by
  unfold FDatabase.mergeOneOriented at h
  cases hmo : d.sig.mergeOf r₁.fn with
  | union => rw [hmo] at h; simp at h
  | noMerge => rw [hmo] at h; simp at h
  | merge body res =>
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
    (∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
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
    · show d.sig.mergeOf f = MergeSpec.union
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
    · have hu' : e.sig.mergeOf r.fn = MergeSpec.union := by rw [hsig]; exact hu
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
`ctorRows`, since an undeclared name is already a constructor and every row of one is
already a constructor row. -/
theorem Inv.decl {d : FDatabase} (h : d.Inv) {f : FnName} {dc : FnDecl}
    (hf : d.sig f = none) (hterms : ∀ as, Term.app f as ∉ d.terms) :
    ({ d with sig := Function.update d.sig f (some dc) } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := by
    intro g as hm
    have hg : g ≠ f := by rintro rfl; exact hterms as hm
    show Signature.mergeOf (Function.update d.sig f (some dc)) g = MergeSpec.union
    rw [Signature.mergeOf_update_of_ne hg]
    exact h.ctorTerms g as hm
  rowsComplete := h.rowsComplete
  rowsWF := h.rowsWF
  ctorRows := by
    intro r hr hu
    refine h.ctorRows r hr ?_
    show Signature.mergeOf d.sig r.fn = MergeSpec.union
    by_cases hfn : r.fn = f
    · rw [hfn]
      exact Signature.mergeOf_eq_union_of_none hf
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
  ∀ g body res, Signature.mergeOf sig g = MergeSpec.merge body res →
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
    · exact hlegal
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
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db ∧
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
      ⟨subset_rfl, subset_rfl, subset_rfl⟩, rfl, rfl, ?_⟩
    show ({r' | r' ∈ r :: d.rules} : Set Rule) = insert r {r' | r' ∈ d.rules}
    ext r'
    simp
  | run =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨R, hRstep, hRcont⟩ := execRunRules_contained h hrules
    have hRsig : R.sig = d.sig := MergeClosure.sig hRstep
    have hRenv : R.env = d.env := (MergeClosure.envRules hRstep).1
    have hRrules : R.rules = d.toDatabase.rules := (MergeClosure.envRules hRstep).2
    have hmerges₁ : Signature.MergesLegal (execRunRules d).sig := by
      rw [execRunRules_fields.1]; exact hmerges
    obtain ⟨db₂, hcl₂, hcont₂⟩ :=
      mergeSaturateF_contained (h.execRunRules hrules) hmerges₁ hs
    obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
      MergeClosure.transport hRcont (by rw [hRsig]; exact execRunRules_fields.1) hcl₂
    refine ⟨db₃, .run (hRstep.trans hcl₃), hcont₂.trans hcont₃, ?_, ?_, ?_⟩
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
    exact ⟨{ d.toDatabase with sig := Function.update d.toDatabase.sig f (some dc) },
      .decl, ⟨subset_rfl, subset_rfl, subset_rfl⟩, rfl, rfl, rfl⟩

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
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db := by
  obtain ⟨db, hstep, hcont, -, -, -⟩ := execCmdM_contained' h hlegal hmerges hrules hs
  exact ⟨db, hstep, hcont⟩

theorem execProgramM_contained_aux {p : Program} : ∀ {d d' : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig →
    (∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) →
    d.ProgramLegal p → d.execProgramM p = some d' →
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db := by
  induction p with
  | nil =>
    intro d d' _ _ _ _ hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact ⟨d.toDatabase, .nil, hs ▸ Database.Contained.refl _⟩
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
    obtain ⟨db₃, hstep₃, hcont₃, -, -, -⟩ :=
      ProgramStep.mono hcont₁ hsig₁ henv₁ hrules₁ hstep₂
    exact ⟨db₃, .cons hstep₁ hstep₃, hcont₂.trans hcont₃⟩

/-- **The interpreter's answer to a whole program is contained in one the specification
reaches.**

`execCmdM_contained'` per command, with `ProgramStep.mono` re-basing the tail's witness
onto the head's — which is where `MValidSubst.mono` is spent, read forwards: a larger
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
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db :=
  execProgramM_contained_aux h hmerges hrules hp hs

end FDatabase

/-- **The contract for `execM`.** `execProgramM_contained` from `FDatabase.empty`, whose
two global side conditions discharge themselves: the empty signature declares no merge
body and the empty state has no rules. `hp` is what remains, and `FDatabase.ProgramLegal`
is stated so that a front end which declares before use and type-checks its merge bodies
satisfies it.

See the section header above for why the contract is containment rather than the equality
`exec_toDatabase` enjoys. -/
theorem execM_contained {p : Program} (hp : FDatabase.empty.ProgramLegal p)
    {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Contained db :=
  FDatabase.execProgramM_contained FDatabase.Inv.empty
    (fun g body res hg => by
      rw [Signature.mergeOf_eq_union_of_none
        (show FDatabase.empty.sig g = none from rfl)] at hg
      exact MergeSpec.noConfusion hg)
    (fun r hr => absurd hr (by simp [FDatabase.empty])) hp h

end Egglog
