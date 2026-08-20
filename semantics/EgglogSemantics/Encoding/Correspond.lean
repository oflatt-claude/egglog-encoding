import EgglogSemantics.Encoding.Encode
import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Merge

/-!
# The encoding correspondence: the claim, the decision procedure, and what they cost

`Encoding/Encode.lean` reads the target with `ViewRepr` and `SameClass`. `DiffTest.lean`
sweeps every pair of terms of every in-domain case for

```
Cong src a b  ↔  SameClass tgt a b
```

and reports agreement. This file is what makes those two the *same* claim: `sameClassF`
decides `SameClass` over an `FDatabase`, `sameClassF_iff` proves it, and `mem_closureF_iff`
(`Proofs/Interp.lean`) already does the source side. Without the two of them the sweep is
evidence about a different predicate than the theorem mentions.

## The two hypotheses the decision procedure needs

`sameClassF` reads the view tables the way `difftest` does, and that reading is exact only
under two conditions on the target — one per direction of the iff.

* **`SubtermClosed`**, for `sameClassF → SameClass`. `Database.Out` asks that the key
  columns be terms the database holds, which is subterm closure at the entry term. It is
  `Database.WF`'s own clause, and decidable, so a self-test can report it at the state it
  swept.
* **`EqsRefl`**, for `SameClass → sameClassF`. `Database.Out` reads the key up to
  congruence and the procedure reads it up to equality; the two agree exactly where the
  target asserts no equation but a reflexive one. `encode` emits no `union` — a source
  `union` becomes a `set` of a `@UF` edge — so its targets satisfy it, and
  `difftest correspond`'s `tgt-eqs` column is that measurement, 0 on every case.

Neither is an artefact: both are properties of the state the encoded program runs to, and
both are decided at the witness at the end of this file.

## What is proved, and what is not

* **Proved**, no `sorry`: `sameClassF_iff` and `mem_viewReprsF_iff`, both directions;
  `cong_sameClass`, which reduces the forward half to three obligations with `symm`
  discharged; `witnessProgram_encodeDomain` and `encode_corresponds_witness`.
* **Proved, and what says the specification's own target is reachable**:
  `not_mergeConflict_self`, `refutationState_mergeSaturated`, and
  `satProgram_programStep` — a compiled `ProgramStep Database.empty (encode P) tgt` for a
  `P` that builds a term. Each of the three is the negation of a lemma that stood here
  before `Spec/Step.lean` read `identityVals`, and that refutation is why the statement
  below reads `execM`; the reason it still does is a different one.
* **`sorry`**, one per obligation and the only four in the library: `encode_assert`,
  `encode_trans`, `encode_congr`, `encode_corresponds_complete`. `encode_corresponds` and
  `encode_corresponds_forward` are assembled from them and carry `sorryAx` through them.
-/

namespace Egglog

/-! ### Where `Cong` is the identity

The encoded program asserts no equation but the reflexive one `addTerm` records, so its
`Cong` is the identity on the terms it holds. That is what lets a *computed* reading of
`Database.Out` — which searches the key's congruence class — read the key up to equality. -/

/-- Every equation the database asserts is reflexive. -/
def Database.EqsRefl (d : Database) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

/-- **Where every asserted equation is reflexive, `Cong` is the identity.** By `Cong.le` at
`R := Eq`: the three closure rules are `Eq`'s own, and `congr`'s premise is `Forall₂ Eq`. -/
theorem Cong.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {a b : Term} (h : Cong d a b) :
    a = b := by
  refine Cong.le (R := fun x y => x = y) (fun x y hm => hr (x, y) hm) (fun _ _ h => h.symm)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun f as bs _ _ hl => ?_) h
  rw [show as = bs from (List.forall₂_eq_eq_eq ▸ hl : as = bs)]

/-- The list form. -/
theorem CongList.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {as bs : List Term}
    (h : CongList d as bs) : as = bs :=
  List.forall₂_eq_eq_eq ▸ (h.toForall₂.imp fun _ _ hab => Cong.eq_of_eqsRefl hr hab)

/-- `Database.EqsRefl`, over the interpreter's equation list. `toDatabase` keeps `d.eqs` and
the diagonal of `d.terms`, so this is the whole condition. -/
def FDatabase.EqsRefl (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

/-- Decided, so that a self-test can report it. -/
def FDatabase.eqsReflB (d : FDatabase) : Bool := d.eqs.all fun p => p.1 == p.2

theorem FDatabase.eqsReflB_iff (d : FDatabase) : d.eqsReflB = true ↔ d.EqsRefl := by
  simp [FDatabase.eqsReflB, FDatabase.EqsRefl, List.all_eq_true]

theorem FDatabase.EqsRefl.toDatabase {d : FDatabase} (h : d.EqsRefl) :
    d.toDatabase.EqsRefl := by
  intro p hp
  rcases FDatabase.mem_toDatabase_eqs.mp hp with ⟨he, -⟩ | ⟨hp', -, -⟩
  · exact he
  · exact h p hp'

/-- The interpreter's term list is closed under subterms. This is the only part of
`Database.WF` the reading below needs, and unlike `WF` it is decidable, so a self-test can
report it at the state it swept. -/
def FDatabase.SubtermClosed (d : FDatabase) : Prop :=
  ∀ t ∈ d.terms, ∀ s ∈ t.subtermList, s ∈ d.terms

/-- Decided. -/
def FDatabase.subtermClosedB (d : FDatabase) : Bool :=
  d.terms.all fun t => t.subtermList.all fun s => d.terms.contains s

theorem FDatabase.subtermClosedB_iff (d : FDatabase) :
    d.subtermClosedB = true ↔ d.SubtermClosed := by
  simp [FDatabase.subtermClosedB, FDatabase.SubtermClosed, List.all_eq_true]

/-- `Database.WF`'s own clause, read back onto the list. -/
theorem FDatabase.SubtermClosed.of_wf {d : FDatabase} (hw : d.toDatabase.WF) :
    d.SubtermClosed := by
  intro t ht s hs
  have ht' : t ∈ d.toDatabase.terms := by rw [FDatabase.toDatabase_terms]; exact ht
  have hs' : s ∈ d.toDatabase.terms := hw.subtermClosed t ht' ((Term.mem_subtermList t).mp hs)
  rwa [FDatabase.toDatabase_terms] at hs'

/-! ### Reading the target, computed

`ViewRepr` as a function from a source term to the list of ids the target gives it: one view
read per subterm, joined on ids. An application's ids are the e-class columns of every view
entry of its head whose key columns are, pointwise, ids of its children.

This is `DiffTest.lean`'s `viewReprs` with the table reading inlined — entries read out of
`terms`, which is what `Database.Out` says, and the key/value split taken from the source
term's own arity rather than from the program's constructor list. -/

/-- Pointwise membership: `ks` picks, per column, one of the ids that column's child was
given. `false` at unequal lengths, which is what makes a view entry of the wrong width no
entry at all. -/
def memAll : List (List Term) → List Term → Bool
  | [], [] => true
  | r :: rs, k :: ks => decide (k ∈ r) && memAll rs ks
  | _, _ => false

/-- The id a view entry gives the source application `f a…`, or `none` where the entry is
not one: the head has to be `f`'s view, the width has to be the key plus the two value
columns, and the key columns have to be ids of the children, which `rs` carries. -/
def viewIdOf (rs : List (List Term)) (f : FnName) (n : Nat) : Term → Option Term
  | .app g cs =>
      if g = viewName f ∧ cs.length = n + 2 ∧ memAll rs (cs.take n) = true then
        (cs.drop n).head?
      else none
  | .lit _ => none

/-- **What a reading found**: the entry term, split into its columns. Both directions of the
link read the table through this. -/
theorem viewIdOf_eq_some {rs : List (List Term)} {f : FnName} {n : Nat} {t e : Term} :
    viewIdOf rs f n t = some e ↔
      ∃ ks pf, t = .app (viewName f) (ks ++ [e, pf]) ∧ ks.length = n ∧
        memAll rs ks = true := by
  match t with
  | .lit l => simp [viewIdOf]
  | .app g cs =>
    simp only [viewIdOf]
    constructor
    · intro h
      split at h
      · rename_i hcond
        obtain ⟨rfl, hlen, hall⟩ := hcond
        have hdlen : (cs.drop n).length = 2 := by rw [List.length_drop, hlen]; omega
        obtain ⟨e', pf, hd⟩ := List.length_eq_two.mp hdlen
        rw [hd] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        refine ⟨cs.take n, pf, ?_, ?_, hall⟩
        · rw [← hd, List.take_append_drop]
        · rw [List.length_take, hlen]; omega
      · exact absurd h (by simp)
    · rintro ⟨ks, pf, hteq, hklen, hall⟩
      simp only [Term.app.injEq] at hteq
      obtain ⟨rfl, rfl⟩ := hteq
      rw [List.take_left' hklen, List.drop_left' hklen,
        if_pos ⟨rfl, by simp [hklen], hall⟩]
      rfl

mutual

/-- The ids the target gives a source term: `ViewRepr d.toDatabase t`, computed.

A literal is its own id where the target holds it and has none where it does not:
`encodeBuild` emits no action for a literal, so a literal never keys a view entry. -/
def viewReprsF (d : FDatabase) : Term → List Term
  | .lit l => if (Term.lit l) ∈ d.terms then [Term.lit l] else []
  | .app f as => d.terms.filterMap (viewIdOf (viewReprsListF d as) f as.length)

/-- `viewReprsF` over an argument list, one id list per column. -/
def viewReprsListF (d : FDatabase) : List Term → List (List Term)
  | [] => []
  | t :: ts => viewReprsF d t :: viewReprsListF d ts

end

/-- `SameClass d.toDatabase`, computed: one id the target gives both terms. -/
def sameClassF (d : FDatabase) (a b : Term) : Bool :=
  (viewReprsF d a).any fun e => decide (e ∈ viewReprsF d b)

/-! ### The link, computed to stated

`SubtermClosed` is what this direction spends: `Database.Out` asks that the key columns be
terms the database holds, and they are subterms of the entry term the reading found. -/

mutual

theorem viewRepr_of_mem_viewReprsF {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (t e : Term), e ∈ viewReprsF d t → ViewRepr d.toDatabase t e
  | .lit l, e, h => by
    simp only [viewReprsF] at h
    split at h
    · rename_i hm
      rw [List.mem_singleton] at h
      subst h
      exact .lit (by rw [FDatabase.toDatabase_terms]; exact hm)
    · exact absurd h (by simp)
  | .app f as, e, h => by
    simp only [viewReprsF, List.mem_filterMap] at h
    obtain ⟨t, ht, hid⟩ := h
    obtain ⟨ks, pf, rfl, hklen, hall⟩ := viewIdOf_eq_some.mp hid
    have hmem : Term.app (viewName f) (ks ++ [e, pf]) ∈ d.toDatabase.terms := by
      rw [FDatabase.toDatabase_terms]; exact ht
    refine .app (viewReprList_of_memAll hsc as ks hall) (Database.out_self hmem ?_)
    intro x hx
    rw [FDatabase.toDatabase_terms]
    exact hsc _ ht x ((Term.mem_subtermList _).mpr
      (Term.IsSubterm.arg (List.mem_append_left _ hx) (.refl x)))

theorem viewReprList_of_memAll {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (as ks : List Term), memAll (viewReprsListF d as) ks = true →
      ViewReprList d.toDatabase as ks
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h (by simp [viewReprsListF, memAll])
  | _ :: _, [], h => absurd h (by simp [viewReprsListF, memAll])
  | a :: as, k :: ks, h => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons (viewRepr_of_mem_viewReprsF hsc a k h.1) (viewReprList_of_memAll hsc as ks h.2)

end

/-! ### The link, stated to computed

`EqsRefl` is what this direction spends, and it is spent in exactly one place: `Out`'s
`CongList` premise reads the key up to congruence, and the reading found the entry keyed by
the ids themselves. -/

/-- `ViewReprList` reads one id per column. -/
theorem ViewReprList.length_eq {d : Database} : ∀ {as es : List Term},
    ViewReprList d as es → es.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ hl => by simp [ViewReprList.length_eq hl]

mutual

theorem mem_viewReprsF_of_viewRepr {d : FDatabase} (hr : d.EqsRefl) {t e : Term}
    (h : ViewRepr d.toDatabase t e) : e ∈ viewReprsF d t := by
  match h with
  | .lit hm =>
    rw [FDatabase.toDatabase_terms] at hm
    have hm' : (Term.lit _) ∈ d.terms := hm
    simp only [viewReprsF, if_pos hm', List.mem_singleton]
  | @ViewRepr.app _ f as es e pf hl ho =>
    obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : es = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    rw [FDatabase.toDatabase_terms] at hmem
    simp only [viewReprsF, List.mem_filterMap]
    exact ⟨_, hmem, viewIdOf_eq_some.mpr
      ⟨es, pf, rfl, hl.length_eq, memAll_of_viewReprList hr as es hl⟩⟩

theorem memAll_of_viewReprList {d : FDatabase} (hr : d.EqsRefl) :
    ∀ (as es : List Term), ViewReprList d.toDatabase as es →
      memAll (viewReprsListF d as) es = true
  | _, _, .nil => by simp [viewReprsListF, memAll]
  | a :: as, e :: es, .cons hab hl => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨mem_viewReprsF_of_viewRepr hr hab, memAll_of_viewReprList hr as es hl⟩

end

/-! ### The two links, joined

`sameClassF_iff` is the theorem the corpus result needs: what `difftest correspond` computes
on the target is what `Encode.lean`'s `SameClass` says about it. -/

/-- **`viewReprsF` decides `ViewRepr`.** -/
theorem mem_viewReprsF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (t e : Term) : e ∈ viewReprsF d t ↔ ViewRepr d.toDatabase t e :=
  ⟨viewRepr_of_mem_viewReprsF hsc t e, mem_viewReprsF_of_viewRepr hr⟩

/-- **`sameClassF` decides `SameClass`.** -/
theorem sameClassF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (a b : Term) :
    sameClassF d a b = true ↔ SameClass d.toDatabase a b := by
  simp only [sameClassF, List.any_eq_true, decide_eq_true_eq, SameClass]
  constructor
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mp hea, (mem_viewReprsF_iff hsc hr b e).mp heb⟩
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mpr hea, (mem_viewReprsF_iff hsc hr b e).mpr heb⟩

/-! ### The proof column and `MergeSaturated`

`ENCODING.md`'s finding 1 was that no state `encode` ran to satisfied `Rebuilt`, and
`Cmd.saturate rebuildRuleset` was the repair. The proof column (`@UF(t) ↦ (p, pf)`) landed
after it and reopened the hole one level down, and this section is what closed it again.

The mechanism was `Spec/Step.lean`'s own reading of a collision. **Every entry collides with
itself**, and the shared `:merge` body writes, for the colliding pair, the edge

```
@UF (ordering-max old0 new0) ↦ (ordering-min old0 new0, @Trans (@Sym hi_pf) lo_pf)
```

At a self-collision `old0 = new0` and `old1 = new1 = pf`, so the body wrote the self-loop
`@UF(v) ↦ (v, @Trans (@Sym pf) pf)`: a **new term**, one composition larger than the proof it
started from. `MergeSaturated` therefore forced the whole tower into the state, no state with
finitely many terms holds it, and `ProgramStep Database.empty (encode P) tgt` was
unsatisfiable for every `P` that built a term.

`identityVals := some 1` is what kept the *implementation* out of it: the proof column sits
outside the change test, so a collision that moves only the proof resolves to the resident
row. `Spec/Step.lean` reads `identityVals` too now — `MergeConflict`, which is
`Impl/Merge.lean`'s `noConflict` negated — so a self-collision at either encoded table is no
longer a step at all, and the tower is what is unreachable. `satProgram_programStep` below is
the satisfiability that replaced the refutation. -/

/-- **An entry does not conflict with itself**, so no `MergeStep` fires at a self-collision
of a `:merge` with a block: with `:internal-identity-vals k` the two tuples agree on every
counted column because they *are* the same tuple, and without it the only arm left is the
empty body. -/
theorem not_mergeConflict_self {decl : FnDecl} {body : List Action} (hb : body ≠ [])
    (a : List Term) : ¬ MergeConflict decl body a a := by
  unfold MergeConflict
  cases decl.identityVals <;> simp [hb]

/-- The body both encoded `:merge`s run is one `set`, so it never takes `MergeConflict`'s
empty-body arm. -/
theorem mergeBody_ne_nil : mergeBody ≠ [] := by simp [mergeBody]

/-! #### Satisfaction, instantiated

A refutation whose hypotheses nothing satisfies is worth as little as a theorem whose
hypotheses nothing satisfies, and the burden has changed sides: what needs a witness now is
that a state holding a `@UF` self-loop **is** merge-saturated. Here is the state the old
refutation was instantiated at — the encoding's own declarations, one `@UF` self-loop, and
nothing else. No run is needed to build it and none is run to check it. -/

/-- A term to hang the state on. -/
private def refA : Term := .app "A" []

/-- The state: `@UF`, `@Sym` and `@Trans` declared as the prelude declares them, and the
single entry `@UF(A) ↦ (A, @Fiat)`. -/
def refutationState : FDatabase where
  sig := fun n =>
    if n = ufName then some ufDecl
    else if n = symName then some (proofDecl 1)
    else if n = transName then some (proofDecl 2)
    else none
  terms := [refA, .app fiatName [], .app ufName [refA, refA, .app fiatName []]]
  rows := []
  eqs := []
  env := []
  rules := []

/-- The one `@UF` entry pins both value tuples of any collision at it, so every collision
there is a collision of that entry with itself. -/
private theorem refutationState_pin {cs vals : List Term} (hl : cs.length = 1)
    (hmem : Term.app ufName (cs ++ vals) ∈ refutationState.toDatabase.terms) :
    vals = [refA, .app fiatName []] := by
  rw [FDatabase.mem_toDatabase_terms] at hmem
  match cs with
  | [] => simp at hl
  | [x] =>
    suffices h : x = refA ∧ vals = [refA, .app fiatName []] from h.2
    simpa [refutationState, refA, ufName, fiatName] using hmem
  | _ :: _ :: _ => simp at hl

/-- **And the state is `MergeSaturated`.** `@UF` is the one `:merge` its signature declares,
its one entry collides with nothing but itself, and `identityVals := some 1` makes that
collision no conflict. -/
theorem refutationState_mergeSaturated : MergeSaturated refutationState.toDatabase := by
  intro db' h
  cases h with
  | @collide _ f decl as bs a b vs body res hsig hm hconf hla hlb hma hmb _ _ _ =>
    replace hsig : (if f = ufName then some ufDecl
        else if f = symName then some (proofDecl 1)
        else if f = transName then some (proofDecl 2) else none) = some decl := hsig
    obtain ⟨rfl, rfl⟩ : f = ufName ∧ decl = ufDecl := by
      split_ifs at hsig <;>
        obtain rfl := Option.some.inj hsig
        <;> first
          | exact ⟨by assumption, rfl⟩
          | simp [proofDecl] at hm
    obtain ⟨rfl, rfl⟩ : body = mergeBody ∧ res = mergeResult := by
      simpa [ufDecl] using hm.symm
    have hab : a = b := (refutationState_pin (by simpa [ufDecl] using hla) hma).trans
      (refutationState_pin (by simpa [ufDecl] using hlb) hmb).symm
    rw [hab] at hconf
    exact (not_mergeConflict_self mergeBody_ne_nil b hconf).elim

/-! ### The statement is satisfiable

`ProgramStep Database.empty (encode P) tgt` is what the correspondence would like to carry,
and the refutation above used to say that nothing satisfies it. Here is a `P` that builds a
term and the state its encoding runs to — compiled, with the two fixpoint conditions
`Cmd.saturate` demands discharged rather than assumed.

`not_mergeSaturated_of_entry`, the deleted lemma, said that **one view entry is enough** to
break saturation, so the smallest program with a view table is exactly where the defect bit;
that is what this witness is chosen to be. Nothing here executes a program: the twelve
commands are stepped one at a time, each `CmdStep` a `cmdEffect` and a reflexive merge phase,
and the trailing `Cmd.saturate` is discharged by `satTarget_runRules` and
`satTarget_mergeSaturated`. -/

/-- One nullary constructor, declared, and one action that builds it: the smallest source
program that builds a term. -/
def satProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.app "A" []))]

/-- The signature `encode satProgram`'s prelude installs, in the order it declares them: the
three fixed proof heads, `@UF`, and `A`'s table triple. `congrArities` is empty at a nullary
constructor and `Program.srcRules` is empty at a program with no rule, so neither
arity-indexed family contributes. -/
def satSig : Signature :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update Database.empty.sig
      fiatName (some (proofDecl 0))) symName (some (proofDecl 1)))
      transName (some (proofDecl 2))) ufName (some ufDecl))
      "A" (some (skolemDecl 0))) (viewName "A") (some (viewDecl 0)))
      (termName "A") (some (termDecl 0))

/-- **The two `:merge` functions the prelude declares with a body are `@UF` and `@AView`.**
`@ATerm` is `:no-merge` and everything else is a constructor, so those are the only two a
`MergeStep` can fire at. -/
private theorem satSig_merge {f : FnName} {decl : FnDecl} {body : List Action} {res : List Expr}
    (hsig : satSig f = some decl) (hm : decl.merge = some (.merge body res)) :
    (f = ufName ∧ decl = ufDecl) ∨ (f = viewName "A" ∧ decl = viewDecl 0) := by
  simp only [satSig, Function.update_apply, Database.empty] at hsig
  split_ifs at hsig <;>
    obtain rfl := Option.some.inj hsig
    <;> first
      | exact Or.inl ⟨by assumption, rfl⟩
      | exact Or.inr ⟨by assumption, rfl⟩
      | simp [proofDecl, skolemDecl, termDecl] at hm

/-- `A`'s one rebuild rule: the e-class column of `@AView() ↦ (@e, @p)` follows `@e`'s
union-find edge. A nullary constructor has no child column, so `rebuildRules` emits no
other. -/
def satRebuildRule : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName "A") [],
              .values [.var "@x", .var "@q"] ufName [.var "@e"]],
    actions := [.set (viewName "A") [] [.var "@x", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

/-- After the prelude: the seven declarations and the two maintenance rules. -/
def satPrelude : Database :=
  { Database.empty with
    sig := satSig,
    rules := insert satRebuildRule (insert pathCompressRule Database.empty.rules) }

/-- `@ATerm(A)`, the term-relation row `(A)`'s build writes. -/
def satTermEntry : Term := .app (termName "A") [.app "A" []]

/-- `@AView() ↦ (A, @Fiat)`, the view row `(A)`'s build writes. -/
def satViewEntry : Term := .app (viewName "A") [.app "A" [], .app fiatName []]

/-- **The state `encode satProgram` runs to.** Definitionally the chain of `cmdEffect`s, so
every `CmdStep` in `satProgram_programStep` is `rfl`. -/
def satTarget : Database := (satPrelude.addTerm satTermEntry).addTerm satViewEntry

theorem satTarget_sig : satTarget.sig = satSig := rfl

theorem satTarget_rules :
    satTarget.rules = insert satRebuildRule (insert pathCompressRule Database.empty.rules) :=
  rfl

/-- The prelude asserts no equation, so it holds no term. -/
theorem satPrelude_terms : satPrelude.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [satPrelude, Database.empty] at hu

/-- The four terms the run holds: the two entries and their arguments. -/
theorem satTarget_terms :
    satTarget.terms = satTermEntry.subterms ∪ satViewEntry.subterms := by
  simp [satTarget, satPrelude_terms]

/-- Only `Database.addTerm` ever writes here, so the state is diagonal — which is what makes
a query read the key up to *equality*. -/
theorem satTarget_diag : satTarget.Diag := by
  have h : satPrelude.Diag := fun p hp => absurd hp (by simp [satPrelude, Database.empty])
  exact (h.addTerm _).addTerm _

/-- **The state holds no `@UF` entry.** `satProgram` has no `union`, so nothing writes one:
the four terms are `@ATerm(A)`, `@AView(A, @Fiat)`, `(A)` and `(@Fiat)`. -/
theorem satTarget_no_uf (ts : List Term) : Term.app ufName ts ∉ satTarget.terms := by
  rw [satTarget_terms]
  simp [satTermEntry, satViewEntry, ufName, termName, viewName, fiatName]

/-- The view entry is there, so the correspondence has something to read: the run does its
job rather than stopping short. -/
theorem satTarget_mem_view : satViewEntry ∈ satTarget.terms := by
  rw [satTarget_terms]; exact Or.inr (Term.self_mem_subterms _)

/-- The one `@AView` entry pins both value tuples, as `refutationState_pin` does for `@UF`. -/
private theorem satTarget_pin {vals : List Term}
    (hmem : Term.app (viewName "A") ([] ++ vals) ∈ satTarget.terms) :
    vals = [.app "A" [], .app fiatName []] := by
  rw [satTarget_terms] at hmem
  simpa [satTermEntry, satViewEntry, viewName, termName, fiatName] using hmem

/-- **The state is merge-saturated.** `satSig_merge` leaves two functions to check: `@UF`,
which has no entry at all, and `@AView`, which has exactly one — so its only collision is
with itself, and `identityVals := some 1` makes that no conflict. -/
theorem satTarget_mergeSaturated : MergeSaturated satTarget := by
  intro db' h
  cases h with
  | @collide _ f decl as bs a b vs body res hsig hm hconf hla hlb hma hmb _ _ _ =>
    rcases satSig_merge (satTarget_sig ▸ hsig) hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hma (satTarget_no_uf _)
    · obtain ⟨rfl, rfl⟩ : body = mergeBody ∧ res = mergeResult := by
        simpa [viewDecl] using hm.symm
      obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (by simpa [viewDecl] using hla)
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by simpa [viewDecl] using hlb)
      have hab : a = b := (satTarget_pin hma).trans (satTarget_pin hmb).symm
      rw [hab] at hconf
      exact (not_mergeConflict_self mergeBody_ne_nil b hconf).elim

/-- **No `@UF` read matches.** A `Pattern.values` match needs the entry term itself: the
witness has to be a term the state already holds, and on a diagonal state `withOperands`
cannot supply one. -/
theorem satTarget_not_matches_uf {vs as : List Expr} {σ : Env} :
    ¬ Matches satTarget (.values vs ufName as) σ := by
  intro h
  cases h with
  | values hw _ _ hcong =>
    exact absurd (congOn_eq_of_diag satTarget_diag hcong ▸ hw) (satTarget_no_uf _)

/-- A query with a `@UF` read in it admits no substitution here. -/
private theorem satTarget_not_forall₂ : ∀ {q : Query} {σs : List Env},
    List.Forall₂ (ValidSubst satTarget) q σs →
    ∀ {vs as : List Expr}, Pattern.values vs ufName as ∈ q → False
  | _, _, .nil, _, _, h => absurd h (by simp)
  | _ :: _, _, .cons hp hrest, _, _, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact satTarget_not_matches_uf hp.2
    · exact satTarget_not_forall₂ hrest h'

/-- **The rebuild ruleset has reached its fixpoint**, which is `RunSaturated`'s first
conjunct. Both maintenance rules read `@UF` and there is no `@UF` entry to read. -/
theorem satTarget_runRules : RunRules rebuildRuleset satTarget = satTarget := by
  have hS : {d | ∃ r ∈ satTarget.rules, r.ruleset = rebuildRuleset ∧
      d ∈ RuleResults satTarget r} = (∅ : Set Database) := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro d ⟨r, hr, -, σ, ⟨σs, hall, -⟩, -⟩
    rw [satTarget_rules] at hr
    have hr' : r = satRebuildRule ∨ r = pathCompressRule := by
      simpa [Database.empty] using hr
    rcases hr' with rfl | rfl
    · exact satTarget_not_forall₂ hall (vs := [.var "@x", .var "@q"]) (as := [.var "@e"])
        (by simp [satRebuildRule])
    · exact satTarget_not_forall₂ hall (vs := [.var "@b", .var "@p"]) (as := [.var "@a"])
        (by simp [pathCompressRule])
  unfold RunRules
  rw [hS]
  exact Database.ext rfl (by simp) rfl rfl

/-- **The trailing `Cmd.saturate rebuildRuleset` steps from this state to itself**: no round
of `@rebuild` adds anything and no collision changes anything, so the fixpoint is reached in
zero rounds and the merge phase after it is reflexive. -/
theorem satTarget_cmdStep_saturate :
    CmdStep satTarget (.saturate rebuildRuleset) satTarget :=
  ⟨satTarget, ⟨.refl, satTarget_runRules, satTarget_mergeSaturated⟩, .refl⟩

/-- **The twelve commands `encode satProgram` emits**, written out: the three fixed proof
heads, `@UF`, `A`'s table triple, the two maintenance rules, the two `set`s the build of
`(A)` becomes, and the rebuild. Naming them is what keeps `satProgram_programStep` cheap —
stepping through `encode satProgram` itself re-reduces the encoder once per command. -/
def satEncoded : Program :=
  [.decl fiatName (proofDecl 0), .decl symName (proofDecl 1), .decl transName (proofDecl 2),
   .decl ufName ufDecl, .decl "A" (skolemDecl 0), .decl (viewName "A") (viewDecl 0),
   .decl (termName "A") (termDecl 0),
   .rule pathCompressRule, .rule satRebuildRule,
   .action (.set (termName "A") [.app "A" []] []),
   .action (.set (viewName "A") [] [.app "A" [], fiatE]),
   .saturate rebuildRuleset]

theorem satEncoded_eq : encode satProgram = satEncoded := rfl

set_option maxHeartbeats 2000000 in
-- Twelve `cmdEffect` reductions at a state that grows by a `Function.update` or an
-- `addTerm` each time, and the two `set`s decide `Signature.IsCtor` through the whole
-- declaration chain; the default budget is short.
/-- **`ProgramStep Database.empty (encode P) tgt` is satisfiable at a `P` that builds a
term.** Each of the first eleven commands is a `cmdEffect` followed by a reflexive merge
phase; the twelfth is `satTarget_cmdStep_saturate`. -/
theorem satProgram_programStep :
    ProgramStep Database.empty (encode satProgram) satTarget := by
  rw [satEncoded_eq]
  -- the seven declarations, the two maintenance rules, and the first of the two `set`s
  iterate 10 refine .cons ⟨_, rfl, .refl⟩ ?_
  exact .cons ⟨satTarget, rfl, .refl⟩ (.cons satTarget_cmdStep_saturate .nil)

/-- **And the state it reaches holds a view entry**, so the run is not satisfiable only by
doing nothing. -/
theorem satProgram_programStep_view :
    ∃ tgt, ProgramStep Database.empty (encode satProgram) tgt ∧ satViewEntry ∈ tgt.terms :=
  ⟨satTarget, satProgram_programStep, satTarget_mem_view⟩

/-! ### The statement

**The target is the interpreter's, not the specification's** — and no longer because the
specification's is unreachable. `ProgramStep Database.empty (encode P) tgt` is satisfiable
(`satProgram_programStep`); what it is not is **decidable**. The corpus result is a decision
procedure's answer at a concrete state, and every piece of that procedure is shaped for an
`FDatabase`: `sameClassF` reads a term list, and its two side conditions
`FDatabase.SubtermClosed` and `FDatabase.EqsRefl` are `Bool`-decided at the state itself
(`subtermClosedB`, `eqsReflB`). `ProgramStep` mentions a `Database`, whose `terms` is a
`Prop`-valued congruence over a `Set`, and it does not determine one state but a family. So
the hypothesis is `execM (encode P) = some tgt`: the run `difftest` performs, and the state
the corpus result is about.

The two are still not the same claim. `execM` under-fires relative to the specification
(`Proofs/Merge.lean`, `execM_contained`: the enumerator is stricter than `ValidEnv`), so this
is a statement about the reference implementation's target — but it is now a target the
specification can reach, which is what changed.

The source side keeps `ProgramStep`: a source program is constructor-only, `exec_programStep`
is an equality there, and the witness discharges the hypothesis through it. -/

/-- `EncodeDomain.ctorsOnly`, in the form `exec_programStep` asks for. -/
theorem Program.EncodeDomain.ctorDecls {P : Program} (h : P.EncodeDomain) : P.CtorDecls := by
  intro c hc
  match c with
  | .decl f dc => exact h.ctorsOnly _ hc f dc rfl
  | .action _ => trivial
  | .rule _ => trivial
  | .run _ => trivial
  | .saturate _ => trivial

/-! #### The forward half, by cases on `Cong`

`Cong` has four constructors and no `refl`, so the forward half is four obligations.
`symm` is free — `SameClass` is symmetric by construction — and the other three are stated
below, unproved. `cong_sameClass` is the reduction itself and is proved: it is `Cong.le` at
`R := SameClass tgt`. -/

/-- The three obligations `Cong.le` leaves once `symm` is discharged. -/
structure CongObligations (src tgt : Database) : Prop where
  /-- Every equation the source *asserts* — a reflexive one per term built, and one per
  `union` — the target's views agree on. One clause per writer. -/
  assert : ∀ a b, (a, b) ∈ src.eqs → SameClass tgt a b
  /-- The target's e-classes compose. This is `Database.Out`'s functionality at the view:
  two view entries at one key have merged, so their e-class columns are one class. -/
  trans : ∀ a b c, SameClass tgt a b → SameClass tgt b c → SameClass tgt a c
  /-- Congruence: children in one class put their applications in one class. This is what
  the rebuild is for, and it is the whole difficulty. -/
  congr : ∀ f as bs, Cong src (.app f as) (.app f as) → Cong src (.app f bs) (.app f bs) →
    List.Forall₂ (SameClass tgt) as bs → SameClass tgt (.app f as) (.app f bs)

/-- **The forward half is exactly those three.** `Cong` is the least relation closed under
its four rules (`Cong.le`), and `SameClass` is closed under `symm` outright. -/
theorem cong_sameClass {src tgt : Database} (h : CongObligations src tgt) {a b : Term}
    (hc : Cong src a b) : SameClass tgt a b :=
  Cong.le h.assert (fun _ _ hab => hab.symm) h.trans h.congr hc

/-- **Obligation `assert`, at the encoding.** Two writers to cover. `Database.addTerm`
writes a reflexive equation per subterm and `encodeBuild` writes `@fView(es) ↦ (f es, @Fiat)`
for the application it encodes, which is the id `ViewRepr` reads; `evalAction`'s `union`
writes a `@UF` edge, whose two endpoints share a view id only once the rebuild has re-keyed
them, so this clause rests on the rebuild exactly as `congr` does. **Not proved.** -/
theorem encode_assert {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b : Term) (h : (a, b) ∈ src.eqs) : SameClass tgt.toDatabase a b := by
  sorry

/-- **Obligation `trans`, at the encoding.** Needs the view's functional dependency: if `b`
reads to `e₁` and to `e₂` then the two entries collided on a congruent key and the `:merge`
unioned them, so `e₁` and `e₂` are one class — and, at a rebuilt state, one id. Not free
from the flat reading, which is why the union-find walk was there. **Not proved.** -/
theorem encode_trans {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b c : Term) (hab : SameClass tgt.toDatabase a b) (hbc : SameClass tgt.toDatabase b c) :
    SameClass tgt.toDatabase a c := by
  sorry

/-- **Obligation `congr`, at the encoding.** The rebuild rules re-key a view entry to its
children's `@UF` leaders, so two applications whose children share ids key the *same* view
entry and the `:merge` unions their e-class columns. This is the whole difficulty and it is
what a rebuilt state buys. **Not proved.** -/
theorem encode_congr {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (f : FnName) (as bs : List Term) (ha : Cong src (.app f as) (.app f as))
    (hb : Cong src (.app f bs) (.app f bs))
    (hl : List.Forall₂ (SameClass tgt.toDatabase) as bs) :
    SameClass tgt.toDatabase (.app f as) (.app f bs) := by
  sorry

/-- **No equality is lost**: assembled from the three obligations, with `symm` free. -/
theorem encode_corresponds_forward {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (h : Cong src a b) :
    SameClass tgt.toDatabase a b :=
  cong_sameClass ⟨encode_assert hdom hsrc htgt, encode_trans hdom hsrc htgt,
    encode_congr hdom hsrc htgt⟩ h

/-- **No equality is invented.** The target-side induction has no `Cong.le` to lean on:
`SameClass` is an existential over view entries, so this half is an invariant over the
commands that write them — every view entry the encoding records is an equality the source
derives. **Not proved.** -/
theorem encode_corresponds_complete {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (h : SameClass tgt.toDatabase a b) :
    Cong src a b := by
  sorry

/-- **The correspondence.** `difftest correspond 64` runs exactly this claim over the 70
in-domain cases and the seventeen probes, through `sameClassF` and `closureF`, and reports
70 agreeing, 0 LOST, 0 INVENTED — and `link-diff` 0, which is what says the swept relation
is this one.

`EncodeDomain` is still needed: outside it `encode` is not defined for the program at all —
a `:merge` declaration has no table triple to emit, and a source name in the generated
namespace collides with one. `Rebuilt` is *not* a hypothesis: it is a postcondition of the
specification's rebuild command (`cmdStep_rebuilt`), and the hypothesis here names an
`execM` target, so what the two unproved halves have to lean on is the interpreter's own
`mergeSaturateF` fixpoint instead. -/
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) :
    Cong src a b ↔ SameClass tgt.toDatabase a b :=
  ⟨encode_corresponds_forward hdom hsrc htgt, encode_corresponds_complete hdom hsrc htgt⟩

/-! ### The witness

`ENCODING.md`: two of thirteen previous M11 statements were vacuous and nobody noticed,
because they carried `sorry`. So before the `sorry`s above are allowed to stand, here is a
program whose three hypotheses hold **together**, and a pair of term pairs at which both
sides of the conclusion are non-trivial — one both say yes to, one both say no to. An `iff`
between two relations that are always false is true and worthless; `agree-true` is the same
measurement over the whole corpus, and it is 778.

The two runs cannot be `#guard`s: an encoded action is followed by a saturating rebuild, and
running one during elaboration took `lake build difftest` past fifteen minutes. So the
witness is this theorem — compiled, no `sorry` — whose hypotheses are all *decidable* facts
about one concrete program, and `difftest correspond-selftest` evaluates them and reports.
-/

/-- The witness program: two applications made congruent by a `union` of their leaves, with
its constructors declared. `DiffTest.lean`'s `unionCase`, written out because that file is
downstream of this one. It is the smallest program that derives an equality between distinct
terms — two, in fact: `One = Two` and the two `Add`s above them. -/
def witnessProgram : Program :=
  [.decl "Add" { arity := 2, outArity := 1, merge := none },
   .decl "One" { arity := 0, outArity := 1, merge := none },
   .decl "Two" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.app "Add" [.app "One" [], .app "Two" []])),
   .action (.expr (.app "Add" [.app "Two" [], .app "One" []])),
   .action (.union (.app "One" []) (.app "Two" []))]

/-- `(One)`. -/
def witnessOne : Term := .app "One" []

/-- `(Two)`, which the program unions with `witnessOne`. -/
def witnessTwo : Term := .app "Two" []

/-- `(Add One Two)`, which is congruent to `(Add Two One)` and *not* to `(One)`. -/
def witnessAdd : Term := .app "Add" [witnessOne, witnessTwo]

/-- The witness is in `encode`'s domain, at compile time: `Program.encodeDomainB` and its
equivalence live downstream in `DiffTest.lean`, so the six clauses are discharged here
directly. -/
theorem witnessProgram_encodeDomain : witnessProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc f dc heq
    subst heq
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with h | h | h | h | h | h | h <;> simp_all
  noSet := by
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> trivial
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  noAtVar := by decide +kernel
  noAtRuleset := by decide +kernel

/-- **The hypotheses of `encode_corresponds` are simultaneously satisfiable, and both sides
of its conclusion are inhabited and refutable at the witness.**

Everything it asks of the two runs is decidable and is checked at run time by
`difftest correspond-selftest`; `hdom` is discharged here, at compile time. -/
theorem encode_corresponds_witness {d e : FDatabase} {a b c₁ c₂ : Term}
    (hd : exec witnessProgram = some d) (he : execM (encode witnessProgram) = some e)
    (hsc : e.SubtermClosed) (hr : e.EqsRefl)
    (hyes₁ : (a, b) ∈ d.closureF) (hyes₂ : sameClassF e a b = true)
    (hno₁ : (c₁, c₂) ∉ d.closureF) (hno₂ : sameClassF e c₁ c₂ = false) :
    ∃ src, witnessProgram.EncodeDomain ∧ ProgramStep Database.empty witnessProgram src ∧
      execM (encode witnessProgram) = some e ∧
      (Cong src a b ∧ SameClass e.toDatabase a b) ∧
      (¬ Cong src c₁ c₂ ∧ ¬ SameClass e.toDatabase c₁ c₂) := by
  refine ⟨d.toDatabase, witnessProgram_encodeDomain, ?_, he, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (exec_programStep witnessProgram_encodeDomain.ctorDecls
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · exact FDatabase.mem_closureF_iff.mp hyes₁
  · exact (sameClassF_iff hsc hr a b).mp hyes₂
  · exact fun h => hno₁ (FDatabase.mem_closureF_iff.mpr h)
  · exact fun h => by simp [(sameClassF_iff hsc hr c₁ c₂).mpr h] at hno₂

end Egglog
