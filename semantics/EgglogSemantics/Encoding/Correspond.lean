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
* **Proved, and the forward half's whole argument**: `cong_sameClass_of_state`. The three
  obligations `cong_sameClass` leaves hold at *any* target with three named properties —
  `Database.ViewLeader`, `Database.ViewsCover` and `Database.UnionsRead` — over any source
  with `Database.WF`, and the four reductions that make it up (`trans_of_viewLeader`,
  `sameClass_congr_of_keyed`, `viewRepr_total`, `sameClass_self_of_viewsCover`) are proved
  outright. So the forward half is one lemma from done, and that lemma is "the state `execM`
  returned has the three properties".
* **Proved, and the completeness half's whole argument**: `sameClass_cong_of_state`, the
  same shape. `SameClass d a b → Cong src a b` holds at any target with *one* named property
  — `Database.ViewsSound`, that every view entry claims only what the source derives — over
  any source with `Database.WF`, at the source's own e-nodes. The reduction is
  `sameClass_cong_of_justified` (three lines: `SameClass` is flat) plus `cong_of_viewRepr`,
  and the per-writer obligations `ViewsSound`'s preservation leaves are each discharged
  outright: `entrySound_build`, `EntrySound.eclass`, `EntrySound.column`,
  `EntrySound.select`, `cong_of_entrySound_collide`, `cong_of_eqs`, `cong_of_pathCompress`.
* **Proved, and what says the specification's own target is reachable**:
  `not_mergeConflict_self`, `refutationState_mergeSaturated`, and
  `satProgram_programStep` — a compiled `ProgramStep Database.empty (encode P) tgt` for a
  `P` that builds a term. Each of the three is the negation of a lemma that stood here
  before `Spec/Step.lean` read `identityVals`, and that refutation is why the statement
  below reads `execM`; the reason it still does is a different one.
  `satTarget_viewLeader`, `satTarget_viewsSound` and `refutationState_edgesSound` are the
  same discipline applied to the new residues: each discharged at a state a program reaches,
  non-vacuously.
* **Proved, and the shared crux of both residues**: the rule-head match correspondence, in
  `Encoding/Match.lean`, and now with nothing left over.
  `exists_validQuerySubst_of_patternReads` is the property of the two states,
  `patternReads_of_encodeQuery` reads the encoded query back off `encodeQuery` to establish
  its premise, and `encodeQuery_drops_literal_pattern` is the compiled refutation of the two
  side conditions' necessity.
* **Proved, and the case the completeness half was expected to founder on**: a rule *head*'s
  build. `exists_validQuerySubst_at_ids` pins the source reading to the ids the target read
  rather than to arbitrary congruent terms, which is what makes the source's own head
  evaluation build the very term `encodeBuild`'s skolem names — so the head owes only its
  firing (`entrySound_headBuild`, `cong_headUnion`), and not the fact
  `encode_corresponds_invents_enode` refutes at a key column.
* **Proved, and the shared crux of three of the four residues**: the **action read-back**.
  `holdsBuild_of_execActions` reads both rows a build's `set`s wrote off the block that ran
  them, `viewRepr_self_of_execActions` assembles them into the reading a `SameClass` is two
  of, and `holdsBuild_of_execProgramM`/`viewRepr_self_of_execProgramM` are the same where the
  block is the *top-level* `Cmd.action`s `encodeCmd` emits. `FDatabase.execProgramM_terms` is
  what carries the rows to the end of the run, and it is the only form the read-back can take:
  the row a rebuild displaced is gone, the entry term is not.
* **`sorry`**, seven, one *clause* each and none of them an obligation any more.
  `execM_viewsCover_lits`, `execM_viewsCover_keyed`, `execM_readsSelf` and `execM_edges` need
  the induction over `encode P`'s commands that the read-back does not supply;
  `execM_viewLeader` and `execM_eclassFollowed` need the interpreter's rebuild fixpoint;
  `execM_viewsSound` is the completeness half. `execM_viewsCover`, `execM_unionsJoined` and
  `execM_unionsRead` are assembled from them, proved.
  `Encoding/Match.lean`'s `uRebuilt_unionsJoined` is `Database.UnionsJoined`'s three clauses
  at a state a program reaches and `uTgt_not_unionsRead` is the third failing one rebuild
  firing earlier. `encode_assert`, `encode_trans`, `encode_congr`,
  `encode_corresponds_forward`, `encode_corresponds_complete` and `encode_corresponds` are
  assembled from them and carry `sorryAx` through them.
* **Refuted, and it narrowed the domain**: two of those clauses were *false*.
  `litBuild_not_viewsCover` and `litBuild_not_readsSelf` are compiled refutations at
  `litBuildProgram`, one `.action (.expr (.lit 5))`, whose build emits no action at all — so
  the source holds the literal and the target holds nothing.
  `litBuildProgram_domain_but_bare` is every other clause of the domain holding there, and
  `Program.EncodeDomain.noBareBuild` is the repair: a decidable condition on the source text,
  implied by `Spec/Scope.lean`'s own `Action.Scoped`, costing the corpus nothing (still 70 of
  166 in domain).
* **Refuted, and recorded so it is not tried again**: the view's *functional dependency*,
  which is the obvious reduction of `trans` and is false at the witness program. The section
  "What the three obligations reduce to" has the state that refutes it, and the same state
  refutes `MergeSaturated` at an `execM` target.
* **Refuted, and it moved the statement**: the *unrestricted* completeness half.
  `encode_corresponds_invents_enode` is a compiled refutation of
  `SameClass tgt a b → Cong src a b` at `witnessProgram`, whose rebuild gives `(Add One One)`
  an e-class the source has no e-node for. Both halves are now stated at the source's own
  e-nodes, which costs the forward half nothing and is what the corpus sweep measures.
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
  unfold MergeConflict FnDecl.unchangedWidth
  have hbe : body.isEmpty = false := by simpa [List.isEmpty_iff] using hb
  cases decl.identityVals <;> simp [hbe]

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

/-- The one `@UF` entry pins the key and both value tuples of any collision at it, so every
collision there is a collision of that entry with itself. -/
private theorem refutationState_pin {cs vals : List Term} (hl : cs.length = 1)
    (hmem : Term.app ufName (cs ++ vals) ∈ refutationState.toDatabase.terms) :
    cs = [refA] ∧ vals = [refA, .app fiatName []] := by
  rw [FDatabase.mem_toDatabase_terms] at hmem
  match cs with
  | [] => simp at hl
  | [x] =>
    suffices h : x = refA ∧ vals = [refA, .app fiatName []] from ⟨by rw [h.1], h.2⟩
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
    have hab : a = b := (refutationState_pin (by simpa [ufDecl] using hla) hma).2.trans
      (refutationState_pin (by simpa [ufDecl] using hlb) hmb).2.symm
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
phase; the twelfth is `satTarget_cmdStep_saturate`.

**At a `P` that asserts an equation between distinct terms it is not**, and that is not this
program's doing: the trailing `Cmd.saturate rebuildRuleset` has no fixpoint once a `@UF` edge
sits on a view's e-class column, which every source `union` puts there.
`Encoding/Match.lean`'s `uTgt_saturate_infinite` is the compiled statement. So this witness is
exactly as strong as it reads — a program with no `union` — and the specification's target is
unavailable for the rest. -/
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

**The target is the interpreter's, not the specification's.** Two reasons now, and neither is
the one `ENCODING.md` records. `ProgramStep Database.empty (encode P) tgt` is satisfiable at a
program that only builds (`satProgram_programStep`) and is **not decidable**; and at a program
that asserts an equation between distinct terms — which is every program this half's `union`
clause is about — it is not satisfiable either, because `encode`'s rebuild has no fixpoint there
(`Encoding/Match.lean`'s `uTgt_saturate_infinite`). The interpreter's `execM` reaches its target
because `mergeOneOriented` *deletes* the row a collision displaces, and the specification's
`terms` is monotone; that difference is the whole of it.

The corpus result is a decision procedure's answer at a concrete state, and every piece of that
procedure is shaped for an `FDatabase`: `sameClassF` reads a term list, and its two side
conditions `FDatabase.SubtermClosed` and `FDatabase.EqsRefl` are `Bool`-decided at the state
itself (`subtermClosedB`, `eqsReflB`). `ProgramStep` mentions a `Database`, whose `terms` is a
`Prop`-valued congruence over a `Set`, and it does not determine one state but a family. So the
hypothesis is `execM (encode P) = some tgt`: the run `difftest` performs, and the state the
corpus result is about.

The two are still not the same claim, and the gap is wider than under-firing. `execM`
under-fires relative to the specification (`Proofs/Merge.lean`, `execM_contained`: the
enumerator is stricter than `ValidEnv`), and it also *deletes*, which is what lets it reach a
target at all on a program with a `union`. So this is a statement about the reference
implementation's target, and on the programs the `union` clause is about there is no
specification target to compare it with.

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

/-! #### What the three obligations reduce to

Each of the three is a *reduction* plus one property of the state `execM` returned. The
reductions are proved below; the properties are the residue, one `sorry` each, and each is
stated as a fact about a `Database` rather than as a restatement of the obligation, so what
is missing is visible and each is checkable at a concrete state.

**`Database.Out` is not functional at a view key, and the obligations must not be reduced to
saying it is.** The natural reading of `trans` — two entries at one key have collided, the
`:merge` resolved them, so their e-class columns coincide — is *refuted at this file's own
witness program*. `difftest correspond-dump 64 union` prints, for `witnessProgram`,

```
  view @TwoView() ↦ (One)
  view @TwoView() ↦ (Two)
```

and both are in `terms`: `mergeOneOriented` overwrites the resident *row* and `addTerm`s the
combined entry, and nothing is ever removed from `terms` (`MERGE.md`, "Constraint (3):
monotonicity"). So `ViewRepr tgt (Two)` holds of `(One)` and of `(Two)` alike.

`MergeSaturated` is not available at such a state either, which is why neither it nor
`Rebuilt` appears below: the displaced entry still *collides* with the survivor —
`identityVals := some 1` counts the e-class column and `[(Two)] ≠ [(One)]`, so
`MergeConflict` holds — and a `MergeStep` fires at a collision the interpreter had already
settled by deleting the row.

What *is* true there is the next thing down: two ids one source term reads are
`@UF`-connected, so they share a leader. `correspond-dump 64 union`'s `leaders` column is a
single term for each of the four source terms, and `difftest correspond`'s **`leader-diff`**
column is the corpus-wide measurement of the same thing — the pairs on which joining at a
*leader* and joining at any shared node disagree, 0 on every case. `Database.ViewLeader` is
that. -/

/-- **A leader for the view reading.** `lead` picks, per id, one that every source term
reading that id also reads; and two ids one source term reads have the same `lead`.

Not `Database.Out`'s functionality, which is false — see the section header. `lead` is
egglog's union-find representative, but it is existentially quantified rather than computed:
`Database.Out` records every parent a merge displaced, so `UFLeader` is a relation. -/
def Database.ViewLeader (d : Database) : Prop :=
  ∃ lead : Term → Term,
    (∀ t e, ViewRepr d t e → ViewRepr d t (lead e)) ∧
    (∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → lead e₁ = lead e₂)

/-- **Obligation `trans` reduces to `Database.ViewLeader`.** The two witnesses are both ids
of `b`, so they share a `lead`, and that `lead` is an id of `a` and of `c`. -/
theorem SameClass.trans_of_viewLeader {d : Database} (h : d.ViewLeader) {a b c : Term}
    (hab : SameClass d a b) (hbc : SameClass d b c) : SameClass d a c := by
  obtain ⟨lead, hmem, huniq⟩ := h
  obtain ⟨e₁, ha₁, hb₁⟩ := hab
  obtain ⟨e₂, hb₂, hc₂⟩ := hbc
  refine ⟨lead e₁, hmem a e₁ ha₁, ?_⟩
  rw [← huniq b e₂ e₁ hb₂ hb₁]
  exact hmem c e₂ hc₂

/-! #### And at a state a program reaches

`Database.ViewLeader` is the residue `trans` is reduced to, so it had better hold somewhere:
here it is at `satTarget`, the state `satProgram_programStep` steps to. This is the
*degenerate* case of the property — one nullary constructor and no `union`, so a term has at
most one id and the identity is a `lead` — and it is the case every program with no `union` is
in. Where two ids do appear, `difftest correspond-dump 64 union` is the reading, and the
section above is why `lead` and not equality is what survives there. -/

/-- The four terms the run holds, enumerated. -/
private theorem satTarget_mem_cases {t : Term} (h : t ∈ satTarget.terms) :
    t = satViewEntry ∨ t = Term.app fiatName [] ∨ t = satTermEntry ∨ t = Term.app "A" [] := by
  rw [satTarget_terms] at h
  simpa [satTermEntry, satViewEntry] using h

/-- **At `satTarget` a source term has at most one id.** Two of the four terms are too short
to be a view entry at all — a key plus the two value columns is two columns at least — one is
`@ATerm`'s row, which is one column, and `@AView(A, @Fiat)` is what is left, its e-class
column `A`. `satTarget_diag` is what lets the key be read up to equality. -/
private theorem satTarget_viewRepr {t e : Term} (h : ViewRepr satTarget t e) :
    e = Term.app "A" [] := by
  match h with
  | .lit hm => exact absurd (satTarget_mem_cases hm) (by simp [satTermEntry, satViewEntry])
  | @ViewRepr.app _ f as es e pf _ ho =>
    obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : es = bs :=
      List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag satTarget_diag h)
    rcases satTarget_mem_cases hmem with h' | h' | h' | h' <;>
        simp only [satTermEntry, satViewEntry, Term.app.injEq] at h' <;>
      [skip; skip; skip; skip]
    · obtain rfl : es = [] := by
        have hl : (es ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
        simp only [List.length_append, List.length_cons] at hl
        exact List.eq_nil_of_length_eq_zero (by omega)
      exact (show e = Term.app "A" [] ∧ pf = Term.app fiatName [] by simpa using h'.2).1
    · have hl : (es ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      omega
    · have hl : (es ++ [e, pf]).length = 1 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      omega
    · have hl : (es ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      omega

/-- **`Database.ViewLeader` holds at `satTarget`**, with the identity as its `lead`. -/
theorem satTarget_viewLeader : satTarget.ViewLeader :=
  ⟨id, fun _ _ h => h, fun _ _ _ h₁ h₂ =>
    show id _ = id _ from (satTarget_viewRepr h₁).trans (satTarget_viewRepr h₂).symm⟩

/-- **The keys the target's views carry**, relative to what the source holds.

`keyed` is the rebuild, stated: an entry for `f` at *every* tuple of ids its children are
given, not only at the tuple the build wrote. `rebuildRules`' column rules are what put them
there — one `set` per column per `@UF` edge, so a saturated ruleset covers the product — and
`difftest correspond-dump 64 union` shows the product covered and nothing outside it: keys
`(One,One)`, `(One,Two)` and `(Two,One)` for `@AddView`, and no `(Two,Two)`, since `(One)` is
a leader and reads only to itself.

`lits` is the one thing no view entry can say. `encodeBuild` emits no action for a literal,
so a literal is its own id exactly where the target holds it, and it is held as a key column
of the entry its parent's build wrote. -/
structure Database.ViewsCover (d src : Database) : Prop where
  /-- A literal the source holds, the target holds too. -/
  lits : ∀ l : Lit, Term.lit l ∈ src.terms → Term.lit l ∈ d.terms
  /-- An application the source holds has a view entry at every key its children's ids
  form. -/
  keyed : ∀ f as es, Term.app f as ∈ src.terms → ViewReprList d as es →
    ∃ e pf, d.Out (viewName f) es [e, pf]

/-- A pointwise `SameClass` is one shared id tuple: exactly what a view read needs, since
`Database.Out` is keyed on the tuple. -/
theorem viewReprList_of_forall₂ {d : Database} : ∀ {as bs : List Term},
    List.Forall₂ (SameClass d) as bs → ∃ es, ViewReprList d as es ∧ ViewReprList d bs es
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons hab hl => by
      obtain ⟨e, hae, hbe⟩ := hab
      obtain ⟨es, h₁, h₂⟩ := viewReprList_of_forall₂ hl
      exact ⟨e :: es, .cons hae h₁, .cons hbe h₂⟩

/-- **Obligation `congr` reduces to `Database.ViewsCover.keyed`.** The pointwise hypothesis
gives one id tuple both argument lists read to, `keyed` gives a view entry at it, and that
entry's e-class column is an id of both applications. The second self-congruence premise is not
used, nor is the rest of `ViewsCover`. -/
theorem sameClass_congr_of_keyed {src d : Database} (hc : d.ViewsCover src) {f : FnName}
    {as bs : List Term} (ha : Term.app f as ∈ src.terms)
    (hl : List.Forall₂ (SameClass d) as bs) :
    SameClass d (.app f as) (.app f bs) := by
  obtain ⟨es, h₁, h₂⟩ := viewReprList_of_forall₂ hl
  obtain ⟨e, pf, ho⟩ := hc.keyed f as es ha h₁
  exact ⟨e, .app h₁ ho, .app h₂ ho⟩

mutual

/-- **Every term the source holds has an id**, by `ViewsCover` and structural recursion:
`lits` at a literal, and `keyed` at an application whose children's ids the recursion
supplies. `Database.WF` is what says the children are held, and `ProgramStep.wf` delivers it
from the empty state. -/
theorem viewRepr_total {d src : Database} (hc : d.ViewsCover src) (hw : src.WF) :
    ∀ t : Term, t ∈ src.terms → ∃ e, ViewRepr d t e
  | .lit l, ht => ⟨.lit l, .lit (hc.lits l ht)⟩
  | .app f as, ht => by
      obtain ⟨es, hes⟩ := viewRepr_list_total hc hw as fun a ha =>
        hw.subtermClosed _ ht (Term.arg_subterms ha (Term.self_mem_subterms a))
      obtain ⟨e, pf, ho⟩ := hc.keyed f as es ht hes
      exact ⟨e, .app hes ho⟩

@[inherit_doc viewRepr_total]
theorem viewRepr_list_total {d src : Database} (hc : d.ViewsCover src) (hw : src.WF) :
    ∀ as : List Term, (∀ a ∈ as, a ∈ src.terms) → ∃ es, ViewReprList d as es
  | [], _ => ⟨[], .nil⟩
  | a :: as, ht => by
      obtain ⟨e, he⟩ := viewRepr_total hc hw a (ht a (List.mem_cons_self ..))
      obtain ⟨es, hes⟩ := viewRepr_list_total hc hw as fun b hb =>
        ht b (List.mem_cons_of_mem _ hb)
      exact ⟨e :: es, .cons he hes⟩

end

/-- **The reflexive half of obligation `assert` reduces to `Database.ViewsCover`.** A
reflexive equation is a term the source holds, and a term with an id is in one class with
itself. -/
theorem sameClass_self_of_viewsCover {src d : Database} (hc : d.ViewsCover src) (hw : src.WF)
    {a : Term} (h : (a, a) ∈ src.eqs) : SameClass d a a :=
  let ⟨e, he⟩ := viewRepr_total hc hw a (Cong.assert h)
  ⟨e, he, he⟩

/-- **What is left of obligation `assert`**: the equations `Database.addTerm` did *not*
write. `encode`'s source fragment has one other writer, `evalAction`'s `union`, and it is the
only one that can relate distinct terms — so this is the `union` clause alone, and it rests
on the rebuild exactly as `congr` does: the two endpoints get a `@UF` edge between their
ids, and the views share an id only once the e-class rebuild rule has followed it. -/
def Database.UnionsRead (d src : Database) : Prop :=
  ∀ a b, (a, b) ∈ src.eqs → a ≠ b → SameClass d a b

/-- **`Database.UnionsRead`, split into the three writers it needs.**

`UnionsRead` is a statement about `SameClass`, which is two `ViewRepr`s at one id; the three
clauses below are the three separate things that have to have happened for the id to be
shared, one writer each. The reduction (`unionsRead_of_unionsJoined`) uses nothing else.

Stated at *source* terms and source equations throughout, so no clause quantifies over the
stale view rows a rebuild displaced — `Database.Out` reads every row `terms` ever held
(`MERGE.md`, "Constraint (3): monotonicity"), and the fixpoint the interpreter reaches is a
fixpoint over its *current* tables. A clause about arbitrary entries would be a claim about
rows the rebuild may have stopped following; these three are not. -/
structure Database.UnionsJoined (d src : Database) : Prop where
  /-- **Every source term reads to itself.** The entry its own build wrote, read with each
  child read as itself. Nothing removes it: `terms` only grows. -/
  readsSelf : ∀ t ∈ src.terms, ViewRepr d t t
  /-- **A source `union` wrote its edge.** `encodeAction` emits
  `@UF (ordering-max x₁ x₂) ↦ (ordering-min x₁ x₂, pf)`, and which endpoint is the key is
  whichever `ordering-max` picked — so the clause is the disjunction, exactly as
  `cong_of_eqs` and `cong_headUnion` take `ho`. -/
  edges : ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
    (∃ pf, d.Out ufName [a] [b, pf]) ∨ (∃ pf, d.Out ufName [b] [a, pf])
  /-- **And the rebuild followed it.** The e-class rebuild rule re-`set`s a view entry at
  the `@UF` parent of its e-class column; at a source term's own reading that is this. The
  one clause that is a *fixpoint* property rather than a read-back of an emitted action. -/
  eclassFollowed : ∀ t p pf, t ∈ src.terms → ViewRepr d t t → d.Out ufName [t] [p, pf] →
    ViewRepr d t p

/-- **Obligation `assert`'s `union` half reduces to `Database.UnionsJoined`.** The edge runs
between the two endpoints; the one it is keyed at reads to the other, and the other reads to
itself, so that other *is* the shared id.

No `Database.WF`, and in particular no `LitsIsolated`: the literal case is not excluded here
but discharged, since `readsSelf` covers a literal too (`ViewRepr.lit`) and `eclassFollowed`
is only ever applied at the endpoint the edge is keyed at. -/
theorem unionsRead_of_unionsJoined {src d : Database} (h : d.UnionsJoined src) :
    d.UnionsRead src := by
  intro a b hab hne
  have ha : a ∈ src.terms := (eqsInTerms_free (Cong.assert hab)).1
  have hb : b ∈ src.terms := (eqsInTerms_free (Cong.assert hab)).2
  rcases h.edges a b hab hne with ⟨pf, ho⟩ | ⟨pf, ho⟩
  · exact ⟨b, h.eclassFollowed a b pf ha (h.readsSelf a ha) ho, h.readsSelf b hb⟩
  · exact ⟨a, h.readsSelf a ha, h.eclassFollowed b a pf hb (h.readsSelf b hb) ho⟩

/-- **The whole forward half, from three properties of the target and nothing else.**

No `execM`, no `encode`, no `sorry`: `Cong src a b → SameClass d a b` at any target with
`ViewLeader`, `ViewsCover` and `UnionsRead`, over any source with `Database.WF`. That is what
the reduction buys — the three `encode_*` obligations below are this theorem instantiated at
an `execM` target, and what is left unproved is exactly that an `execM` target has the three
properties. -/
theorem cong_sameClass_of_state {src d : Database} (hw : src.WF) (hlead : d.ViewLeader)
    (hcov : d.ViewsCover src) (hun : d.UnionsRead src) {a b : Term} (h : Cong src a b) :
    SameClass d a b :=
  cong_sameClass
    ⟨fun x y hxy => if hxyeq : x = y then hxyeq ▸ sameClass_self_of_viewsCover hcov hw
        (hxyeq ▸ hxy) else hun x y hxy hxyeq,
     fun _ _ _ => SameClass.trans_of_viewLeader hlead,
     fun _ _ _ ha _ hl => sameClass_congr_of_keyed hcov ha hl⟩ h

/-! ### The action read-back

`encodeBuild` emits two `set`s per application — the term-relation row and the view row — and
every residue below needs to know they *ran*. This section is that read-back, in four steps and
with no `execM` and no `encode` beyond `encodeBuild`:

* **terms persist.** `FDatabase.execProgramM_terms` and the chain under it. This is the one
  thing the read-back must not overstate: `mergeOneOriented` overwrites the resident *row* and
  `addTerm`s the survivor, and `Impl/` never removes a term (`mergeOneOriented_confined`,
  `mergeRound_confined`), so "the `set` ran" survives as *the entry term is still held* and not
  as "the row is still current", which is false.
* **the rows.** `holdsBuild_of_execActions`: after a build's block, every application the built
  expression applies has both of its rows, keyed on the arguments' values.
* **the reading.** `viewRepr_self_of_execActions`: those rows, assembled into
  `ViewRepr d t t` — what `Database.UnionsJoined.readsSelf` asks for and what a `SameClass` is
  two of.
* **at a run of commands.** `holdsBuild_of_execProgramM` and
  `viewRepr_self_of_execProgramM`: the same, where the block is the *top-level* `Cmd.action`s
  `encodeCmd` emits, each with its own merge phase. A rule head needs no bridge —
  `execLocalActions` *is* `execActions`.

`Encoding/Match.lean`'s head-build case consumes the second and third directly; what neither
reaches is the induction over `encode P`'s commands that says every source term came from a
block the run passed, which is what the residues below are still missing. -/

/-! #### Terms persist -/

namespace FDatabase

theorem mergeSaturateF_terms {n : Nat} : ∀ {d e : FDatabase},
    d.mergeSaturateF n = some e → ∀ t ∈ d.terms, t ∈ e.terms := by
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ fun _ h => h
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ fun _ h => h
    · exact fun t ht => ih hs t (mergeRound_confined.1 t ht)

theorem execRunRules_terms {R : RulesetName} {d : FDatabase} :
    ∀ t ∈ d.terms, t ∈ (execRunRules R d).terms :=
  execRunRules_induction (P := fun x => ∀ t ∈ d.terms, t ∈ x.terms) (fun _ h => h)
    fun _ _ _ _ hacc _ _ _ t ht => mem_terms_union.mpr (Or.inl (hacc t ht))

theorem runRoundM_terms {R : RulesetName} {d e : FDatabase} (h : d.runRoundM R = some e) :
    ∀ t ∈ d.terms, t ∈ e.terms :=
  fun t ht => mergeSaturateF_terms h t (execRunRules_terms t ht)

theorem runSaturateM_terms {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → ∀ t ∈ d.terms, t ∈ e.terms := by
  intro n
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, -, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact absurd hxe (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact fun t ht => ih hxe t (runRoundM_terms hx t ht)

theorem execCmdM_terms {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    ∀ t ∈ d.terms, t ∈ d'.terms := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun t ht => mergeSaturateF_terms h₂ t ((execAction_lists h₁).1 t ht)
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h
  | run R => exact runRoundM_terms hs
  | saturate R => exact runSaturateM_terms _ hs
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h

theorem execProgramM_terms {p : Program} : ∀ {d d' : FDatabase},
    d.execProgramM p = some d' → ∀ t ∈ d.terms, t ∈ d'.terms := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ fun _ h => h
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun t ht => ih h₂ t (execCmdM_terms h₁ t ht)

theorem execProgramM_append {p q : Program} : ∀ {d D : FDatabase},
    d.execProgramM (p ++ q) = some D →
      ∃ m, d.execProgramM p = some m ∧ m.execProgramM q = some D := by
  induction p with
  | nil => intro d D h; exact ⟨d, rfl, h⟩
  | cons c cs ih =>
    intro d D h
    rw [List.cons_append, FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m, hm, hmD⟩ := ih h₂
    exact ⟨m, by rw [FDatabase.execProgramM, h₁, Option.bind_some]; exact hm, hmD⟩

@[simp] theorem addRow_env {d : FDatabase} {f : FnName} {as vs : List Term} :
    (FDatabase.addRow f as vs d).env = d.env := rfl

@[simp] theorem mem_addRow_terms {d : FDatabase} {f : FnName} {as vs : List Term}
    {s : Term} : s ∈ (FDatabase.addRow f as vs d).terms ↔
      s ∈ (Term.app f (as ++ vs)).subtermList ∨ s ∈ d.terms :=
  FDatabase.mem_addTerm_terms

end FDatabase

/-! #### The rows a build writes -/

mutual
/-- The applications an expression *applies*, head and argument list each. A leaf contributes
none, and neither does a variable's value: `encodeBuild` emits no action for a leaf, so the rows
a build writes are indexed by the built expression's own syntax. -/
def Expr.apps : Expr → List (FnName × List Expr)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args) :: Expr.appsList args

/-- `Expr.apps` over an argument list. -/
def Expr.appsList : List Expr → List (FnName × List Expr)
  | [] => []
  | e :: es => e.apps ++ Expr.appsList es
end

/-- A `set` and nothing else, which is all a build emits. -/
def Action.IsSet : Action → Prop
  | .set _ _ _ => True
  | _ => False

mutual
/-- **A build emits `set`s and nothing else.** In particular no `letBind`, which is why a build
moves neither the signature nor the environment, and why every one of its `set`s evaluates its
operands in the state the block started in. -/
theorem encodeBuild_isSet : ∀ (e : Expr) (n : Nat), ∀ a ∈ (encodeBuild e n).2.1, a.IsSet
  | .lit _, _ => by simp [encodeBuild]
  | .var _, _ => by simp [encodeBuild]
  | .app f args, n => by
      intro a ha
      rw [encodeBuild_app_actions] at ha
      rcases List.mem_append.mp ha with h | h
      · exact encodeBuildArgs_isSet args n a h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> trivial

@[inherit_doc encodeBuild_isSet]
theorem encodeBuildArgs_isSet : ∀ (es : List Expr) (n : Nat),
    ∀ a ∈ (encodeBuildArgs es n).2.1, a.IsSet
  | [], _ => by simp [encodeBuildArgs]
  | e :: es, n => by
      intro a ha
      rw [encodeBuildArgs_cons_actions] at ha
      rcases List.mem_append.mp ha with h | h
      · exact encodeBuild_isSet e n a h
      · exact encodeBuildArgs_isSet es _ a h
end

/-- **What one `set` records**: the row `FDatabase.addRow` writes, at the key and value tuples
the operands evaluated to in the state the action ran in. `addRow` is `addTerm` on the entry
term, so this is also the read-back of the *entry term* and of all of its subterms. -/
theorem execAction_set {d e : FDatabase} {f : FnName} {args out : List Expr}
    (h : execAction d (.set f args out) = some e) :
    ∃ as vs, Expr.evalList d.sig args d.env = some as ∧
      Expr.evalList d.sig out d.env = some vs ∧ e = FDatabase.addRow f as vs d := by
  simp only [execAction] at h
  obtain ⟨as, has, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨as, vs, has, hvs, rfl⟩

/-- A `set` leaves the environment alone. -/
theorem execAction_env_of_isSet {d e : FDatabase} : ∀ {a : Action}, a.IsSet →
    execAction d a = some e → e.env = d.env
  | .set _ _ _, _, h => by
      obtain ⟨-, -, -, -, rfl⟩ := execAction_set h
      rfl

/-- A block of `set`s leaves the environment alone. -/
theorem execActions_env_of_isSet {as : List Action} (ha : ∀ a ∈ as, a.IsSet) :
    ∀ {d e : FDatabase}, execActions d as = some e → e.env = d.env := by
  induction as with
  | nil => intro d e h; rw [execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    intro d e h
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some d' =>
      rw [execActions, hv, Option.bind_some] at h
      exact (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h).trans
        (execAction_env_of_isSet (ha a List.mem_cons_self) hv)

/-- Running a concatenation of action blocks runs the first and then the second. -/
theorem execActions_append {as bs : List Action} : ∀ {d e : FDatabase},
    execActions d (as ++ bs) = some e →
      ∃ m, execActions d as = some m ∧ execActions m bs = some e := by
  induction as with
  | nil => intro d e h; exact ⟨d, rfl, h⟩
  | cons a as ih =>
    intro d e h
    cases hv : execAction d a with
    | none => rw [List.cons_append, execActions, hv] at h; simp at h
    | some d' =>
      rw [List.cons_append, execActions, hv, Option.bind_some] at h
      obtain ⟨m, hm, hme⟩ := ih h
      exact ⟨m, by rw [execActions, hv, Option.bind_some]; exact hm, hme⟩

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

/-- A one-element operand list. -/
theorem Expr.evalList_singleton {sig : Signature} {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList sig [e] σ = some ts) : ∃ t, e.eval sig σ = some t ∧ ts = [t] := by
  rw [Expr.evalList] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.evalList, Option.map_some, Option.some.injEq] at h
  exact ⟨t, ht, h.symm⟩

/-- A two-element operand list: a view row's value tuple. -/
theorem Expr.evalList_pair {sig : Signature} {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList sig [e₁, e₂] σ = some ts) :
    ∃ t₁ t₂, e₁.eval sig σ = some t₁ ∧ e₂.eval sig σ = some t₂ ∧ ts = [t₁, t₂] := by
  rw [Expr.evalList] at h
  obtain ⟨t₁, ht₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨t₂, ht₂, rfl⟩ := Expr.evalList_singleton hus
  exact ⟨t₁, t₂, ht₁, ht₂, rfl⟩

/-- **The two rows one `encodeBuild` application writes**: the view row `@fView(is) ↦ (v, pf)`
and the term-relation row `@fTerm(is, v)`, at the key tuple `is` the arguments evaluated to and
the value `v` the naming expression evaluated to.

Existential in the proof column: which justification the entry carries is not what being the
entry is. Read as *entry terms*, not as current rows — `mergeOneOriented` overwrites a row and
`addTerm`s the survivor, and nothing in `Impl/` ever removes a term
(`mergeOneOriented_confined`, `mergeRound_confined`), so the row a rebuild displaced is still
the entry term `Database.Out` reads, and "the row is still current" would be false. -/
structure Database.HoldsBuild (d : Database) (f : FnName) (is : List Term) (v : Term) :
    Prop where
  /-- The view row. -/
  view : ∃ pf, Term.app (viewName f) (is ++ [v, pf]) ∈ d.terms
  /-- The term-relation row. -/
  term : Term.app (termName f) (is ++ [v]) ∈ d.terms

/-- Both rows are memberships, so they survive anything that only adds terms. -/
theorem Database.HoldsBuild.mono {d₁ d₂ : Database} (h : d₁.terms ⊆ d₂.terms)
    {f : FnName} {is : List Term} {v : Term} (hb : d₁.HoldsBuild f is v) :
    d₂.HoldsBuild f is v :=
  ⟨hb.view.imp fun _ hp => h hp, h hb.term⟩

/-- `Database.HoldsBuild.mono` along an inclusion of term *lists*, which is the form the
interpreter's monotonicity lemmas deliver. -/
theorem Database.HoldsBuild.monoF {d₁ d₂ : FDatabase} (h : ∀ t ∈ d₁.terms, t ∈ d₂.terms)
    {f : FnName} {is : List Term} {v : Term} (hb : d₁.toDatabase.HoldsBuild f is v) :
    d₂.toDatabase.HoldsBuild f is v :=
  hb.mono fun t ht => FDatabase.mem_toDatabase_terms.mpr
    (h t (FDatabase.mem_toDatabase_terms.mp ht))

/-- **One application's build, read back.** The block splits into the arguments' builds and the
two `set`s, and this is what the second half writes: the term row `@fTerm(is, v)` and the view
row `@fView(is) ↦ (v, pf)`, keyed on the arguments' values `is` and valued at whatever the
naming expression evaluated to. The view row's *subterms* come back too, since
`FDatabase.addTerm` inserts them and every consumer needs the key columns.

Both evaluations are taken in the state the block started in: a build emits `set`s only
(`encodeBuild_isSet`), so neither the signature nor the environment moves inside it. -/
theorem execActions_encodeBuild_app {f : FnName} {args : List Expr} {n : Nat}
    {d d' : FDatabase} (hrun : execActions d (encodeBuild (.app f args) n).2.1 = some d') :
    ∃ d₁ is v pf, execActions d (encodeBuildArgs args n).2.1 = some d₁ ∧
      d₁.sig = d.sig ∧ d₁.env = d.env ∧ (∀ t ∈ d₁.terms, t ∈ d'.terms) ∧
      Expr.evalList d.sig args d.env = some is ∧
      Expr.eval d.sig (.app f args) d.env = some v ∧
      (∀ s ∈ (Term.app (viewName f) (is ++ [v, pf])).subterms, s ∈ d'.terms) ∧
      Term.app (termName f) (is ++ [v]) ∈ d'.terms := by
  rw [encodeBuild_app_actions_eq] at hrun
  obtain ⟨d₁, hargs, htail⟩ := execActions_append hrun
  have hsig₁ : d₁.sig = d.sig := FDatabase.execActions_sig hargs
  have henv₁ : d₁.env = d.env := execActions_env_of_isSet (encodeBuildArgs_isSet args n) hargs
  rw [execActions] at htail
  obtain ⟨d₂, h₁, htail₂⟩ := Option.bind_eq_some_iff.mp htail
  rw [execActions] at htail₂
  obtain ⟨d₃, h₂', htail₃⟩ := Option.bind_eq_some_iff.mp htail₂
  rw [execActions, Option.some.injEq] at htail₃
  have h₂ : execAction d₂ (.set (viewName f) args [.app f args, fiatE]) = some d' :=
    h₂'.trans (congrArg some htail₃)
  obtain ⟨ks, kvs, hks, hkvs, rfl⟩ := execAction_set h₁
  obtain ⟨is, vs, his, hvs, rfl⟩ := execAction_set h₂
  simp only [FDatabase.addRow_sig, FDatabase.addRow_env, hsig₁, henv₁] at hks hkvs his hvs
  obtain ⟨v, pf, hv, -, rfl⟩ := Expr.evalList_pair hvs
  obtain ⟨is₀, vs₀, his₀, hvs₀, rfl⟩ := Expr.evalList_append hks
  obtain ⟨v₀, hv₀, rfl⟩ := Expr.evalList_singleton hvs₀
  obtain rfl : kvs = [] := (Option.some.inj hkvs).symm
  refine ⟨d₁, is, v, pf, hargs, hsig₁, henv₁, fun t ht => ?_, his, hv, fun s hs => ?_, ?_⟩
  · exact FDatabase.mem_addRow_terms.mpr (Or.inr (FDatabase.mem_addRow_terms.mpr (Or.inr ht)))
  · exact FDatabase.mem_addRow_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr hs))
  · refine FDatabase.mem_addRow_terms.mpr (Or.inr (FDatabase.mem_addRow_terms.mpr
      (Or.inl ((Term.mem_subtermList _).mpr ?_))))
    rw [Option.some.inj (his₀.symm.trans his), Option.some.inj (hv₀.symm.trans hv),
      List.append_nil]
    exact Term.self_mem_subterms _

mutual
/-- **The action read-back.** Once a build's actions have run, every application the built
expression applies has its two rows in the resulting state — keyed on the arguments' values and
valued at the application's own value, both evaluated in the state the block *started* in,
which is the state every one of its actions ran in.

No `encode` beyond `encodeBuild` and no `execM`: this is about one action block and the state it
ran from, so a top-level action (through `exists_execActions_of_execProgramM`) and a rule head
(`execLocalActions` *is* `execActions`) consume the same lemma. What it does not say is that the
rows are still the current ones: `mergeOneOriented` overwrites a row and `addTerm`s the
survivor, so what persists is the entry term, which is what `Database.Out` reads. -/
theorem holdsBuild_of_execActions : ∀ (e : Expr) (n : Nat) {d d' : FDatabase},
    execActions d (encodeBuild e n).2.1 = some d' →
    ∀ (f : FnName) (args : List Expr), (f, args) ∈ e.apps →
      ∃ is v, Expr.evalList d.sig args d.env = some is ∧
        Expr.eval d.sig (.app f args) d.env = some v ∧
        d'.toDatabase.HoldsBuild f is v
  | .lit _, _, _, _, _, _, _, hm => absurd hm (by simp [Expr.apps])
  | .var _, _, _, _, _, _, _, hm => absurd hm (by simp [Expr.apps])
  | .app f args, n, d, d', hrun, g, gargs, hm => by
      obtain ⟨d₁, is, v, pf, hargs, -, -, hmono, his, hv, hview, hterm⟩ :=
        execActions_encodeBuild_app hrun
      rw [Expr.apps, List.mem_cons] at hm
      rcases hm with hm | hm
      · obtain ⟨rfl, rfl⟩ : g = f ∧ gargs = args := by simpa using hm
        exact ⟨is, v, his, hv,
          ⟨⟨pf, FDatabase.mem_toDatabase_terms.mpr (hview _ (Term.self_mem_subterms _))⟩,
            FDatabase.mem_toDatabase_terms.mpr hterm⟩⟩
      · obtain ⟨is', v', hk', hv', hb'⟩ :=
          holdsBuildArgs_of_execActions args n hargs g gargs hm
        exact ⟨is', v', hk', hv', hb'.monoF hmono⟩

@[inherit_doc holdsBuild_of_execActions]
theorem holdsBuildArgs_of_execActions : ∀ (es : List Expr) (n : Nat) {d d' : FDatabase},
    execActions d (encodeBuildArgs es n).2.1 = some d' →
    ∀ (f : FnName) (args : List Expr), (f, args) ∈ Expr.appsList es →
      ∃ is v, Expr.evalList d.sig args d.env = some is ∧
        Expr.eval d.sig (.app f args) d.env = some v ∧
        d'.toDatabase.HoldsBuild f is v
  | [], _, _, _, _, _, _, hm => absurd hm (by simp [Expr.appsList])
  | e :: es, n, d, d', hrun, g, gargs, hm => by
      rw [encodeBuildArgs_cons_actions] at hrun
      obtain ⟨d₁, hhead, htail⟩ := execActions_append hrun
      have hsig₁ : d₁.sig = d.sig := FDatabase.execActions_sig hhead
      have henv₁ : d₁.env = d.env := execActions_env_of_isSet (encodeBuild_isSet e n) hhead
      rw [Expr.appsList, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨is, v, hk, hv, hb⟩ := holdsBuild_of_execActions e n hhead g gargs hm
        exact ⟨is, v, hk, hv, hb.monoF (FDatabase.execActions_lists htail).1⟩
      · obtain ⟨is, v, hk, hv, hb⟩ :=
          holdsBuildArgs_of_execActions es (encodeBuild e n).2.2 htail g gargs hm
        rw [hsig₁, henv₁] at hk hv
        exact ⟨is, v, hk, hv, hb⟩
end

/-! #### From the rows to the reading -/

/-- A non-primitive application evaluates to its head applied to the arguments' values. -/
theorem Expr.eval_app_of_noPrim {sig : Signature} {σ : Env} {f : FnName} {args : List Expr}
    {t : Term} (hp : Prim.ofName f = none) (h : (Expr.app f args).eval sig σ = some t) :
    ∃ is, Expr.evalList sig args σ = some is ∧ t = .app f is := by
  simp only [Expr.eval, hp] at h
  split at h
  · obtain ⟨is, his, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨is, his, rfl⟩
  · exact absurd h (by simp)

mutual
/-- **A build's own term reads to itself at any state the run passes to.** The read-back turned
into `ViewRepr`, which is what `Database.UnionsJoined.readsSelf` asks for and what a `SameClass`
is two of.

`D` is any state the block's result state is contained in, so this survives everything the rest
of the run does — `FDatabase.execProgramM_terms` is that inclusion, and it is the whole of what
`D` has to satisfy.

The two side hypotheses are exactly the two leaves a build emits no action for. `hprim` is
`Program.EncodeDomain.noPrim`: a source name shadowing a primitive would make the value column
the primitive's *result* rather than the application, and the entry would be keyed on nothing
the source built. `hvar` is the earlier top-level `let`s' own read-back — a variable's value gets
no row from *this* build. A bare literal is why the statement carries `hmem`: nothing at all is
emitted for it, which is what `litBuild_not_viewsCover` refutes and
`Cmd.NoBareBuild` excludes. -/
theorem viewRepr_self_of_execActions : ∀ (e : Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuild e n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ e.fns, Prim.ofName g = none) →
    (∀ w ∈ e.vars, ∀ u, Env.lookup w d.env = some u → ViewRepr D.toDatabase u u) →
    ∀ t, e.eval d.sig d.env = some t → t ∈ D.toDatabase.terms → ViewRepr D.toDatabase t t
  | .lit l, _, _, _, _, _, _, _, _, t, hev, hmem => by
      obtain rfl : Term.lit l = t := Option.some.inj hev
      exact .lit hmem
  | .var w, _, _, _, _, _, _, _, hvar, t, hev, _ => hvar w (by simp [Expr.vars]) t hev
  | .app f args, n, d, d', D, hrun, hD, hprim, hvar, t, hev, _ => by
      obtain ⟨d₁, is, v, pf, hargs, hsig₁, henv₁, hmono, his, hv, hview, -⟩ :=
        execActions_encodeBuild_app hrun
      have hvapp : v = Term.app f is := by
        obtain ⟨is', his', hveq⟩ := Expr.eval_app_of_noPrim (hprim f (by simp [Expr.fns])) hv
        rw [hveq, Option.some.inj (his'.symm.trans his)]
      have htv : t = Term.app f is := (Option.some.inj (hev.symm.trans hv)).trans hvapp
      rw [hvapp] at hview
      subst htv
      have hmemis : ∀ i ∈ is, i ∈ D.toDatabase.terms := fun i hi =>
        FDatabase.mem_toDatabase_terms.mpr (hD _ (hview i
          (Term.arg_subterms (List.mem_append_left _ hi) (Term.self_mem_subterms i))))
      refine .app (viewReprList_self_of_execActions args n hargs
        (fun x hx => hD x (hmono x hx)) (fun g hg => hprim g (by simp [Expr.fns, hg]))
        (fun w hw u hu => hvar w (by simpa [Expr.vars] using hw) u hu) is his hmemis)
        ⟨is, CongList.refl hmemis, FDatabase.mem_toDatabase_terms.mpr
          (hD _ (hview _ (Term.self_mem_subterms _)))⟩

@[inherit_doc viewRepr_self_of_execActions]
theorem viewReprList_self_of_execActions : ∀ (es : List Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuildArgs es n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
    (∀ w ∈ Expr.varsList es, ∀ u, Env.lookup w d.env = some u → ViewRepr D.toDatabase u u) →
    ∀ ts, Expr.evalList d.sig es d.env = some ts → (∀ t ∈ ts, t ∈ D.toDatabase.terms) →
      ViewReprList D.toDatabase ts ts
  | [], _, _, _, _, _, _, _, _, ts, hev, _ => by
      obtain rfl : ([] : List Term) = ts := Option.some.inj hev
      exact .nil
  | e :: es, n, d, d', D, hrun, hD, hprim, hvar, ts, hev, hmem => by
      rw [encodeBuildArgs_cons_actions] at hrun
      obtain ⟨d₁, hhead, htail⟩ := execActions_append hrun
      have hsig₁ : d₁.sig = d.sig := FDatabase.execActions_sig hhead
      have henv₁ : d₁.env = d.env := execActions_env_of_isSet (encodeBuild_isSet e n) hhead
      rw [Expr.evalList] at hev
      obtain ⟨t, ht, hev⟩ := Option.bind_eq_some_iff.mp hev
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp hev
      refine .cons (viewRepr_self_of_execActions e n hhead
          (fun x hx => hD x ((FDatabase.execActions_lists htail).1 x hx))
          (fun g hg => hprim g (by simp [Expr.fnsList, hg]))
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u hu) t ht
          (hmem t List.mem_cons_self))
        (viewReprList_self_of_execActions es (encodeBuild e n).2.2 htail hD
          (fun g hg => hprim g (by simp [Expr.fnsList, hg]))
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u
            (by rw [henv₁] at hu; exact hu))
          ts' (by rw [hsig₁, henv₁]; exact hts')
          fun x hx => hmem x (List.mem_cons_of_mem _ hx))
end

/-! #### From an action block to a run of top-level commands -/

/-- **Two runs of the same block of `set`s agree on what they write.** `Expr.eval` reads the
signature and the environment and nothing else, so the run from a *smaller* state — same
signature, same environment, fewer terms — succeeds wherever the larger one does and writes the
same entry terms. This is what lets a block's own `execActions` run stand in for `execProgramM`
over the block's `Cmd.action`s, where each command is followed by its own merge phase. -/
theorem execActions_parallel {as : List Action} (hs : ∀ a ∈ as, a.IsSet) :
    ∀ {d₁ d₂ e₂ : FDatabase}, d₂.sig = d₁.sig → d₂.env = d₁.env →
      (∀ t ∈ d₁.terms, t ∈ d₂.terms) → execActions d₂ as = some e₂ →
      ∃ e₁, execActions d₁ as = some e₁ ∧ (∀ t ∈ e₁.terms, t ∈ e₂.terms) := by
  induction as with
  | nil =>
    intro d₁ d₂ e₂ _ _ hmem h
    rw [execActions, Option.some.injEq] at h
    exact ⟨d₁, rfl, h ▸ hmem⟩
  | cons a as ih =>
    intro d₁ d₂ e₂ hsig henv hmem h
    match a, hs a List.mem_cons_self with
    | .set f args out, _ =>
      rw [execActions] at h
      obtain ⟨m₂, hm₂, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ks, vs, hks, hvs, rfl⟩ := execAction_set hm₂
      rw [hsig, henv] at hks hvs
      have hm₁ : execAction d₁ (.set f args out) = some (FDatabase.addRow f ks vs d₁) := by
        simp only [execAction, hks, hvs, Option.bind_some, Option.map_some]
      obtain ⟨e₁, he₁, hmem₁⟩ :=
        ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
          (d₁ := FDatabase.addRow f ks vs d₁) (d₂ := FDatabase.addRow f ks vs d₂)
          (by simp only [FDatabase.addRow_sig]; exact hsig)
          (by simp only [FDatabase.addRow_env]; exact henv)
          (fun t ht => FDatabase.mem_addRow_terms.mpr
            ((FDatabase.mem_addRow_terms.mp ht).imp id (hmem t))) hrest
      exact ⟨e₁, by rw [execActions, hm₁, Option.bind_some]; exact he₁, hmem₁⟩

/-- **A block of top-level `set` commands runs the block.** `execCmdM` follows each action with a
merge phase, which adds terms and moves neither the signature nor the environment
(`FDatabase.mergeSaturateF_terms`, `mergeSaturateF_fields`), so `execActions_parallel` carries
the block's own `execActions` run along it. -/
theorem exists_execActions_of_execProgramM {as : List Action} (hs : ∀ a ∈ as, a.IsSet) :
    ∀ {d D : FDatabase}, d.execProgramM (as.map Cmd.action) = some D →
      ∃ e, execActions d as = some e ∧ (∀ t ∈ e.terms, t ∈ D.terms) := by
  induction as with
  | nil =>
    intro d D h
    rw [List.map_nil, FDatabase.execProgramM, Option.some.injEq] at h
    exact ⟨d, rfl, h ▸ fun _ ht => ht⟩
  | cons a as ih =>
    intro d D h
    rw [List.map_cons, FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [FDatabase.execCmdM] at h₁
    obtain ⟨d₀, hact, hmerge⟩ := Option.bind_eq_some_iff.mp h₁
    obtain ⟨e₁, he₁, hmem₁⟩ := ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h₂
    obtain ⟨hsig, henv, -⟩ := FDatabase.mergeSaturateF_fields hmerge
    obtain ⟨e₀, he₀, hmem₀⟩ :=
      execActions_parallel (fun b hb => hs b (List.mem_cons_of_mem _ hb))
        (d₁ := d₀) (d₂ := d₁) hsig henv (FDatabase.mergeSaturateF_terms hmerge) he₁
    exact ⟨e₀, by rw [execActions, hact, Option.bind_some]; exact he₀,
      fun t ht => hmem₁ t (hmem₀ t ht)⟩

/-- **The action read-back at a run of top-level commands.** The build's `set`s are the block's
own `Cmd.action`s, `p` is everything the run does after them, and the rows are in the state it
finishes at: `exists_execActions_of_execProgramM` reduces the block to one `execActions` run and
`FDatabase.execProgramM_terms` carries the entry terms through the rest — the rebuild's
`Cmd.saturate` included, since a merge phase deletes rows and never a term.

This is the form an induction over `encode P`'s commands consumes, one top-level
`.action (.expr e)` at a time: `encodeCmd` emits exactly
`(encodeBuild e n).2.1.map Cmd.action ++ [Cmd.saturate rebuildRuleset]`. -/
theorem holdsBuild_of_execProgramM (e : Expr) (n : Nat) {d D : FDatabase} {p : Program}
    (hrun : d.execProgramM ((encodeBuild e n).2.1.map Cmd.action ++ p) = some D) :
    ∀ (f : FnName) (args : List Expr), (f, args) ∈ e.apps →
      ∃ is v, Expr.evalList d.sig args d.env = some is ∧
        Expr.eval d.sig (.app f args) d.env = some v ∧
        D.toDatabase.HoldsBuild f is v := by
  obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  obtain ⟨m, hm, hmem⟩ := exists_execActions_of_execProgramM (encodeBuild_isSet e n) hblock
  intro f args hfa
  obtain ⟨is, v, his, hv, hb⟩ := holdsBuild_of_execActions e n hm f args hfa
  exact ⟨is, v, his, hv,
    hb.monoF fun t ht => FDatabase.execProgramM_terms hafter t (hmem t ht)⟩

@[inherit_doc holdsBuild_of_execProgramM]
theorem viewRepr_self_of_execProgramM (e : Expr) (n : Nat) {d D : FDatabase} {p : Program}
    (hrun : d.execProgramM ((encodeBuild e n).2.1.map Cmd.action ++ p) = some D)
    (hprim : ∀ g ∈ e.fns, Prim.ofName g = none)
    (hvar : ∀ w ∈ e.vars, ∀ u, Env.lookup w d.env = some u → ViewRepr D.toDatabase u u)
    {t : Term} (hev : e.eval d.sig d.env = some t) (hmem : t ∈ D.toDatabase.terms) :
    ViewRepr D.toDatabase t t := by
  obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  obtain ⟨m, hm, hmm⟩ := exists_execActions_of_execProgramM (encodeBuild_isSet e n) hblock
  exact viewRepr_self_of_execActions e n hm
    (fun x hx => FDatabase.execProgramM_terms hafter x (hmm x hx)) hprim hvar t hev hmem

/-! #### The read-back is not vacuous

`ENCODING.md`'s discipline again: a lemma whose premise nothing satisfies proves nothing. Here
is the read-back run, at the signature `encode satProgram`'s prelude installs plus a unary `W`'s
table triple. Two builds, and the second's operand is a **variable** — so the `hvar` hypothesis
of `viewRepr_self_of_execActions` is discharged non-vacuously, by the first build's own reading,
which is exactly the shape the missing command induction has to carry. -/

/-- `satSig` with a unary `W`'s table triple added. -/
def rbSig : Signature :=
  Function.update (Function.update (Function.update satSig
    "W" (some (skolemDecl 1))) (viewName "W") (some (viewDecl 1)))
    (termName "W") (some (termDecl 1))

/-- The state the prelude leaves: declarations and nothing built. -/
def rbState : FDatabase := { FDatabase.empty with sig := rbSig }

/-- After `(A)`'s build: its two rows and their subterms, four terms. -/
def rbState1 : FDatabase :=
  (execActions rbState (encodeBuild (.app "A" []) 0).2.1).getD FDatabase.empty

theorem rbState1_eq : execActions rbState (encodeBuild (.app "A" []) 0).2.1 = some rbState1 :=
  rfl

/-- A global binding `x ↦ (A)`, as a top-level `let` leaves it. -/
def rbEnv : Env := [("x", Term.app "A" [])]

/-- After `(W x)`'s build, in that environment: seven terms. -/
def rbState2 : FDatabase :=
  (execActions { rbState1 with env := rbEnv }
    (encodeBuild (.app "W" [.var "x"]) 0).2.1).getD FDatabase.empty

theorem rbState2_eq : execActions { rbState1 with env := rbEnv }
    (encodeBuild (.app "W" [.var "x"]) 0).2.1 = some rbState2 := rfl

/-- **`(A)`'s build reads to itself, at the *later* state.** The `D` parameter of
`viewRepr_self_of_execActions` doing its job: the reading survives the second build. -/
theorem rbState2_viewRepr_A : ViewRepr rbState2.toDatabase (.app "A" []) (.app "A" []) :=
  viewRepr_self_of_execActions (.app "A" []) 0 rbState1_eq (by decide) (by decide)
    (fun w hw => absurd hw (by simp [Expr.vars, Expr.varsList])) _ rfl
    (FDatabase.mem_toDatabase_terms.mpr (by decide))

/-- **And `(W x)`'s build reads to itself**, with `hvar` discharged at the variable `x` by the
reading above. This is the composition the residues below still need an induction to perform
once per command. -/
theorem rbState2_viewRepr_W :
    ViewRepr rbState2.toDatabase (.app "W" [.app "A" []]) (.app "W" [.app "A" []]) :=
  viewRepr_self_of_execActions (.app "W" [.var "x"]) 0 rbState2_eq (fun _ h => h) (by decide)
    (fun w hw u hu => by
      obtain rfl : w = "x" := by simpa [Expr.vars, Expr.varsList] using hw
      obtain rfl : u = Term.app "A" [] := by simpa [rbEnv, Env.lookup] using hu.symm
      exact rbState2_viewRepr_A)
    _ rfl (FDatabase.mem_toDatabase_terms.mpr (by decide))

/-- **And the rows themselves come back**, keyed on the variable's value: `@WView((A)) ↦
(W((A)), @Fiat)` and `@WTerm((A), W((A)))`. `Expr.apps` is what indexes them, and it is
non-empty here. -/
theorem rbState2_holdsBuild : rbState2.toDatabase.HoldsBuild "W" [Term.app "A" []]
    (Term.app "W" [Term.app "A" []]) := by
  obtain ⟨is, v, hk, hv, hb⟩ :=
    holdsBuild_of_execActions (.app "W" [.var "x"]) 0 rbState2_eq "W" [.var "x"]
      (by simp [Expr.apps])
  obtain rfl : is = [Term.app "A" []] := Option.some.inj hk.symm
  obtain rfl : v = Term.app "W" [Term.app "A" []] := Option.some.inj hv.symm
  exact hb

/-! #### The three residues

One `sorry` each, and each of the three is a property of the state `execM` returned rather
than a restatement of an obligation. All three hold at `witnessProgram`, the program the
vacuity witness at the end of this file is stated over; `difftest correspond-dump 64 union`
prints the state and its `reprs`/`leaders` block is the reading.

* `Database.ViewLeader` — `leaders` is a single term for every source term: `(One)` for
  `(One)` and for `(Two)`, `(Add (One) (Two))` for both `Add`s. `difftest correspond`'s
  `leader-diff` column is the same reading over the whole corpus, and it is 0.
* `Database.ViewsCover` — the three `@AddView` keys are exactly the product of the two
  children's `reprs`, and the source holds no literal.
* `Database.UnionsRead` — `reprs` of `(One)` and of `(Two)` share `(One)`.

So none of the three is a hypothesis nothing reachable satisfies, which is the failure
`ENCODING.md` records twice.

What all three still need is one missing piece in three shapes: an invariant carried through
`FDatabase.execProgramM` that reads the encoded program's *own* commands — the two `set`s per
build, the `@UF` edge per `union`, and the `Cmd.saturate rebuildRuleset` after each. The
nearest thing the library has is `execM_contained`, and it does not reach: it is proved under
`Program.NoSaturate`, and `encode` emits a `Cmd.saturate` after every command that writes.

**What the section above supplies, and what is left.** The action read-back is proved: at a
block of a build's own commands, both of its rows are entry terms of whatever the run finishes
at (`holdsBuild_of_execProgramM`), and they assemble into the reading
(`viewRepr_self_of_execProgramM`). What no lemma here supplies is the **induction over
`encode P`'s commands** that finds, for each source term, the block that built it. Two things
make that induction more than bookkeeping, and each residue below names the ones it needs:

* a source term built by a **rule firing** needs the source's firing to have a target firing
  behind it, which is the *opposite* direction from `exists_validQuerySubst_of_encodeQuery`;
* a source term reached through a **variable** needs the earlier `let`'s own read-back, which
  is the `hvar` hypothesis of `viewRepr_self_of_execActions` and is what the induction's
  hypothesis has to carry.

**Two of these statements were false before `Program.EncodeDomain.noBareBuild`**, and the
refutation is compiled below: `litBuild_not_viewsCover` and `litBuild_not_readsSelf` at
`litBuildProgram`, one `.action (.expr (.lit 5))`, which satisfied every other clause of the
domain (`litBuildProgram_domain_but_bare`). -/

/-! #### The bare-leaf refutation

`ENCODING.md`'s discipline: a residue that is *false* must not stand as a `sorry`. Two of the
three below were, at a program the domain admitted, and this is the state that shows it. -/

/-- One top-level action that builds a bare literal, and its constructor-free program. -/
def litBuildProgram : Program := [.action (.expr (.lit (.int 5)))]

/-- **Every clause of `Program.EncodeDomain` but `noBareBuild` holds of it**, so the clause is
not implied by the rest. -/
theorem litBuildProgram_domain_but_bare :
    (∀ c ∈ litBuildProgram, ∀ f d, c = Cmd.decl f d → d.merge = none) ∧
      (∀ c ∈ litBuildProgram, c.NoSet) ∧
      (∀ fk ∈ litBuildProgram.ctors, Prim.ofName fk.1 = none) ∧
      (∀ fk ∈ litBuildProgram.ctors, ¬ "@".isPrefixOf fk.1) ∧
      (∀ v ∈ litBuildProgram.vars, ¬ "@".isPrefixOf v) ∧
      (∀ R ∈ litBuildProgram.rulesets, ¬ "@".isPrefixOf R) ∧
      (∀ c ∈ litBuildProgram, c.NoLeafPattern) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [litBuildProgram, Program.ctors, Cmd.ctors, Action.ctors, Expr.ctors, Program.vars,
      Cmd.vars, Action.vars, Expr.vars, Program.rulesets, Cmd.rulesets, Cmd.NoSet,
      Action.NoSet, Cmd.NoLeafPattern]

/-- **And `noBareBuild` is the clause it fails.** -/
theorem litBuildProgram_not_encodeDomain : ¬ litBuildProgram.EncodeDomain := by
  intro h
  exact h.noBareBuild (.action (.expr (.lit (.int 5)))) (by simp [litBuildProgram])

/-- The state the one action reaches: the literal, and nothing else. -/
def litBuildSrc : Database := Database.empty.addTerm (.lit (.int 5))

theorem litBuildProgram_programStep : ProgramStep Database.empty litBuildProgram litBuildSrc :=
  .cons ⟨litBuildSrc, rfl, .refl⟩ .nil

theorem litBuildSrc_mem : Term.lit (.int 5) ∈ litBuildSrc.terms :=
  Cong.assert (by simp [litBuildSrc, Database.addTerm, Database.empty])

/-- **The encoded run holds nothing at all.** `encodeBuild` emits no action for a leaf, so the
six commands `encode` produces are five declarations and a rebuild that fires nothing. -/
theorem execM_litBuild_terms :
    (execM (encode litBuildProgram)).map FDatabase.terms = some [] := rfl

theorem litBuild_terms {tgt : FDatabase} (htgt : execM (encode litBuildProgram) = some tgt) :
    tgt.terms = [] := by
  have h := execM_litBuild_terms
  rw [htgt] at h
  exact Option.some.inj h

/-- **The literal has no reading at all in the target.** -/
theorem litBuild_not_viewRepr {tgt : FDatabase}
    (htgt : execM (encode litBuildProgram) = some tgt) (e : Term) :
    ¬ ViewRepr tgt.toDatabase (.lit (.int 5)) e := by
  intro h
  match h with
  | .lit hm =>
    rw [FDatabase.mem_toDatabase_terms, litBuild_terms htgt] at hm
    exact absurd hm (by simp)

/-- **`Database.ViewsCover` is false at an `execM` target of an in-domain-but-for-`noBareBuild`
program.** The source holds the literal and the target holds nothing, so the `lits` clause
fails — which is why `Program.EncodeDomain.noBareBuild` exists. -/
theorem litBuild_not_viewsCover {tgt : FDatabase}
    (htgt : execM (encode litBuildProgram) = some tgt) :
    ¬ tgt.toDatabase.ViewsCover litBuildSrc := by
  intro h
  have hm := h.lits (.int 5) litBuildSrc_mem
  rw [FDatabase.mem_toDatabase_terms, litBuild_terms htgt] at hm
  exact absurd hm (by simp)

/-- **And so is `Database.UnionsJoined.readsSelf`.** -/
theorem litBuild_not_readsSelf {tgt : FDatabase}
    (htgt : execM (encode litBuildProgram) = some tgt) :
    ¬ tgt.toDatabase.UnionsJoined litBuildSrc := fun h =>
  litBuild_not_viewRepr htgt _ (h.readsSelf _ litBuildSrc_mem)

/-- **The forward half itself is false there**: the source asserts the literal's reflexive
equation and the target has no reading of it, so `Cong src a a` holds where
`SameClass tgt a a` does not. This is what `noBareBuild` buys, and it is why the clause is a
domain restriction rather than a convenience. -/
theorem litBuild_forward_false {tgt : FDatabase}
    (htgt : execM (encode litBuildProgram) = some tgt) :
    Cong litBuildSrc (.lit (.int 5)) (.lit (.int 5)) ∧
      ¬ SameClass tgt.toDatabase (.lit (.int 5)) (.lit (.int 5)) :=
  ⟨litBuildSrc_mem, fun h => litBuild_not_viewRepr htgt h.choose h.choose_spec.1⟩

/-! #### The three residues, by clause -/

/-- **The residue of obligation `trans`. Not proved.**

What is missing: that the ids a source term reads to at an `execM` target are `@UF`-connected
and that the connection has a unique endpoint. Two entries at one view key collide, and
`mergeBody` writes the edge between their e-class columns; `rebuildRules`' e-class rule
follows an edge, so an id's `lead` is read by every term that reads the id;
`pathCompressRule` is what makes the endpoint unique. All three are *specification* rules
fired to saturation, and the hypothesis here is an `execM` target — so what it has to be
proved from is `FDatabase.runSaturateM`'s own fixpoint, and that is strictly weaker than
`RunSaturated` (`execM_contained`: the enumerator under-fires). -/
theorem execM_viewLeader {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewLeader := by
  sorry

/-- **`Database.ViewsCover.lits`, at an `execM` target. Not proved**, and *false* without
`Program.EncodeDomain.noBareBuild` — `litBuild_not_viewsCover` is the refutation, and this is
the clause it refutes.

What is missing: the induction over `encode P`'s commands. With the domain clause every source
term is built by an action whose expression is an application or bound by a `let`, so a literal
the source holds is a key column of some view row the target wrote
(`execActions_encodeBuild_app` returns the row's *subterms* for exactly this reason) — but
which row that is comes from the induction, and a literal reached through a rule firing needs
the firing's target counterpart, which this file does not have. -/
theorem execM_viewsCover_lits {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ l : Lit, Term.lit l ∈ src.terms → Term.lit l ∈ tgt.toDatabase.terms := by
  sorry

/-- **`Database.ViewsCover.keyed`, at an `execM` target. Not proved**, and the one residue that
needs *both* halves of the missing mechanism.

The read-back gives the entry at the key the build itself wrote — the tuple where each child
reads to itself (`holdsBuild_of_execProgramM`). `keyed` asks for an entry at *every* tuple of
ids the children are given, which is the product `rebuildRules`' column rules cover, so what is
missing beyond the induction is `FDatabase.runSaturateM`'s own fixpoint — the same thing
`execM_viewLeader` and `execM_eclassFollowed` need. -/
theorem execM_viewsCover_keyed {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ f as es, Term.app f as ∈ src.terms → ViewReprList tgt.toDatabase as es →
      ∃ e pf, tgt.toDatabase.Out (viewName f) es [e, pf] := by
  sorry

/-- **The residue of obligations `congr` and of `assert`'s reflexive half**, assembled from its
two clauses. -/
theorem execM_viewsCover {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewsCover src :=
  ⟨execM_viewsCover_lits hdom hsrc htgt, execM_viewsCover_keyed hdom hsrc htgt⟩

/-- **`Database.UnionsJoined.readsSelf`, at an `execM` target. Not proved**, and *false*
without `Program.EncodeDomain.noBareBuild` — `litBuild_not_readsSelf` is the refutation.

**This is the clause the action read-back is for, and the read-back is proved.**
`viewRepr_self_of_execProgramM` is exactly this statement for *one* build's block: the block's
`set`s ran, the rows are entry terms of the state the run finishes at, and they assemble into
`ViewRepr tgt t t`. What is missing is only the induction over `encode P`'s commands, and it
needs two things this file does not have: the `hvar` hypothesis carried along the run — a
variable's value gets its rows from whichever earlier build bound it — and, for a term a source
rule built, a target firing behind the source firing, which is the opposite direction from
`exists_validQuerySubst_of_encodeQuery`. -/
theorem execM_readsSelf {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ t ∈ src.terms, ViewRepr tgt.toDatabase t t := by
  sorry

/-- **`Database.UnionsJoined.edges`, at an `execM` target. Not proved.**

The same shape as `execM_readsSelf` and the same missing induction, at `encodeAction`'s
`union` case rather than at `encodeBuild`: the emitted action is
`.set @UF [ordering-max x₁ x₂] [ordering-min x₁ x₂, pf]`, so `execAction_set` reads the row
back off it just as `execActions_encodeBuild_app` does for a build, and the disjunction is
which endpoint `ordering-max` picked. Not proved because the *`union` is not the last action of
its block* — the two operands' builds precede it — so the read-back has to be threaded through
`execActions_append` at `encodeAction`'s shape, and then the same command induction applies. -/
theorem execM_edges {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
      (∃ pf, tgt.toDatabase.Out ufName [a] [b, pf]) ∨
        (∃ pf, tgt.toDatabase.Out ufName [b] [a, pf]) := by
  sorry

/-- **`Database.UnionsJoined.eclassFollowed`, at an `execM` target. Not proved**, and the one
clause of the three that is a *fixpoint* claim rather than a read-back of an emitted action.

`rebuildRules`' e-class rule re-`set`s a view entry at the `@UF` parent of its e-class column,
and what has to be shown is that `FDatabase.runSaturateM` ran it — which is the same thing
`execM_viewLeader` and `execM_viewsCover_keyed` need and is strictly weaker than `RunSaturated`
(`execM_contained`: the enumerator under-fires). The action read-back says nothing about it:
no `set` the encoder emitted writes this row. -/
theorem execM_eclassFollowed {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ t p pf, t ∈ src.terms → ViewRepr tgt.toDatabase t t →
      tgt.toDatabase.Out ufName [t] [p, pf] → ViewRepr tgt.toDatabase t p := by
  sorry

/-- **The residue of obligation `assert`'s `union` half**, assembled from the three things it
needs (`Database.UnionsJoined`) rather than left as the obligation restated.

Two of the three are the action read-back and one is the rebuild: `execM_readsSelf` is
`encodeBuild`'s view `set` having run for every source term, `execM_edges` is `encodeAction`'s
`@UF` set having run for every source `union`, and `execM_eclassFollowed` is
`FDatabase.runSaturateM`'s fixpoint having followed the edge into the endpoint's own view row —
the same rebuild `execM_viewLeader` needs.

**All three hold at a state a program reaches, and two of them non-vacuously**:
`unionsJoined_witness` in `Encoding/Match.lean`, over `uProgram`, whose rule head unions two
distinct terms. `uTgt_not_unionsRead` there is the same three clauses one rebuild firing
*earlier*, where `eclassFollowed` fails and the conclusion with it — so the clause is
load-bearing and not decoration. -/
theorem execM_unionsJoined {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.UnionsJoined src :=
  ⟨execM_readsSelf hdom hsrc htgt, execM_edges hdom hsrc htgt,
    execM_eclassFollowed hdom hsrc htgt⟩

@[inherit_doc execM_unionsJoined]
theorem execM_unionsRead {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.UnionsRead src :=
  unionsRead_of_unionsJoined (execM_unionsJoined hdom hsrc htgt)

/-- **Obligation `assert`, at the encoding**, split by writer. `Database.addTerm` writes a
reflexive equation per subterm built, and `sameClass_self_of_viewsCover` discharges those out
of `execM_viewsCover`; `evalAction`'s `union` is the only other writer the source fragment
has, and `execM_unionsRead` is it. **Proved from the two residues.** -/
theorem encode_assert {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b : Term) (h : (a, b) ∈ src.eqs) : SameClass tgt.toDatabase a b := by
  by_cases hab : a = b
  · subst hab
    exact sameClass_self_of_viewsCover (execM_viewsCover hdom hsrc htgt)
      (hsrc.wf Database.WF.empty) h
  · exact execM_unionsRead hdom hsrc htgt a b h hab

/-- **Obligation `trans`, at the encoding. Proved from `execM_viewLeader`.** Not from the
view's functional dependency, which is false at this file's own witness — the section header
above has the refutation. -/
theorem encode_trans {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (_hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b c : Term) (hab : SameClass tgt.toDatabase a b) (hbc : SameClass tgt.toDatabase b c) :
    SameClass tgt.toDatabase a c :=
  SameClass.trans_of_viewLeader (execM_viewLeader hdom htgt) hab hbc

/-- **Obligation `congr`, at the encoding. Proved from `execM_viewsCover`.** The pointwise
hypothesis is one shared id tuple, and `ViewsCover.keyed` is the view entry at it — the
rebuild's whole contribution, isolated. The second self-congruence premise is unused. -/
theorem encode_congr {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (f : FnName) (as bs : List Term) (ha : Cong src (.app f as) (.app f as))
    (_hb : Cong src (.app f bs) (.app f bs))
    (hl : List.Forall₂ (SameClass tgt.toDatabase) as bs) :
    SameClass tgt.toDatabase (.app f as) (.app f bs) :=
  sameClass_congr_of_keyed (execM_viewsCover hdom hsrc htgt) ha hl


/-- **No equality is lost**: assembled from the three obligations, with `symm` free. -/
theorem encode_corresponds_forward {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (h : Cong src a b) :
    SameClass tgt.toDatabase a b :=
  cong_sameClass ⟨encode_assert hdom hsrc htgt, encode_trans hdom hsrc htgt,
    encode_congr hdom hsrc htgt⟩ h

/-! ### The completeness half

`SameClass` is flat — `∃ e, ViewRepr d a e ∧ ViewRepr d b e` — so this half needs no
induction on the target side at all. It reduces to a single **no-junk** invariant on the
target, and `sameClass_cong_of_state` is that reduction: no `encode`, no `execM`, one
property of the state, exactly the shape `cong_sameClass_of_state` has for the forward half.

**The obvious form of the invariant is false, and so is the obvious statement of this half.**
"Every id a term reads is congruent to it" is not what an `execM` target satisfies: the
rebuild's column rules re-key an entry onto its children's leaders and nothing is ever
removed, so `difftest correspond-dump 64 union` prints, for `witnessProgram`,

```
  view @AddView((One), (One)) ↦ (Add (One) (Two))
```

and `(Add One One)` is a term the source never built — `Cong src` relates it to nothing, its
own self included, since `Cong.congr` needs both sides self-congruent and no other rule
produces an application. So the target hands `(Add One One)` an e-class the source has no
e-node for: `SameClass tgt (Add One One) (Add One One)` holds where
`Cong src (Add One One) (Add One One)` fails, and **`SameClass tgt a b → Cong src a b` is
refuted at this file's own witness program**. `encode_corresponds_invents_enode` is that
refutation, its two measurements decided by `difftest correspond-selftest`.

The corpus sweep does not see it because its universe is `src.terms ++ tgt.terms` and
`(Add One One)` is in neither: it is a *key tuple* of an entry term, not a subterm of one. So
`difftest correspond`'s 0 INVENTED is a claim about the source's own e-nodes, and that is
what the statement below is restricted to — `a ∈ src.terms` and `b ∈ src.terms`, which
`Cong src a b` implies anyway, so the forward half pays nothing for them.

The other repair, not taken: conclude `CongOn src [a, b] a b` instead of `Cong src a b`.
`withOperands` records the missing e-node and adds no equation between distinct terms, so the
invented class is congruent *there* — but then the two halves of `encode_corresponds` are
relations over different sources, and `ENCODING.md` records why `CongOn` is too weak to state
this correspondence over. -/

/-- One column of the right-hand list moved along a congruence. What the rebuild's column
rules do to a key, pointwise. -/
theorem CongList.setAt {db : Database} {as cs : List Term} {c x : Term} (i : Nat)
    (h : CongList db as cs) (hget : cs[i]? = some c) (hcx : Cong db c x) :
    CongList db as (cs.set i x) := by
  rw [CongList.forall₂] at h ⊢
  induction i generalizing as cs with
  | zero =>
    cases h with
    | nil => simp at hget
    | cons hab hl =>
      obtain rfl : _ = c := by simpa using hget
      simpa using List.Forall₂.cons (hab.trans hcx) hl
  | succ n ih =>
    cases h with
    | nil => simp at hget
    | cons hab hl => simpa using List.Forall₂.cons hab (ih hl (by simpa using hget))

/-- **What one view entry claims about the source**: `f` applied to *some* source term list
that reads the key `cs` is congruent to the entry's e-class column `e`.

Existential in `as`, and that is the whole of why the invariant is this and not "`f` applied
to `cs` is congruent to `e`". The latter is the false reading refuted above:
`@AddView(One,One) ↦ (Add One Two)` is an entry no source application of `Add` keys, and two
that *read* it — `(Add One Two)` and `(Add Two One)`. The universal reading over source
applications follows (`EntrySound.cong_of_congList`); the reading at the key itself does
not. -/
def EntrySound (src : Database) (f : FnName) (cs : List Term) (e : Term) : Prop :=
  ∃ as, Term.app f as ∈ src.terms ∧ CongList src as cs ∧ Cong src (.app f as) e

/-- **Any source application that reads the key is congruent to the e-class column**, from
the one that witnesses the entry: the two argument lists are congruent through the key, so
the two applications are. This is the only place `Cong.congr` is used, and the two
self-congruences it wants are exactly what `EntrySound` and the hypothesis carry — no
"the unmoved children are still present" side condition enters. -/
theorem EntrySound.cong_of_congList {src : Database} {f : FnName} {cs : List Term} {e : Term}
    (h : EntrySound src f cs e) {as : List Term} (ha : Term.app f as ∈ src.terms)
    (hl : CongList src as cs) : Cong src (.app f as) e :=
  let ⟨_, hbm, hbl, hbe⟩ := h
  (Cong.congr ha hbm (hl.trans hbl.symm)).trans hbe

/-- **Every view entry the target holds claims only what the source derives.** The invariant
the whole half rests on, and the only one it needs: `ViewRepr` reads view entries and nothing
else. -/
def Database.ViewsSound (d src : Database) : Prop :=
  ∀ f cs e pf, d.Out (viewName f) cs [e, pf] → EntrySound src f cs e

/-- **And every union-find edge is an equation the source derives.** Not used by the
reduction — `SameClass` never reads `@UF` — but used to *preserve* `ViewsSound`: every
rebuild rule moves a column or an e-class along an edge. -/
def Database.EdgesSound (d src : Database) : Prop :=
  ∀ t p pf, d.Out ufName [t] [p, pf] → Cong src t p

mutual

/-- **Every id a source term reads is congruent to it.** By recursion on the term: the
literal case *is* the hypothesis, and at an application `ViewsSound` supplies a source
argument list congruent to the key. `Database.WF` says the children are source terms and is
used for nothing else. -/
theorem cong_of_viewRepr {src d : Database} (hw : src.WF) (hs : d.ViewsSound src) :
    ∀ (a : Term) {e : Term}, a ∈ src.terms → ViewRepr d a e → Cong src a e
  | .lit _, _, ha, .lit _ => ha
  | .app f as, _, ha, .app hl ho =>
      (hs f _ _ _ ho).cong_of_congList ha
        (congList_of_viewReprList hw hs as
          (fun a h => hw.subtermClosed _ ha (Term.arg_subterms h (Term.self_mem_subterms a)))
          hl)

@[inherit_doc cong_of_viewRepr]
theorem congList_of_viewReprList {src d : Database} (hw : src.WF) (hs : d.ViewsSound src) :
    ∀ (as : List Term) {es : List Term}, (∀ a ∈ as, a ∈ src.terms) →
      ViewReprList d as es → CongList src as es
  | [], _, _, .nil => .nil
  | a :: as, _, ha, .cons h₁ h₂ =>
      .cons (cong_of_viewRepr hw hs a (ha a (List.mem_cons_self ..)) h₁)
        (congList_of_viewReprList hw hs as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h₂)

end

/-- The invariant in the form the reduction consumes: `ViewsJustified` is what `ViewsSound`
buys, and the step between them is the recursion above. -/
def Database.ViewsJustified (d src : Database) : Prop :=
  ∀ a e, a ∈ src.terms → ViewRepr d a e → Cong src a e

@[inherit_doc cong_of_viewRepr]
theorem Database.ViewsSound.justified {src d : Database} (hw : src.WF)
    (hs : d.ViewsSound src) : d.ViewsJustified src := fun a _ ha h => cong_of_viewRepr hw hs a ha h

/-- **The completeness half reduces to `Database.ViewsJustified`, in three steps.** The two
terms read one id, that id is congruent to each of them, and `symm`/`trans` close it. This is
the whole of the target-side induction, and there is none. -/
theorem sameClass_cong_of_justified {src d : Database} (hj : d.ViewsJustified src) {a b : Term}
    (ha : a ∈ src.terms) (hb : b ∈ src.terms) (h : SameClass d a b) : Cong src a b :=
  let ⟨e, hae, hbe⟩ := h
  (hj a e ha hae).trans (hj b e hb hbe).symm

/-- **The whole completeness half, from one property of the target and nothing else.**

No `execM`, no `encode`, no `sorry`: `SameClass d a b → Cong src a b` at any target with
`ViewsSound`, over any source with `Database.WF`, at the source's own e-nodes. The
counterpart of `cong_sameClass_of_state`, and what is left unproved is exactly that an
`execM` target has the property. -/
theorem sameClass_cong_of_state {src d : Database} (hw : src.WF) (hs : d.ViewsSound src)
    {a b : Term} (ha : a ∈ src.terms) (hb : b ∈ src.terms) (h : SameClass d a b) :
    Cong src a b :=
  sameClass_cong_of_justified (hs.justified hw) ha hb h

/-! #### What each writer owes

`ViewsSound` and `EdgesSound` are per-*entry* conditions over a **fixed** source, and
`Cong src` does not move when the target does — so preservation under a writer is one
obligation about the one entry the writer adds, and an entry once justified stays justified.
That is also why `mergeResult`'s choice operator costs nothing here: the refutation
`ENCODING.md` records (`Falsity.Choice.transport_recorded_false`) is about relating two
*target* states, and this invariant relates a target to a fixed source, so whichever of two
colliding rows survives is justified against the same source. `EntrySound.select` is that,
stated.

One lemma per writer follows, each a fact about `EntrySound` and `Cong src` alone. -/

/-- **A build.** `encodeBuild` writes `@fView(es) ↦ (f(es), @Fiat)`, whose e-class column is
its own key applied — so `as := cs` witnesses the entry, and the obligation is that the source
holds the term the build built. -/
theorem entrySound_build {src : Database} (hw : src.WF) {f : FnName} {cs : List Term}
    (h : Term.app f cs ∈ src.terms) : EntrySound src f cs (.app f cs) :=
  ⟨cs, h, CongList.refl fun a ha =>
    hw.subtermClosed _ h (Term.arg_subterms ha (Term.self_mem_subterms a)), h⟩

/-- **The rebuild's e-class rule.** The entry keeps its key and moves its e-class along an
edge, so the witness is unchanged and the justification composes. -/
theorem EntrySound.eclass {src : Database} {f : FnName} {cs : List Term} {e x : Term}
    (h : EntrySound src f cs e) (hx : Cong src e x) : EntrySound src f cs x :=
  let ⟨as, ham, hal, hae⟩ := h
  ⟨as, ham, hal, hae.trans hx⟩

/-- **The rebuild's column rule.** Column `i` of the key moves along an edge and the e-class
stays. The witness is unchanged again — the existential in `EntrySound` is what pays for
that, and it is why this case needs neither a congruence step nor the unmoved children. -/
theorem EntrySound.column {src : Database} {f : FnName} {cs : List Term} {e c x : Term}
    (h : EntrySound src f cs e) {i : Nat} (hi : cs[i]? = some c) (hx : Cong src c x) :
    EntrySound src f (cs.set i x) e :=
  let ⟨as, ham, hal, hae⟩ := h
  ⟨as, ham, hal.setAt i hi hx, hae⟩

/-- **The merge step's edge.** Two entries have collided at one key and `mergeBody` writes
the `@UF` edge between their e-class columns; both are congruent to one source application,
so the edge is an equation the source derives — in either orientation, which is what
`ordering-max`/`ordering-min` leave open. -/
theorem cong_of_entrySound_collide {src : Database} {f : FnName} {cs : List Term}
    {e₁ e₂ : Term} (h₁ : EntrySound src f cs e₁) (h₂ : EntrySound src f cs e₂) :
    Cong src e₁ e₂ :=
  let ⟨_, ham, hal, hae⟩ := h₁
  hae.symm.trans (h₂.cong_of_congList ham hal)

/-- **The merge step's surviving row.** `mergeResult` settles the collision on one of the two
e-class columns, and either choice is justified — the selection is between two rows the
invariant already covers. -/
theorem EntrySound.select {src : Database} {f : FnName} {cs : List Term} {e₁ e₂ e : Term}
    (h₁ : EntrySound src f cs e₁) (h₂ : EntrySound src f cs e₂) (h : e = e₁ ∨ e = e₂) :
    EntrySound src f cs e := by
  rcases h with rfl | rfl <;> assumption

/-- **A source `union`.** `encodeAction` writes `@UF (ordering-max x₁ x₂) ↦ (ordering-min x₁
x₂, pf)`, and the source asserts the pair; `Cong.symm` covers whichever orientation
`ordering-max` picks. -/
theorem cong_of_eqs {src : Database} {a b t p : Term} (h : (a, b) ∈ src.eqs)
    (ho : (t = a ∧ p = b) ∨ (t = b ∧ p = a)) : Cong src t p := by
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .assert h
  · exact (Cong.assert h).symm

/-- **Path compression.** `pathCompressRule` writes `a → c` out of `a → b` and `b → c`: two
sound edges compose, and that is `Cong.trans` with nothing added. -/
theorem cong_of_pathCompress {src : Database} {a b c : Term} (h₁ : Cong src a b)
    (h₂ : Cong src b c) : Cong src a c := h₁.trans h₂

/-! #### And at a state a program reaches

The same discipline the forward half's residues get: `Database.ViewsSound` is what the
completeness half is reduced to, so here it is at `satTarget`, the state
`satProgram_programStep` steps to, over the source `satProgram`'s own run leaves. The one
view entry the run wrote is discharged by `entrySound_build`, non-vacuously; the `@UF` clause
is vacuous there — `satProgram` has no `union` — and is discharged non-vacuously at
`refutationState`, which holds one edge and nothing else. -/

/-- `viewName` is injective, which is what lets an entry term name its constructor. -/
theorem viewName_inj {f g : FnName} (h : viewName f = viewName g) : f = g := by
  have h2 := congrArg String.toList h
  rw [viewName, viewName, String.toList_append, String.toList_append, String.toList_append,
    String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left (List.append_cancel_right h2))

/-- **A view is never a term relation**, whatever the two constructors: the two suffixes
differ in their last character. Needed wherever a term-relation row is as wide as a view
entry, which it is at every constructor of positive arity — a nullary one's row has a single
column and is excluded by length alone. -/
theorem viewName_ne_termName {f g : FnName} : viewName f ≠ termName g := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, termName, String.toList_append, List.reverse_append] at h2

/-- The source state `satProgram` runs to: the one term it builds, and nothing else. -/
def satSrc : Database := Database.empty.addTerm (.app "A" [])

theorem satSrc_wf : satSrc.WF := Database.WF.empty.addTerm _

theorem satSrc_mem : Term.app "A" [] ∈ satSrc.terms := Database.mem_addTerm _ _

/-- **`Database.ViewsSound` holds at `satTarget`.** Three of the four terms the run holds are
too short to be a view entry — a key plus the two value columns is two columns at least — and
`@AView(A, @Fiat)` is what is left: key `[]`, e-class `A`, and `A` is the term
`satProgram` built. -/
theorem satTarget_viewsSound : satTarget.ViewsSound satSrc := by
  intro f cs e pf ho
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : cs = bs :=
    List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag satTarget_diag h)
  rcases satTarget_mem_cases hmem with h' | h' | h' | h' <;>
      simp only [satTermEntry, satViewEntry, Term.app.injEq] at h' <;>
    [skip; skip; skip; skip]
  · obtain rfl : cs = [] := by
      have hl : (cs ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : f = "A" := viewName_inj h'.1
    obtain ⟨rfl, -⟩ : e = Term.app "A" [] ∧ pf = Term.app fiatName [] := by simpa using h'.2
    exact entrySound_build satSrc_wf satSrc_mem
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · have hl : (cs ++ [e, pf]).length = 1 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega

/-- **`Database.EdgesSound` holds at `satTarget` too**, and vacuously: `satProgram` has no
`union`, so nothing writes a `@UF` entry. -/
theorem satTarget_edgesSound : satTarget.EdgesSound satSrc := by
  intro t p pf ho
  obtain ⟨bs, -, hmem⟩ := ho
  exact absurd hmem (satTarget_no_uf (bs ++ [p, pf]))

/-- **`Database.EdgesSound` at a state that holds an edge**, so the clause is not carried by
its vacuous case alone: `refutationState`'s one entry is `@UF(A) ↦ (A, @Fiat)`, and `A` is
self-congruent in `satSrc`. -/
theorem refutationState_edgesSound : refutationState.toDatabase.EdgesSound satSrc := by
  intro t p pf ho
  obtain ⟨bs, hcl, hmem⟩ := ho
  have hr : refutationState.toDatabase.EqsRefl :=
    FDatabase.EqsRefl.toDatabase (by intro q hq; simp [refutationState] at hq)
  obtain rfl : [t] = bs := CongList.eq_of_eqsRefl hr hcl
  obtain ⟨hk, hv⟩ := refutationState_pin (by simp) hmem
  obtain rfl : t = refA := by simpa using hk
  obtain ⟨rfl, -⟩ : p = refA ∧ pf = Term.app fiatName [] := by simpa using hv
  exact satSrc_mem

/-- **`SameClass` is inhabited at that state**, so the reduction is not discharged by a
premise nothing satisfies: `A` reads its own view entry. -/
theorem satTarget_sameClass_self : SameClass satTarget (.app "A" []) (.app "A" []) :=
  let hv : ViewRepr satTarget (.app "A" []) (.app "A" []) :=
    .app .nil ⟨[], .nil, satTarget_mem_view⟩
  ⟨_, hv, hv⟩

/-- **All of `sameClass_cong_of_state`'s hypotheses hold together at a reachable state, and
its premise is inhabited there.** `satProgram_programStep` is the reachability. -/
theorem sameClass_cong_of_state_witness :
    satSrc.WF ∧ satTarget.ViewsSound satSrc ∧ satTarget.EdgesSound satSrc ∧
      Term.app "A" [] ∈ satSrc.terms ∧ SameClass satTarget (.app "A" []) (.app "A" []) ∧
      Cong satSrc (.app "A" []) (.app "A" []) :=
  ⟨satSrc_wf, satTarget_viewsSound, satTarget_edgesSound, satSrc_mem,
    satTarget_sameClass_self,
    sameClass_cong_of_state satSrc_wf satTarget_viewsSound satSrc_mem satSrc_mem
      satTarget_sameClass_self⟩

/-- **The residue of the completeness half. Not proved.**

What is missing: that the state `execM` returned satisfies `Database.ViewsSound` and
`Database.EdgesSound` over the source. Every *per-entry* obligation is discharged, one per
writer `encode` emits — `entrySound_build`, `EntrySound.eclass`, `EntrySound.column`,
`EntrySound.select`, `cong_of_entrySound_collide`, `cong_of_eqs`, `cong_of_pathCompress` here,
and `entrySound_headBuild`/`cong_headUnion` in `Encoding/Match.lean` for the two writers a rule
head has. What is left is two things, and the rule head is no longer one of them.

* The encoded action list has to be read back off `execAction`, one `set` at a time, so that
  "these are the writers" is a theorem rather than a reading of `encodeBuild`. This is the same
  missing step `execM_viewsCover` needs, in the opposite direction, and `encodeBuild_fst` is
  what makes it a *syntactic* read-back: the naming expression a build returns is the
  expression it was given, so the entry is keyed on the source argument expressions and valued
  at the source expression, both evaluated in the target.
* `execM`'s rule firing is `FDatabase.runSaturateM`'s fixpoint, which is strictly weaker than
  `RunSaturated` (`execM_contained`: the enumerator under-fires), so it is that fixpoint the
  two properties have to be proved from — and it is the *source* side of the same alignment
  that `entrySound_headBuild`'s `hfired` names: the source rule fired, at the substitution the
  correspondence returns, and holds what its own head built. `RunRules` fires only the
  substitutions valid in the pre-state, so this is a per-command alignment and not a fact about
  either final state.

**The rule head is closed, and was the case worth doubting.** `encodeBuild` mints its skolem
over the arguments' *ids*, so `mem_terms_of_entrySound_skolem` makes the head's obligation
equivalent to the minted id being a source term — which, read off the key, is the fact
`encode_corresponds_invents_enode` refutes. It is not needed: the source reading the
correspondence delivers is a *choice*, and taking it to be the ids themselves is legitimate
because `Database.ViewsSound` reads a key column back as something congruent to the id and both
endpoints of a congruence are present. `Encoding/Match.lean`'s `exists_validQuerySubst_at_ids`
is that reading, `Expr.eval_transport` is why the source's head evaluation then gives the same
term rather than a congruent one, and `entrySound_headBuild` is the case — with `hfired`, the
source's own firing, as its only residue. `entrySound_headBuild_witness` is all of its
hypotheses holding together at `wProgram`, at the view entry that run really wrote.

At a program with no rule the hypothesis is the source's own `evalAction`, and
`satTarget_viewsSound` is that case discharged. -/
theorem execM_viewsSound {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    tgt.toDatabase.ViewsSound src ∧ tgt.toDatabase.EdgesSound src := by
  sorry

/-- **No equality is invented, at the source's own e-nodes.** Proved from
`execM_viewsSound`, through `sameClass_cong_of_state` — the target-side half needs no
induction, only the invariant.

**The two membership hypotheses are not bookkeeping and cannot be dropped**: without them the
statement is false at `witnessProgram`, where the rebuild gives `(Add One One)` an e-class and
the source has no e-node for it (`encode_corresponds_invents_enode`). `Cong src a b` implies
both, so the forward half pays nothing for them, and `difftest correspond`'s universe is the
two term sets, so the corpus result is a measurement of exactly this restricted claim. -/
theorem encode_corresponds_complete {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) (h : SameClass tgt.toDatabase a b) : Cong src a b :=
  sameClass_cong_of_state (hsrc.wf Database.WF.empty)
    (execM_viewsSound hdom hsrc htgt).1 ha hb h

/-- **The correspondence.** `difftest correspond 64` runs exactly this claim over the 70
in-domain cases and the seventeen probes, through `sameClassF` and `closureF`, and reports
70 agreeing, 0 LOST, 0 INVENTED — and `link-diff` 0, which is what says the swept relation
is this one.

`EncodeDomain` is still needed: outside it `encode` is not defined for the program at all —
a `:merge` declaration has no table triple to emit, and a source name in the generated
namespace collides with one. `Rebuilt` is *not* a hypothesis: it is a postcondition of the
specification's rebuild command (`cmdStep_rebuilt`), and the hypothesis here names an
`execM` target, so what the two unproved halves have to lean on is the interpreter's own
`mergeSaturateF` fixpoint instead.

**Stated at the source's e-nodes**, which is where the encoding is faithful and where the
corpus sweep measures it. The two membership hypotheses cost the forward direction nothing —
`Cong src a b` implies both — and the backward direction cannot do without them:
`encode_corresponds_invents_enode` refutes the unrestricted `iff` at this file's own witness
program. -/
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt.toDatabase a b :=
  ⟨encode_corresponds_forward hdom hsrc htgt, encode_corresponds_complete hdom hsrc htgt ha hb⟩

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

/-- `(Add One One)` — a term `witnessProgram` never builds, and the one the rebuild gives an
e-class anyway. `(union One Two)` puts `(One)` in `(Two)`'s `reprs`, so the column rule
re-keys `@AddView((One), (Two))` to `@AddView((One), (One))`, and there is the entry
`(Add One One)` reads. Nothing writes `(Add One One)` into either database's term set, which
is why the corpus sweep never puts it on a pair. -/
def witnessAddOneOne : Term := .app "Add" [witnessOne, witnessOne]

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
  noLeafPattern := by
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> trivial
  noBareBuild := by
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.NoBareBuild, Action.NoBareBuild, Expr.IsApp]

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

/-- **The encoding invents an e-node, so the unrestricted completeness half is false.**

Same shape as `encode_corresponds_witness` and the same discipline: every hypothesis is a
*decidable* fact about one concrete program's two runs, and `difftest correspond-selftest`
evaluates them. With them, all three hypotheses of `encode_corresponds_complete` hold, the
target puts `(Add One One)` in an e-class with itself, and the source holds no such term — so
`SameClass tgt a b → Cong src a b` cannot be proved without the membership hypotheses
`encode_corresponds_complete` now carries.

`(Add One One)` is *not* a defect in `encode`: the entry the rebuild wrote is true of the
terms it is about, and every source e-node still corresponds. What is a defect is stating the
correspondence as an unrestricted `iff`, which is what this refutes. -/
theorem encode_corresponds_invents_enode {d e : FDatabase}
    (hd : exec witnessProgram = some d) (he : execM (encode witnessProgram) = some e)
    (hsc : e.SubtermClosed) (hr : e.EqsRefl)
    (hyes : sameClassF e witnessAddOneOne witnessAddOneOne = true)
    (hno : (witnessAddOneOne, witnessAddOneOne) ∉ d.closureF) :
    ∃ src, witnessProgram.EncodeDomain ∧ ProgramStep Database.empty witnessProgram src ∧
      execM (encode witnessProgram) = some e ∧
      SameClass e.toDatabase witnessAddOneOne witnessAddOneOne ∧
      witnessAddOneOne ∉ src.terms := by
  refine ⟨d.toDatabase, witnessProgram_encodeDomain, ?_, he,
    (sameClassF_iff hsc hr _ _).mp hyes, fun hmem => hno ?_⟩
  · exact (exec_programStep witnessProgram_encodeDomain.ctorDecls
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · exact FDatabase.mem_closureF_iff.mpr hmem

end Egglog
