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
* **Proved, and what joins the read-back's blocks**: the **command induction**.
  `ReadsSelfInv` is the invariant it carries — every source term reads to itself and every
  source equation has its `@UF` edge, both at the state the *whole* run finishes at, plus the
  two environments coinciding and the source staying in the constructor fragment — and
  `readsSelfInv_step` carries it across a source command in five of its six cases:
  `.decl`, `.rule`, a top-level build, a top-level `let` (whose `hvar` obligation the
  invariant supplies, `ReadsSelfInv.hvar`) and a top-level `union` (whose edge
  `out_uf_of_execProgramM` reads back off the emitted `set`). `readsSelfInv_execM` runs it from
  the empty source database and the state the prelude leaves, and `execM_readsSelf` and
  `execM_edges` are its two data clauses. Three lemmas make it go through and each is worth
  naming: `Expr.eval_sigIndep` — two successful evaluations in one environment agree, whatever
  the two signatures — `encodeBuild_fst`, and `viewReprAll_self_of_execProgramM`, the read-back
  strengthened to every *subterm*, which is what `Database.addTerm` records. And it is not
  vacuous: `rbState2_readsSelfInv` is the invariant at a source state a program reaches
  (`rbProgram_programStep`) with the `terms` clause asked at positive arity and the environment
  non-empty, `rbState2_readsSelfInv_hvar` is the `hvar` composition read off it, and
  `builtRead_fire_satisfiable` is the residue's five hypotheses holding together.
* **Proved, and the rebuild fixpoint the five residues were waiting for**:
  `FDatabase.RoundClosed` (`Proofs/Merge.lean`). `runSaturateM` returns only from the branch
  that tested `sameData`, so a successful `Cmd.saturate R` leaves a state where **one more
  round of `R` derives no new term**; `roundClosed_of_execProgramM` locates one at the end of
  every block `encodeCmd` emits for a writing command. It is the only fixpoint available —
  `execM_contained` says the enumerator under-fires, so `RunSaturated`, and `Rebuilt` with it,
  is not a consequence — and it is a `terms` fact, because a round adds terms and *deletes*
  rows, so the sandwich that closes over the first does not close over the second.
* **Refuted, and it is why the fixpoint closes none of the five**: `FDatabase.IndexCurrent`,
  the converse of `FDatabase.IndexOk.entry` — every entry term still current in the index.
  `cxTgt_not_indexCurrent` refutes it at a state built by the interpreter's own writers at the
  encoding's own declarations, where a source `union` collides two e-classes at one view key,
  `mergeOneOriented` deletes the displaced row, and `Database.Out` still reads its entry term.
  A rebuild rule's *conclusion* is a `terms` fact the fixpoint supplies; its *premise* is a
  `rows` fact only this would, so `IndexOk` needs a companion rather than a fourth field, and
  the companion is false. What survives is the same claim up to the union-find
  (`cxTgt_out_uf`), which does not compose with the clauses as stated.
* **`sorry`**, five, one *clause* each and none of them an obligation any more.
  `execM_viewsCover_keyed` needs the command induction *and* the index argument;
  `execM_viewLeader` and `execM_eclassFollowed` need the index argument;
  `execM_viewsSound` is the completeness half; and `builtRead_fire` is the command induction's
  one open case — a source command that fires rules, which needs the premise row to be
  **current in the index**, not merely an entry term. `execM_viewsCover`, `execM_unionsJoined`
  and `execM_unionsRead` are assembled from them, proved.
  `Encoding/Match.lean`'s `uRebuilt_unionsJoined` is `Database.UnionsJoined`'s three clauses
  at a state a program reaches and `uTgt_not_unionsRead` is the third failing one rebuild
  firing earlier. `encode_assert`, `encode_trans`, `encode_congr`,
  `encode_corresponds_forward`, `encode_corresponds_complete` and `encode_corresponds` are
  assembled from them and carry `sorryAx` through them.
* **Refuted, and it was the *reading* that was wrong**: two of those clauses were once false
  at `litBuildProgram`, one `.action (.expr (.lit 5))`, whose build emits no action at all, and
  `Program.EncodeDomain.noBareBuild` was the repair. The defect was `ViewRepr`'s literal clause
  asking the target to hold the literal, where the encoding mints no e-node for one. The
  premise is gone and the domain clause with it;
  `litBuild_viewsCover`/`litBuild_unionsJoined`/`litBuild_forward` are the two once-false
  statements holding at that program, now in the domain (`litBuildProgram_encodeDomain`). What
  keeps the reading exact is `ViewRepr.eq_of_lit`: a literal's only id is itself, so distinct
  literals are never in one class (`SameClass.eq_of_lit`) and `not_sameClass_lit_app` rules out
  the view row a literal would need to join an application.
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

A literal is its own id and nothing else's, whether the target holds it or not: `encodeBuild`
emits no action for a literal, so a literal never keys a view entry and the encoding owes it
no e-node. -/
def viewReprsF (d : FDatabase) : Term → List Term
  | .lit l => [Term.lit l]
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
    rw [viewReprsF, List.mem_singleton] at h
    subst h
    exact .lit
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
  | .lit => simp [viewReprsF]
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

/-- **At `satTarget` an application has at most one id, and it is `(A)`.** Two of the four
terms are too short to be a view entry at all — a key plus the two value columns is two
columns at least — one is `@ATerm`'s row, which is one column, and `@AView(A, @Fiat)` is what
is left, its e-class column `A`. `satTarget_diag` is what lets the key be read up to equality.

Stated at an application because a literal's id is the literal (`ViewRepr.eq_of_lit`), which
this state holds none of. -/
private theorem satTarget_viewRepr {g : FnName} {bs : List Term} {e : Term}
    (h : ViewRepr satTarget (.app g bs) e) : e = Term.app "A" [] := by
  match h with
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

/-- **`Database.ViewLeader` holds at `satTarget`**, with the identity as its `lead`. The
literal case needs nothing of the state: a literal's only id is itself. -/
theorem satTarget_viewLeader : satTarget.ViewLeader :=
  ⟨id, fun _ _ h => h, fun t _ _ h₁ h₂ =>
    show id _ = id _ from match t with
      | .lit _ => (h₁.eq_of_lit).trans h₂.eq_of_lit.symm
      | .app _ _ => (satTarget_viewRepr h₁).trans (satTarget_viewRepr h₂).symm⟩

/-- **The keys the target's views carry**, relative to what the source holds.

`keyed` is the rebuild, stated: an entry for `f` at *every* tuple of ids its children are
given, not only at the tuple the build wrote. `rebuildRules`' column rules are what put them
there — one `set` per column per `@UF` edge, so a saturated ruleset covers the product — and
`difftest correspond-dump 64 union` shows the product covered and nothing outside it: keys
`(One,One)`, `(One,Two)` and `(Two,One)` for `@AddView`, and no `(Two,Two)`, since `(One)` is
a leader and reads only to itself.

**One clause, and it is about applications only.** A literal is its own id unconditionally
(`ViewRepr.lit`), so the target owes it nothing — which is why there is no `lits` clause here
and why a source action building a bare literal costs the domain nothing. -/
structure Database.ViewsCover (d src : Database) : Prop where
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
`ViewRepr.lit` at a literal, and `keyed` at an application whose children's ids the recursion
supplies. `Database.WF` is what says the children are held, and `ProgramStep.wf` delivers it
from the empty state. -/
theorem viewRepr_total {d src : Database} (hc : d.ViewsCover src) (hw : src.WF) :
    ∀ t : Term, t ∈ src.terms → ∃ e, ViewRepr d t e
  | .lit l, _ => ⟨.lit l, .lit⟩
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
no row from *this* build. A bare literal needs neither, and nothing about `D` either: its id is
itself (`ViewRepr.lit`). -/
theorem viewRepr_self_of_execActions : ∀ (e : Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuild e n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ e.fns, Prim.ofName g = none) →
    (∀ w ∈ e.vars, ∀ u, Env.lookup w d.env = some u → ViewRepr D.toDatabase u u) →
    ∀ t, e.eval d.sig d.env = some t → ViewRepr D.toDatabase t t
  | .lit l, _, _, _, _, _, _, _, _, t, hev => by
      obtain rfl : Term.lit l = t := Option.some.inj hev
      exact .lit
  | .var w, _, _, _, _, _, _, _, hvar, t, hev => hvar w (by simp [Expr.vars]) t hev
  | .app f args, n, d, d', D, hrun, hD, hprim, hvar, t, hev => by
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
        (fun w hw u hu => hvar w (by simpa [Expr.vars] using hw) u hu) is his)
        ⟨is, CongList.refl hmemis, FDatabase.mem_toDatabase_terms.mpr
          (hD _ (hview _ (Term.self_mem_subterms _)))⟩

@[inherit_doc viewRepr_self_of_execActions]
theorem viewReprList_self_of_execActions : ∀ (es : List Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuildArgs es n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
    (∀ w ∈ Expr.varsList es, ∀ u, Env.lookup w d.env = some u → ViewRepr D.toDatabase u u) →
    ∀ ts, Expr.evalList d.sig es d.env = some ts → ViewReprList D.toDatabase ts ts
  | [], _, _, _, _, _, _, _, _, ts, hev => by
      obtain rfl : ([] : List Term) = ts := Option.some.inj hev
      exact .nil
  | e :: es, n, d, d', D, hrun, hD, hprim, hvar, ts, hev => by
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
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u hu) t ht)
        (viewReprList_self_of_execActions es (encodeBuild e n).2.2 htail hD
          (fun g hg => hprim g (by simp [Expr.fnsList, hg]))
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u
            (by rw [henv₁] at hu; exact hu))
          ts' (by rw [hsig₁, henv₁]; exact hts'))
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
    {t : Term} (hev : e.eval d.sig d.env = some t) :
    ViewRepr D.toDatabase t t := by
  obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  obtain ⟨m, hm, hmm⟩ := exists_execActions_of_execProgramM (encodeBuild_isSet e n) hblock
  exact viewRepr_self_of_execActions e n hm
    (fun x hx => FDatabase.execProgramM_terms hafter x (hmm x hx)) hprim hvar t hev

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
    _ rfl

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

/-- After `(W 5)`'s build from the prelude: a **literal in a key column**, which is the one
place a source literal can be and the case `ViewRepr`'s clause is about. -/
def rbLitState : FDatabase :=
  (execActions rbState (encodeBuild (.app "W" [.lit (.int 5)]) 0).2.1).getD FDatabase.empty

theorem rbLitState_eq :
    execActions rbState (encodeBuild (.app "W" [.lit (.int 5)]) 0).2.1 = some rbLitState := rfl

/-- **A build over a literal key reads back**, with the literal column supplied by
`ViewRepr.lit` and nothing asked of the state for it. -/
theorem rbLitState_viewRepr :
    ViewRepr rbLitState.toDatabase (.app "W" [.lit (.int 5)]) (.app "W" [.lit (.int 5)]) :=
  viewRepr_self_of_execActions (.app "W" [.lit (.int 5)]) 0 rbLitState_eq (fun _ h => h)
    (by decide) (fun w hw => absurd hw (by simp [Expr.vars, Expr.varsList])) _ rfl

/-- **And the literal in that key column joins nothing to its parent.** Both readings are
decided at the state: the literal's ids are exactly itself, `(W 5)`'s is the skolem `W(5)`,
and `sameClassF_iff` carries the second to `SameClass` — so `ViewRepr.lit` giving every
literal an id costs the key column nothing. -/
theorem rbLitState_lit :
    viewReprsF rbLitState (.lit (.int 5)) = [Term.lit (.int 5)] ∧
      ¬ SameClass rbLitState.toDatabase (.lit (.int 5)) (.app "W" [.lit (.int 5)]) :=
  ⟨rfl, fun h => by
    have := (sameClassF_iff (d := rbLitState) ((FDatabase.subtermClosedB_iff _).mp rfl)
      ((FDatabase.eqsReflB_iff _).mp rfl) _ _).mpr h
    exact absurd this (by decide)⟩

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

What all three need is an invariant carried through `FDatabase.execProgramM` that reads the
encoded program's *own* commands — the two `set`s per build, the `@UF` edge per `union`, and the
`Cmd.saturate rebuildRuleset` after each. The nearest thing the library has is
`execM_contained`, and it does not reach: it is proved under `Program.NoSaturate`, and `encode`
emits a `Cmd.saturate` after every command that writes.

**What the two sections below supply, and what is left.** The action read-back is proved: at a
block of a build's own commands, both of its rows are entry terms of whatever the run finishes
at (`holdsBuild_of_execProgramM`), and they assemble into the reading
(`viewRepr_self_of_execProgramM`). The **command induction** is proved on top of it, save one
case: `ReadsSelfInv` is its invariant, `readsSelfInv_execM` runs it over `encode P`, and
`Database.UnionsJoined`'s first two clauses — `execM_readsSelf` and `execM_edges` — come out of
it. Both of the two things that made the induction more than bookkeeping are handled there:

* a source term reached through a **variable** needs the earlier `let`'s own read-back, which is
  the `hvar` hypothesis of `viewRepr_self_of_execActions`; the invariant's `env` and `terms`
  clauses together supply it (`ReadsSelfInv.hvar`);
* a source term built by a **rule firing** needs the source's firing to have a target firing
  behind it, which is the *opposite* direction from `exists_validQuerySubst_of_encodeQuery`.
  This is the case that does not close, and the reason is one step below the firing:
  `matchQuery` reads the *index* at a `.merge` function, and the read-back gives entry terms.
  `builtRead_fire` is it, alone.

**Two of these statements were once false**, at a program the domain admitted, and the state
that showed it is below — now with the sign reversed: `ViewRepr`'s literal clause carries no
membership premise, so the bare-literal build is in the domain and both statements hold there
(`litBuild_viewsCover`, `litBuild_unionsJoined`). -/

/-! #### The bare leaf, admitted

`.action (.expr (.lit 5))` writes nothing at all in the target — `encodeBuild` emits no action
for a leaf — and for that reason used to refute `Database.ViewsCover`'s since-deleted `lits`
clause and `Database.UnionsJoined.readsSelf`, which is what
`Program.EncodeDomain.noBareBuild` was added to exclude. It excludes nothing now: a literal's
id is itself and the target is asked for nothing, so the clause is gone and this is the
witness that its absence costs the two statements nothing. -/

/-- One top-level action that builds a bare literal, and its constructor-free program. -/
def litBuildProgram : Program := [.action (.expr (.lit (.int 5)))]

/-- **And it is in the domain.** The clause that excluded it is gone; every other one holds. -/
theorem litBuildProgram_encodeDomain : litBuildProgram.EncodeDomain where
  ctorsOnly := by simp [litBuildProgram]
  noSet := by simp [litBuildProgram, Cmd.NoSet, Action.NoSet]
  noPrim := by simp [litBuildProgram, Program.ctors, Cmd.ctors, Action.ctors, Expr.ctors]
  noAt := by simp [litBuildProgram, Program.ctors, Cmd.ctors, Action.ctors, Expr.ctors]
  noAtVar := by
    simp [litBuildProgram, Program.vars, Cmd.vars, Action.vars, Expr.vars]
  noAtRuleset := by simp [litBuildProgram, Program.rulesets, Cmd.rulesets]
  noLeafPattern := by simp [litBuildProgram, Cmd.NoLeafPattern]

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

/-- The one term the source holds. -/
theorem litBuildSrc_terms : litBuildSrc.terms = {Term.lit (.int 5)} := by
  simp [litBuildSrc, Term.subterms_lit]

/-- It asserts nothing but that term's reflexive equation. -/
theorem litBuildSrc_diag : litBuildSrc.Diag :=
  Database.Diag.addTerm (fun p hp => absurd hp (by simp [Database.empty])) _

/-- **`Database.ViewsCover` holds** — vacuously in `keyed`, the only clause, since the source
holds no application. The literal is covered by the reading itself (`ViewRepr.lit`), which asks
the target for no e-node because the encoding writes none. -/
theorem litBuild_viewsCover {tgt : FDatabase} : tgt.toDatabase.ViewsCover litBuildSrc where
  keyed := by
    intro f as es hmem
    rw [litBuildSrc_terms] at hmem
    exact absurd hmem (by simp)

/-- **And so does `Database.UnionsJoined`**: `readsSelf` at the one term is `ViewRepr.lit`, the
source asserts no equation between distinct terms, and the target holds no `@UF` entry to
follow. -/
theorem litBuild_unionsJoined {tgt : FDatabase}
    (htgt : execM (encode litBuildProgram) = some tgt) :
    tgt.toDatabase.UnionsJoined litBuildSrc where
  readsSelf := by
    intro t hmem
    rw [litBuildSrc_terms, Set.mem_singleton_iff] at hmem
    exact hmem ▸ .lit
  edges := fun a b hab hne => absurd (litBuildSrc_diag (a, b) hab) hne
  eclassFollowed := by
    intro t p pf _ _ ho
    obtain ⟨bs, -, hmem⟩ := ho
    rw [FDatabase.mem_toDatabase_terms, litBuild_terms htgt] at hmem
    exact absurd hmem (by simp)

/-- **The forward half holds at the very program that refuted it**: the source asserts the
literal's reflexive equation and the target reads it back, with nothing in the target at
all. -/
theorem litBuild_forward {tgt : FDatabase} :
    Cong litBuildSrc (.lit (.int 5)) (.lit (.int 5)) ∧
      SameClass tgt.toDatabase (.lit (.int 5)) (.lit (.int 5)) :=
  ⟨litBuildSrc_mem, ⟨_, .lit, .lit⟩⟩

/-! #### The command induction

`Database.UnionsJoined`'s first two clauses are read-backs of actions the encoder emitted, and
the read-back above is stated at **one** block. What joins the blocks is an induction over
`encode P`'s commands, and what that induction has to carry is more than the reading itself: a
term reached through a variable needs the earlier `let`'s own reading — the `hvar` hypothesis of
`viewRepr_self_of_execActions` — and a source `union` records an equation at the same moment it
records two terms, so `readsSelf` and `edges` have to be carried *together*.

`ReadsSelfInv` is that invariant. Its two data clauses are stated at the **final** state `D`,
which is what makes them composable: the rebuild overwrites rows and only the entry term
survives (`FDatabase.execProgramM_terms`), so "the block wrote it" is a fact about the state the
whole run finishes at, never about the state the next command starts from. Its other two clauses
are bookkeeping — the two environments coincide, so a source `let`'s value is the encoded `let`'s
value, and the source state stays in the constructor fragment, which is what makes every source
command's merge phase empty.

Five of the six command cases close. The sixth — a command that **fires rules** — is
`builtRead_fire`, alone, with a docstring saying exactly what it needs and why the read-back
cannot supply it. -/

/-! ##### Evaluation does not depend on the signature

The read-back hands back the *target's* evaluation of a source expression and the source hands
back its own. The two states have different signatures and the same environment, and that is
enough: the signature decides only whether an application evaluates, never to what. -/

mutual
/-- **Two successful evaluations of one expression in one environment agree.** `Expr.eval` reads
the signature for one thing — whether the head builds — and that decides only whether the
evaluation *succeeds*. So a source expression the encoded run also evaluated evaluated to the
same term, with nothing asked of either signature. -/
theorem Expr.eval_sigIndep {s₁ s₂ : Signature} {σ : Env} :
    ∀ (e : Expr) {t₁ t₂ : Term}, e.eval s₁ σ = some t₁ → e.eval s₂ σ = some t₂ → t₁ = t₂
  | .lit _, _, _, h₁, h₂ => by
      rw [Expr.eval, Option.some.injEq] at h₁ h₂
      rw [← h₁, ← h₂]
  | .var _, _, _, h₁, h₂ => Option.some.inj (h₁.symm.trans h₂)
  | .app f args, _, _, h₁, h₂ => by
      cases hp : Prim.ofName f with
      | some p =>
          simp only [Expr.eval, hp] at h₁ h₂
          obtain ⟨is₁, hi₁, ha₁⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨is₂, hi₂, ha₂⟩ := Option.bind_eq_some_iff.mp h₂
          rw [Expr.evalList_sigIndep args hi₁ hi₂] at ha₁
          exact Option.some.inj (ha₁.symm.trans ha₂)
      | none =>
          simp only [Expr.eval, hp] at h₁ h₂
          split at h₁
          · split at h₂
            · obtain ⟨is₁, hi₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
              obtain ⟨is₂, hi₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
              rw [Expr.evalList_sigIndep args hi₁ hi₂]
            · exact absurd h₂ (by simp)
          · exact absurd h₁ (by simp)

@[inherit_doc Expr.eval_sigIndep]
theorem Expr.evalList_sigIndep {s₁ s₂ : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts₁ ts₂ : List Term},
      Expr.evalList s₁ es σ = some ts₁ → Expr.evalList s₂ es σ = some ts₂ → ts₁ = ts₂
  | [], _, _, h₁, h₂ => by
      rw [Expr.evalList, Option.some.injEq] at h₁ h₂
      rw [← h₁, ← h₂]
  | e :: es, _, _, h₁, h₂ => by
      rw [Expr.evalList] at h₁ h₂
      obtain ⟨t₁, ht₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨us₁, hus₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨t₂, ht₂, h₂⟩ := Option.bind_eq_some_iff.mp h₂
      obtain ⟨us₂, hus₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      rw [Expr.eval_sigIndep e ht₁ ht₂, Expr.evalList_sigIndep es hus₁ hus₂]
end

mutual
/-- **An expression that evaluated has all of its variables bound.** What carries a source
`let`'s success to the encoded `let`, whose operand is the same expression. -/
theorem Expr.exists_lookup_of_eval {s : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term}, e.eval s σ = some t →
      ∀ w ∈ e.vars, ∃ u, Env.lookup w σ = some u
  | .lit _, _, _, _, hw => absurd hw (by simp [Expr.vars])
  | .var v, t, h, w, hw => by
      obtain rfl : w = v := by simpa [Expr.vars] using hw
      exact ⟨t, h⟩
  | .app f args, _, h, w, hw => by
      cases hp : Prim.ofName f with
      | some p =>
          simp only [Expr.eval, hp] at h
          obtain ⟨is, his, -⟩ := Option.bind_eq_some_iff.mp h
          exact Expr.exists_lookupList_of_evalList args his w (by simpa [Expr.vars] using hw)
      | none =>
          simp only [Expr.eval, hp] at h
          split at h
          · obtain ⟨is, his, -⟩ := Option.map_eq_some_iff.mp h
            exact Expr.exists_lookupList_of_evalList args his w (by simpa [Expr.vars] using hw)
          · exact absurd h (by simp)

@[inherit_doc Expr.exists_lookup_of_eval]
theorem Expr.exists_lookupList_of_evalList {s : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term}, Expr.evalList s es σ = some ts →
      ∀ w ∈ Expr.varsList es, ∃ u, Env.lookup w σ = some u
  | [], _, _, _, hw => absurd hw (by simp [Expr.varsList])
  | e :: es, _, h, w, hw => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp h
      rw [Expr.varsList] at hw
      rcases List.mem_union_iff.mp hw with hw' | hw'
      · exact Expr.exists_lookup_of_eval e ht w hw'
      · exact Expr.exists_lookupList_of_evalList es hus w hw'
end

mutual
/-- **A head an expression applies is one of its `Expr.ctors`.** `Expr.fns` deduplicates and
`Expr.ctors` carries arities; the two name the same heads, which is what carries
`Program.EncodeDomain.noPrim` to a build's `hprim`. -/
theorem Expr.exists_ctor_of_mem_fns : ∀ {e : Expr} {g : FnName}, g ∈ e.fns →
    ∃ k, (g, k) ∈ e.ctors
  | .lit _, _, hg => absurd hg (by simp [Expr.fns])
  | .var _, _, hg => absurd hg (by simp [Expr.fns])
  | .app f args, g, hg => by
      rw [Expr.fns, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨args.length, by rw [Expr.ctors]; exact List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk⟩

@[inherit_doc Expr.exists_ctor_of_mem_fns]
theorem Expr.exists_ctorList_of_mem_fnsList : ∀ {es : List Expr} {g : FnName},
    g ∈ Expr.fnsList es → ∃ k, (g, k) ∈ Expr.ctorsList es
  | [], _, hg => absurd hg (by simp [Expr.fnsList])
  | e :: es, g, hg => by
      rw [Expr.fnsList] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_right _ hk⟩
end

/-- **No source head is a primitive**, at an expression the source program builds. `noPrim` is
stated over `Program.ctors` and a build's read-back asks over `Expr.fns`;
`Expr.exists_ctor_of_mem_fns` is the bridge. -/
theorem noPrim_of_mem_ctors {Q : Program} (hQ : Q.EncodeDomain) {e : Expr}
    (hsub : ∀ p ∈ e.ctors, p ∈ Q.ctors) : ∀ g ∈ e.fns, Prim.ofName g = none := by
  intro g hg
  obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
  exact hQ.noPrim (g, k) (hsub _ hk)

/-! ##### What the encoded commands leave the environment and the signature

`encodeCmd` emits no declaration at all, and the only action it emits that is not a `set` is the
`letBind` a source `let` becomes. So the target's signature never moves after the prelude, and
its environment moves exactly where the source's does. -/

/-- Every action this command runs is a `set`. True of a build's block, of every rule, run and
declaration, and false at exactly one encoded action: the `letBind` a source `let` becomes. -/
def Cmd.ActionsAreSets : Cmd → Prop
  | .action a => a.IsSet
  | _ => True

/-- Not a declaration. `encodeCmd` emits none. -/
def Cmd.NoDecl : Cmd → Prop
  | .decl _ _ => False
  | _ => True

namespace FDatabase

/-- A command whose actions are all `set`s leaves the environment alone. -/
theorem execCmdM_env {d d' : FDatabase} : ∀ {c : Cmd}, d.execCmdM c = some d' →
    c.ActionsAreSets → d'.env = d.env := by
  intro c hs hc
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).2.1, execAction_env_of_isSet hc h₁]
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl
  | run R => exact (runRoundM_fields hs).2.1
  | saturate R => exact (runSaturateM_fields runFuel hs).2.1
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl

/-- A command that is not a declaration leaves the signature alone. -/
theorem execCmdM_sig_of_noDecl {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d')
    (hc : c.NoDecl) : d'.sig = d.sig := by
  rw [execCmdM_sig hs]
  cases c with
  | decl f dc => exact (hc : False).elim
  | _ => rfl

@[inherit_doc execCmdM_env]
theorem execProgramM_env {p : Program} (hp : ∀ c ∈ p, c.ActionsAreSets) :
    ∀ {d D : FDatabase}, d.execProgramM p = some D → D.env = d.env := by
  induction p with
  | nil =>
    intro d D h
    rw [FDatabase.execProgramM, Option.some.injEq] at h
    exact h ▸ rfl
  | cons c cs ih =>
    intro d D h
    rw [FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) h₂,
      execCmdM_env h₁ (hp c List.mem_cons_self)]

@[inherit_doc execCmdM_sig_of_noDecl]
theorem execProgramM_sig_of_noDecl {p : Program} (hp : ∀ c ∈ p, c.NoDecl) :
    ∀ {d D : FDatabase}, d.execProgramM p = some D → D.sig = d.sig := by
  induction p with
  | nil =>
    intro d D h
    rw [FDatabase.execProgramM, Option.some.injEq] at h
    exact h ▸ rfl
  | cons c cs ih =>
    intro d D h
    rw [FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) h₂,
      execCmdM_sig_of_noDecl h₁ (hp c List.mem_cons_self)]

/-- **What an encoded top-level `let` leaves**: the binding, at the value its operand — the
source expression itself, by `encodeBuild_fst` — evaluated to in the state the `let` ran in. -/
theorem execCmdM_letBind {d d' : FDatabase} {v : Var} {e : Expr}
    (h : d.execCmdM (.action (.letBind v e)) = some d') :
    ∃ t, e.eval d.sig d.env = some t ∧ d'.env = (v, t) :: d.env ∧ d'.sig = d.sig ∧
      ∀ s ∈ d.terms, s ∈ d'.terms := by
  rw [FDatabase.execCmdM, execAction] at h
  obtain ⟨m, hm, hmerge⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨hsig, henv, -⟩ := mergeSaturateF_fields hmerge
  exact ⟨t, ht, henv, hsig, fun s hs =>
    mergeSaturateF_terms hmerge s (mem_addTerm_terms.mpr (Or.inr hs))⟩

end FDatabase

/-- **A build's own expression has a value in the state its block ran from.** For an
application the block's `set`s carry it (`execActions_encodeBuild_app`); for a leaf there is no
action at all, and a variable needs its binding. -/
theorem exists_eval_of_execActions_encodeBuild : ∀ (e : Expr) (n : Nat) {d d' : FDatabase},
    execActions d (encodeBuild e n).2.1 = some d' →
    (∀ w ∈ e.vars, ∃ u, Env.lookup w d.env = some u) →
    ∃ t, e.eval d.sig d.env = some t
  | .lit l, _, _, _, _, _ => ⟨.lit l, rfl⟩
  | .var w, _, _, _, _, hv => by
      obtain ⟨u, hu⟩ := hv w (by simp [Expr.vars])
      exact ⟨u, hu⟩
  | .app f args, n, d, d', hrun, _ => by
      obtain ⟨-, -, v, -, -, -, -, -, -, hv, -, -⟩ := execActions_encodeBuild_app hrun
      exact ⟨v, hv⟩

@[inherit_doc exists_eval_of_execActions_encodeBuild]
theorem exists_eval_of_execProgramM_encodeBuild (e : Expr) (n : Nat) {d D : FDatabase}
    {p : Program}
    (hrun : d.execProgramM ((encodeBuild e n).2.1.map Cmd.action ++ p) = some D)
    (hv : ∀ w ∈ e.vars, ∃ u, Env.lookup w d.env = some u) :
    ∃ t, e.eval d.sig d.env = some t := by
  obtain ⟨D₁, hblock, -⟩ := FDatabase.execProgramM_append hrun
  obtain ⟨m, hm, -⟩ := exists_execActions_of_execProgramM (encodeBuild_isSet e n) hblock
  exact exists_eval_of_execActions_encodeBuild e n hm hv

/-! ##### The reading at every subterm

`Database.addTerm` records a reflexive equation per **subterm** of the term built, so
`Database.UnionsJoined.readsSelf` is asked about all of them and not only about the term itself.
`ViewRepr d t t` does not give that on its own — its children read to *ids*, which need not be
themselves — so the recursion has to deliver it, and it does: an argument's subterms are covered
by the argument's own build, a variable's by `hvar`, and a literal's are itself. -/

mutual
/-- **Every subterm of a build's own term reads to itself.** `viewRepr_self_of_execActions` with
its conclusion and its `hvar` both closed under subterms, which is the form
`Database.UnionsJoined.readsSelf` consumes: the source records one reflexive equation per
subterm, so every subterm is a source term. -/
theorem viewReprAll_self_of_execActions : ∀ (e : Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuild e n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ e.fns, Prim.ofName g = none) →
    (∀ w ∈ e.vars, ∀ u, Env.lookup w d.env = some u →
      ∀ s ∈ u.subterms, ViewRepr D.toDatabase s s) →
    ∀ t, e.eval d.sig d.env = some t → ∀ s ∈ t.subterms, ViewRepr D.toDatabase s s
  | .lit l, _, _, _, _, _, _, _, _, t, hev, s, hs => by
      obtain rfl : Term.lit l = t := Option.some.inj hev
      obtain rfl : s = Term.lit l := by simpa using hs
      exact .lit
  | .var w, _, _, _, _, _, _, _, hvar, t, hev, s, hs =>
      hvar w (by simp [Expr.vars]) t hev s hs
  | .app f args, n, d, d', D, hrun, hD, hprim, hvar, t, hev, s, hs => by
      obtain ⟨d₁, is, v, pf, hargs, -, -, hmono, his, hv, -, -⟩ :=
        execActions_encodeBuild_app hrun
      have hvapp : v = Term.app f is := by
        obtain ⟨is', his', hveq⟩ := Expr.eval_app_of_noPrim (hprim f (by simp [Expr.fns])) hv
        rw [hveq, Option.some.inj (his'.symm.trans his)]
      have htv : t = Term.app f is := (Option.some.inj (hev.symm.trans hv)).trans hvapp
      subst htv
      rcases Set.mem_insert_iff.mp (by rwa [Term.subterms_app] at hs) with rfl | hs'
      · exact viewRepr_self_of_execActions (.app f args) n hrun hD hprim
          (fun w hw u hu => hvar w hw u hu u (Term.self_mem_subterms u)) _ hev
      · obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp hs'
        exact viewReprAllList_self_of_execActions args n hargs
          (fun x hx => hD x (hmono x hx)) (fun g hg => hprim g (by simp [Expr.fns, hg]))
          (fun w hw u hu => hvar w (by simpa [Expr.vars] using hw) u hu) is his i hi _ hsi

@[inherit_doc viewReprAll_self_of_execActions]
theorem viewReprAllList_self_of_execActions : ∀ (es : List Expr) (n : Nat) {d d' D : FDatabase},
    execActions d (encodeBuildArgs es n).2.1 = some d' → (∀ t ∈ d'.terms, t ∈ D.terms) →
    (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
    (∀ w ∈ Expr.varsList es, ∀ u, Env.lookup w d.env = some u →
      ∀ s ∈ u.subterms, ViewRepr D.toDatabase s s) →
    ∀ ts, Expr.evalList d.sig es d.env = some ts →
      ∀ i ∈ ts, ∀ s ∈ i.subterms, ViewRepr D.toDatabase s s
  | [], _, _, _, _, _, _, _, _, ts, hev, i, hi, _, _ => by
      obtain rfl : ([] : List Term) = ts := Option.some.inj hev
      exact absurd hi (by simp)
  | e :: es, n, d, d', D, hrun, hD, hprim, hvar, ts, hev, i, hi, s, hs => by
      rw [encodeBuildArgs_cons_actions] at hrun
      obtain ⟨d₁, hhead, htail⟩ := execActions_append hrun
      have hsig₁ : d₁.sig = d.sig := FDatabase.execActions_sig hhead
      have henv₁ : d₁.env = d.env := execActions_env_of_isSet (encodeBuild_isSet e n) hhead
      rw [Expr.evalList] at hev
      obtain ⟨t, ht, hev⟩ := Option.bind_eq_some_iff.mp hev
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp hev
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact viewReprAll_self_of_execActions e n hhead
          (fun x hx => hD x ((FDatabase.execActions_lists htail).1 x hx))
          (fun g hg => hprim g (by simp [Expr.fnsList, hg]))
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u hu) _ ht s hs
      · exact viewReprAllList_self_of_execActions es (encodeBuild e n).2.2 htail hD
          (fun g hg => hprim g (by simp [Expr.fnsList, hg]))
          (fun w hw u hu => hvar w (by simp [Expr.varsList, hw]) u
            (by rw [henv₁] at hu; exact hu))
          ts' (by rw [hsig₁, henv₁]; exact hts') i hi' s hs
end

@[inherit_doc viewReprAll_self_of_execActions]
theorem viewReprAll_self_of_execProgramM (e : Expr) (n : Nat) {d D : FDatabase} {p : Program}
    (hrun : d.execProgramM ((encodeBuild e n).2.1.map Cmd.action ++ p) = some D)
    (hprim : ∀ g ∈ e.fns, Prim.ofName g = none)
    (hvar : ∀ w ∈ e.vars, ∀ u, Env.lookup w d.env = some u →
      ∀ s ∈ u.subterms, ViewRepr D.toDatabase s s)
    {t : Term} (hev : e.eval d.sig d.env = some t) :
    ∀ s ∈ t.subterms, ViewRepr D.toDatabase s s := by
  obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  obtain ⟨m, hm, hmm⟩ := exists_execActions_of_execProgramM (encodeBuild_isSet e n) hblock
  exact viewReprAll_self_of_execActions e n hm
    (fun x hx => FDatabase.execProgramM_terms hafter x (hmm x hx)) hprim hvar t hev

/-! ##### What the `union` head's selectors evaluate to -/

/-- A primitive application, evaluated. -/
private theorem eval_prim_app {s : Signature} {σ : Env} {f : FnName} {p : Prim}
    {args : List Expr} {is : List Term} {t : Term} (hp : Prim.ofName f = some p)
    (hargs : Expr.evalList s args σ = some is) (happ : p.apply is = some t) :
    (Expr.app f args).eval s σ = some t := by
  simp only [Expr.eval, hp, hargs, Option.bind_some]
  exact happ

/-- **`(if (ordering-gt e₁ e₂) ea eb)`, evaluated.** `ordering-gt` is strict, so a tie takes the
`else` branch; this is the one shape `encodeAction`'s `union` emits, four times over. -/
theorem eval_ifGt {s : Signature} {σ : Env} {e₁ e₂ ea eb : Expr} {t₁ t₂ ta tb : Term}
    (h₁ : e₁.eval s σ = some t₁) (h₂ : e₂.eval s σ = some t₂)
    (ha : ea.eval s σ = some ta) (hb : eb.eval s σ = some tb) :
    (ifE (gtE e₁ e₂) ea eb).eval s σ = some (if Term.blt t₂ t₁ then ta else tb) := by
  have hgt : (gtE e₁ e₂).eval s σ = some (.lit (.bool (Term.blt t₂ t₁))) :=
    eval_prim_app (p := .orderingGt) (is := [t₁, t₂]) rfl
      (by simp [Expr.evalList, h₁, h₂]) rfl
  exact eval_prim_app (p := .ifThenElse)
    (is := [Term.lit (.bool (Term.blt t₂ t₁)), ta, tb]) rfl
    (by simp [Expr.evalList, hgt, ha, hb]) rfl

/-! ##### What a source command does, on the constructor fragment

`CmdStep` is `cmdEffect` followed by a merge phase, and on an all-constructors signature the
phase is empty (`MergeClosure.eq_of_allConstructors`). So a source command that fires no rule is
the function `evalAction` or a field update, and `evalAction_eq_some` reads it back. -/

theorem cmdStep_action_eq {sd sd' : Database} {a : Action} (hsig : sd.sig.AllConstructors)
    (h : CmdStep sd (.action a) sd') : evalAction sd a = some sd' := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : evalAction sd a = some d := hreach
  have heq : sd' = d := MergeClosure.eq_of_allConstructors (db := d)
    (by rw [evalAction_sig hd]; exact hsig) hcl
  rw [heq]
  exact hd

theorem cmdStep_rule_fields {sd sd' : Database} {r : Rule} (hsig : sd.sig.AllConstructors)
    (h : CmdStep sd (.rule r) sd') : sd'.eqs = sd.eqs ∧ sd'.env = sd.env := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : some { sd with rules := insert r sd.rules } = some d := hreach
  have hdsig : d.sig.AllConstructors := by rw [← Option.some.inj hd]; exact hsig
  have heq : sd' = d := MergeClosure.eq_of_allConstructors (db := d) hdsig hcl
  rw [heq, ← Option.some.inj hd]
  exact ⟨rfl, rfl⟩

theorem cmdStep_decl_fields {sd sd' : Database} {f : FnName} {dc : FnDecl}
    (hsig : sd.sig.AllConstructors) (hdc : Cmd.CtorDecl (.decl f dc))
    (h : CmdStep sd (.decl f dc) sd') : sd'.eqs = sd.eqs ∧ sd'.env = sd.env := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : some { sd with sig := Function.update sd.sig f (some dc) } = some d := hreach
  have hdsig : d.sig.AllConstructors := by
    rw [← Option.some.inj hd]; exact hsig.sigBind hdc
  have heq : sd' = d := MergeClosure.eq_of_allConstructors (db := d) hdsig hcl
  rw [heq, ← Option.some.inj hd]
  exact ⟨rfl, rfl⟩

/-- A `(name, arity)` pair one command applies is one the whole program applies. -/
theorem mem_program_ctors {Q : Program} {c : Cmd} (hc : c ∈ Q) {p : FnName × Nat}
    (hp : p ∈ c.ctors) : p ∈ Q.ctors := by
  rw [Program.ctors, List.mem_dedup, List.mem_flatMap]
  exact ⟨c, hc, hp⟩

/-- Every command of a build's block plus its rebuild runs only `set`s. -/
theorem actionsAreSets_block {as : List Action} (h : ∀ a ∈ as, a.IsSet) :
    ∀ c ∈ as.map Cmd.action ++ [Cmd.saturate rebuildRuleset], c.ActionsAreSets := by
  intro c hc
  rcases List.mem_append.mp hc with hc' | hc'
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc'
    exact h a ha
  · obtain rfl : c = Cmd.saturate rebuildRuleset := by simpa using hc'
    trivial

/-! ##### The `@UF` row an encoded `union` writes -/

/-- **The edge a `union` head records, read back.** `execAction_set` returns the row at the key
`ordering-max` picked and the value `ordering-min` picked, and `eval_ifGt` says which endpoint
each is; the disjunction below is that choice. The proof column is existential — which
justification the edge carries is not what being an edge means. -/
theorem out_uf_of_execProgramM {td D : FDatabase} {e₁ e₂ : Expr} {t₁ t₂ : Term} {p : Program}
    (hrun : td.execProgramM
      (Cmd.action (.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]) :: p) = some D)
    (h₁ : e₁.eval td.sig td.env = some t₁) (h₂ : e₂.eval td.sig td.env = some t₂) :
    (∃ pf, D.toDatabase.Out ufName [t₁] [t₂, pf]) ∨
      (∃ pf, D.toDatabase.Out ufName [t₂] [t₁, pf]) := by
  rw [FDatabase.execProgramM, FDatabase.execCmdM] at hrun
  obtain ⟨td₃, hcmd, hafter⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨m, hact, hmerge⟩ := Option.bind_eq_some_iff.mp hcmd
  obtain ⟨ks, vs, hks, hvs, rfl⟩ := execAction_set hact
  obtain ⟨kv, hkv, rfl⟩ := Expr.evalList_singleton hks
  obtain ⟨mv, pf, hmv, -, rfl⟩ := Expr.evalList_pair hvs
  have hmem : ∀ s ∈ (Term.app ufName ([kv] ++ [mv, pf])).subterms, s ∈ D.toDatabase.terms := by
    intro s hs
    exact FDatabase.mem_toDatabase_terms.mpr (FDatabase.execProgramM_terms hafter s
      (FDatabase.mergeSaturateF_terms hmerge s
        (FDatabase.mem_addRow_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr hs)))))
  have hout : D.toDatabase.Out ufName [kv] [mv, pf] :=
    Database.out_self (hmem _ (Term.self_mem_subterms _))
      (by intro a ha; obtain rfl : a = kv := by simpa using ha
          exact hmem a (Term.arg_subterms (by simp) (Term.self_mem_subterms a)))
  have hk := Option.some.inj (hkv.symm.trans (eval_ifGt h₁ h₂ h₁ h₂))
  have hm := Option.some.inj (hmv.symm.trans (eval_ifGt h₁ h₂ h₂ h₁))
  cases hb : Term.blt t₂ t₁ with
  | false =>
      rw [hb] at hk hm
      simp only [Bool.false_eq_true, if_false] at hk hm
      subst hk; subst hm
      exact Or.inr ⟨pf, hout⟩
  | true =>
      rw [hb] at hk hm
      simp only [if_true] at hk hm
      subst hk; subst hm
      exact Or.inl ⟨pf, hout⟩

/-! ##### The invariant -/

/-- **What the command induction carries.**

The first two clauses are the two clauses of `Database.UnionsJoined` this induction is for, at
the state `D` the *whole* run finishes at. That is what makes them composable: the rebuild
overwrites rows and only the entry term survives, so "the block wrote it" is never a fact about
the state the next command starts from.

The last two are bookkeeping. `env` is what makes a source `let`'s value the encoded `let`'s
value — `encodeBuild`'s naming expression *is* the source expression (`encodeBuild_fst`), and
`Expr.eval_sigIndep` needs nothing of the two signatures. `state` is what makes every source
command's merge phase empty. -/
structure ReadsSelfInv (sd : Database) (td D : FDatabase) : Prop where
  /-- Every source term reads to itself at the state the run finishes at. -/
  terms : ∀ t ∈ sd.terms, ViewRepr D.toDatabase t t
  /-- Every equation the source asserts between distinct terms has its `@UF` edge there. -/
  edges : ∀ a b, (a, b) ∈ sd.eqs → a ≠ b →
    (∃ pf, D.toDatabase.Out ufName [a] [b, pf]) ∨ (∃ pf, D.toDatabase.Out ufName [b] [a, pf])
  /-- The two environments are the same list. -/
  env : td.env = sd.env
  /-- The source is still in the constructor fragment. -/
  state : sd.CtorState

/-- **The `hvar` obligation, out of the invariant.** A variable's value is a term the source
holds (`Database.WF.envInTerms`) and so is every subterm of it (`Database.WF.subtermClosed`), so
the `terms` clause covers exactly what a build over that variable asks for. This is the shape
`rbState2_viewRepr_W` exhibits at one command; here it is at every command. -/
theorem ReadsSelfInv.hvar {sd : Database} {td D : FDatabase} (h : ReadsSelfInv sd td D)
    {w : Var} {u : Term} (hu : Env.lookup w td.env = some u) :
    ∀ s ∈ u.subterms, ViewRepr D.toDatabase s s := by
  intro s hs
  rw [h.env] at hu
  exact h.terms s (h.state.wf.subtermClosed u (h.state.wf.envInTerms _ (Env.mem_of_lookup hu)) hs)

/-- The invariant's two data clauses, which is what the residue below concludes. -/
def BuiltRead (sd : Database) (D : FDatabase) : Prop :=
  (∀ t ∈ sd.terms, ViewRepr D.toDatabase t t) ∧
    ∀ a b, (a, b) ∈ sd.eqs → a ≠ b →
      (∃ pf, D.toDatabase.Out ufName [a] [b, pf]) ∨ (∃ pf, D.toDatabase.Out ufName [b] [a, pf])

/-! ##### Source-side bookkeeping -/

/-- A round leaves the environment alone: `RunRules` takes it from the pre-state and a merge
phase restores it. -/
theorem runStep_env {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.env = db.env := (MergeClosure.envRules h).1

@[inherit_doc runStep_env]
theorem runReach_env {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.env = db.env := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [runStep_env hstep, ih]

theorem cmdStep_env_of_run {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.run R) sd') : sd'.env = sd.env := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : some (RunRules R sd) = some d := hreach
  rw [(MergeClosure.envRules hcl).1, ← Option.some.inj hd]
  rfl

theorem cmdStep_env_of_saturate {sd sd' : Database} {R : RulesetName}
    (h : CmdStep sd (.saturate R) sd') : sd'.env = sd.env :=
  runReach_env (cmdStep_saturate_iff.mp h).1

/-- **The equations `Database.addTerm` records are reflexive**, so they cost the `edges` clause
nothing. -/
theorem eq_of_mem_addTerm_eqs {db : Database} {t : Term} {p : Term × Term}
    (hp : p ∈ (db.addTerm t).eqs) : p ∈ db.eqs ∨ p.1 = p.2 := by
  rcases hp with h | h
  · exact Or.inl h
  · obtain ⟨s, -, hs⟩ := h
    exact Or.inr (by rw [← hs])

@[inherit_doc eq_of_mem_addTerm_eqs]
theorem mem_addEq_eqs {db : Database} {a b : Term} {p : Term × Term}
    (hp : p ∈ (db.addEq a b).eqs) : p = (a, b) ∨ p ∈ db.eqs ∨ p.1 = p.2 := by
  rcases Set.mem_insert_iff.mp hp with h | h
  · exact Or.inl h
  · rcases eq_of_mem_addTerm_eqs h with h' | h'
    · rcases eq_of_mem_addTerm_eqs h' with h'' | h''
      · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr h'')
    · exact Or.inr (Or.inr h')

/-! ##### The one case that does not close -/

/-- **The command induction's rule-firing case. Not proved.**

The five other commands are read-backs of `set`s the encoder emitted, and those read-backs are
proved (`viewReprAll_self_of_execProgramM`, `out_uf_of_execProgramM`). A `Cmd.run` or a
`Cmd.saturate` is not one: the terms it adds are the ones a **source rule firing** built, and to
read them back the encoded rule has to have fired at the substitution the source fired at.

**Why the invariant is the right hypothesis for that, and still not enough.** `ViewRepr D t t` —
the reading at the term *itself* rather than at some id of it — is what makes the target's
substitution available: a source premise term `t` is matched by the encoded query at the id `t`,
because the invariant says the target holds a view row whose e-class column is `t`. That is why
`readsSelf` has to be *carried* rather than proved command by command, and it is why a head that
builds over an id the source query never named is no obstacle — the ids are the source terms
themselves. What is missing is one step further down: `matchQuery` reads `d.rows` at a `.merge`
function (`patternHolds`), and every `@fView` is one, so a firing needs the premise row to be
**current in the index at the state the round starts from**, while the invariant carries
entry-term membership at the state the run *finishes* at. Those are different claims and the
difference is not bookkeeping: `mergeOneOriented` deletes the row a collision displaces and the
rebuild re-`set`s it at the leader, so between a build and a run the row moves.

**The invariant that would supply it is named and refuted.** `FDatabase.IndexCurrent`
(`Proofs/Merge.lean`) is the converse of `FDatabase.IndexOk.entry` — every entry term still
current in the index — and `cxTgt_not_indexCurrent` is a compiled state, built by the
interpreter's own writers over a source `union`, where it fails. So what is missing here is not
a property of the final index but a run-wide one: the rows a block writes are current at the
`Cmd.saturate rebuildRuleset` that immediately follows it, and only `terms` carries the result
past a later merge. `FDatabase.RoundClosed` is the fixpoint half of it, proved
(`roundClosed_of_execProgramM`); this is the half that is not.

Stated over both firing commands at once, because `encodeCmd` gives them the same block:
`[c, Cmd.saturate rebuildRuleset]`. -/
theorem builtRead_fire {R : RulesetName} {c : Cmd} {sd sd' : Database} {td td' D : FDatabase}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hrun : td.execProgramM [c, Cmd.saturate rebuildRuleset] = some td')
    (hmono : ∀ t ∈ td'.terms, t ∈ D.terms) (hinv : ReadsSelfInv sd td D) :
    BuiltRead sd' D := by
  sorry

/-! ##### One command -/

/-- **The invariant survives one source command.** Six cases: five read-backs of the `set`s
`encodeCmd` emitted for that command, and `builtRead_fire`. -/
theorem readsSelfInv_step {Q : Program} (hQ : Q.EncodeDomain) {c : Cmd} (hc : c ∈ Q)
    {n i : Nat} {sd sd' : Database} {td D : FDatabase} {rest : Program}
    (hstep : CmdStep sd c sd')
    (hrun : td.execProgramM ((encodeCmd c n i).1 ++ rest) = some D)
    (hinv : ReadsSelfInv sd td D) :
    ∃ td', td.execProgramM (encodeCmd c n i).1 = some td' ∧ ReadsSelfInv sd' td' D := by
  have hstate' : sd'.CtorState := hstep.ctorState hinv.state (hQ.ctorDecls c hc)
  obtain ⟨td', hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  have hmono : ∀ t ∈ td'.terms, t ∈ D.terms := FDatabase.execProgramM_terms hafter
  refine ⟨td', hblock, ?_⟩
  cases c with
  | decl f dc =>
      obtain ⟨heqs, henv⟩ := cmdStep_decl_fields hinv.state.sig (hQ.ctorDecls _ hc) hstep
      obtain rfl : td' = td := by
        rw [show (encodeCmd (Cmd.decl f dc) n i).1 = [] from rfl, FDatabase.execProgramM,
          Option.some.injEq] at hblock
        exact hblock.symm
      have hsub : sd'.eqs ⊆ sd.eqs := fun p hp => by rw [heqs] at hp; exact hp
      refine ⟨fun t ht => hinv.terms t (Database.mem_terms_of_eqs hsub ht), ?_, ?_, hstate'⟩
      · intro a b hab hne
        exact hinv.edges a b (hsub hab) hne
      · rw [hinv.env, henv]
  | rule r =>
      obtain ⟨heqs, henv⟩ := cmdStep_rule_fields hinv.state.sig hstep
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.rule r) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.rule (encodeRule i r n).1] := hc'
        obtain rfl : c' = Cmd.rule (encodeRule i r n).1 := by simpa using hc2
        trivial
      have hsub : sd'.eqs ⊆ sd.eqs := fun p hp => by rw [heqs] at hp; exact hp
      refine ⟨fun t ht => hinv.terms t (Database.mem_terms_of_eqs hsub ht), ?_, ?_, hstate'⟩
      · intro a b hab hne
        exact hinv.edges a b (hsub hab) hne
      · rw [FDatabase.execProgramM_env hsets hblock, hinv.env, henv]
  | run R =>
      obtain ⟨hterms, hedges⟩ := builtRead_fire (Or.inl rfl) hstep hblock hmono hinv
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.run R) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.run R, Cmd.saturate rebuildRuleset] := hc'
        have hd : c' = Cmd.run R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using hc2
        rcases hd with rfl | rfl <;> trivial
      refine ⟨hterms, hedges, ?_, hstate'⟩
      rw [FDatabase.execProgramM_env hsets hblock, hinv.env, cmdStep_env_of_run hstep]
  | saturate R =>
      obtain ⟨hterms, hedges⟩ := builtRead_fire (Or.inr rfl) hstep hblock hmono hinv
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.saturate R) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.saturate R, Cmd.saturate rebuildRuleset] := hc'
        have hd : c' = Cmd.saturate R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using hc2
        rcases hd with rfl | rfl <;> trivial
      refine ⟨hterms, hedges, ?_, hstate'⟩
      rw [FDatabase.execProgramM_env hsets hblock, hinv.env, cmdStep_env_of_saturate hstep]
  | action a =>
      have hev : evalAction sd a = some sd' := cmdStep_action_eq hinv.state.sig hstep
      rcases evalAction_eq_some hev with
        ⟨e, tS, rfl, htS, rfl⟩ | ⟨v, e, tS, rfl, htS, rfl⟩ |
        ⟨e₁, e₂, t₁, t₂, rfl, ht₁, ht₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, -, -, -⟩
      · -- a top-level build
        have hprim : ∀ g ∈ e.fns, Prim.ofName g = none :=
          noPrim_of_mem_ctors hQ (fun p hp => mem_program_ctors hc hp)
        have hrun' : td.execProgramM ((encodeBuild e n).2.1.map Cmd.action
            ++ ([Cmd.saturate rebuildRuleset] ++ rest)) = some D := by
          rw [← List.append_assoc]; exact hrun
        have htS2 : e.eval sd.sig td.env = some tS := by rw [hinv.env]; exact htS
        obtain ⟨tT, htT⟩ := exists_eval_of_execProgramM_encodeBuild e n hrun'
          (fun w hw => Expr.exists_lookup_of_eval e htS2 w hw)
        have htT2 : e.eval td.sig td.env = some tS := by
          rw [htT, Expr.eval_sigIndep e htT htS2]
        have hall : ∀ s ∈ tS.subterms, ViewRepr D.toDatabase s s :=
          viewReprAll_self_of_execProgramM e n hrun' hprim (fun w _ u hu => hinv.hvar hu) htT2
        have hsets : ∀ c' ∈ (encodeCmd (Cmd.action (Action.expr e)) n i).1,
            c'.ActionsAreSets := by
          change ∀ c' ∈ (encodeBuild e n).2.1.map Cmd.action
            ++ [Cmd.saturate rebuildRuleset], c'.ActionsAreSets
          exact actionsAreSets_block (encodeBuild_isSet e n)
        refine ⟨?_, ?_, ?_, hstate'⟩
        · intro t ht
          rw [Database.addTerm_terms] at ht
          rcases ht with ht' | ht'
          · exact hinv.terms t ht'
          · exact hall t ht'
        · intro x y hxy hne
          rcases eq_of_mem_addTerm_eqs hxy with hxy' | hxy'
          · exact hinv.edges x y hxy' hne
          · exact absurd hxy' hne
        · rw [FDatabase.execProgramM_env hsets hblock]; exact hinv.env
      · -- a top-level let
        have hprim : ∀ g ∈ e.fns, Prim.ofName g = none :=
          noPrim_of_mem_ctors hQ (fun p hp => mem_program_ctors hc hp)
        have hb1 : (encodeAction fiatE (Action.letBind v e) n).1
            = (encodeBuild e n).2.1 ++ [Action.letBind v e] := by
          change (encodeBuild e n).2.1 ++ [Action.letBind v (encodeBuild e n).1] = _
          rw [encodeBuild_fst]
        have hblk : (encodeCmd (Cmd.action (Action.letBind v e)) n i).1
            = (encodeBuild e n).2.1.map Cmd.action
              ++ [Cmd.action (Action.letBind v e), Cmd.saturate rebuildRuleset] := by
          change (encodeAction fiatE (Action.letBind v e) n).1.map Cmd.action
            ++ [Cmd.saturate rebuildRuleset] = _
          rw [hb1]; simp
        have hrun' : td.execProgramM ((encodeBuild e n).2.1.map Cmd.action
            ++ ([Cmd.action (Action.letBind v e), Cmd.saturate rebuildRuleset] ++ rest))
            = some D := by
          rw [← List.append_assoc, ← hblk]; exact hrun
        have htS2 : e.eval sd.sig td.env = some tS := by rw [hinv.env]; exact htS
        obtain ⟨tT, htT⟩ := exists_eval_of_execProgramM_encodeBuild e n hrun'
          (fun w hw => Expr.exists_lookup_of_eval e htS2 w hw)
        have htT2 : e.eval td.sig td.env = some tS := by
          rw [htT, Expr.eval_sigIndep e htT htS2]
        have hall : ∀ s ∈ tS.subterms, ViewRepr D.toDatabase s s :=
          viewReprAll_self_of_execProgramM e n hrun' hprim (fun w _ u hu => hinv.hvar hu) htT2
        rw [hblk] at hblock
        obtain ⟨td₁, hbuilds, hlet⟩ := FDatabase.execProgramM_append hblock
        have hsig₁ : td₁.sig = td.sig :=
          FDatabase.execProgramM_sig_of_noDecl
            (by intro c' hc'; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc'; trivial) hbuilds
        have henv₁ : td₁.env = td.env :=
          FDatabase.execProgramM_env
            (by intro c' hc'; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
                exact encodeBuild_isSet e n b hb) hbuilds
        rw [FDatabase.execProgramM] at hlet
        obtain ⟨td₂, hcmd, hsat⟩ := Option.bind_eq_some_iff.mp hlet
        obtain ⟨tL, htL, henv₂, -, -⟩ := FDatabase.execCmdM_letBind hcmd
        rw [hsig₁, henv₁] at htL
        rw [Expr.eval_sigIndep e htL htS2] at henv₂
        have henv' : td'.env = (v, tS) :: td.env := by
          rw [FDatabase.execProgramM_env
              (by intro c' hc'
                  have hc2 : c' ∈ [Cmd.saturate rebuildRuleset] := hc'
                  obtain rfl : c' = Cmd.saturate rebuildRuleset := by simpa using hc2
                  trivial) hsat, henv₂, henv₁]
        refine ⟨?_, ?_, ?_, hstate'⟩
        · intro t ht
          have ht2 : t ∈ (sd.addTerm tS).terms :=
            Database.mem_terms_of_eqs
              (d₁ := ({ sd.addTerm tS with env := (v, tS) :: sd.env } : Database))
              (d₂ := sd.addTerm tS) (fun p hp => hp) ht
          rw [Database.addTerm_terms] at ht2
          rcases ht2 with ht' | ht'
          · exact hinv.terms t ht'
          · exact hall t ht'
        · intro x y hxy hne
          rcases eq_of_mem_addTerm_eqs (hxy : (x, y) ∈ (sd.addTerm tS).eqs) with hxy' | hxy'
          · exact hinv.edges x y hxy' hne
          · exact absurd hxy' hne
        · rw [henv', hinv.env]
      · -- a top-level union
        have hprim₁ : ∀ g ∈ e₁.fns, Prim.ofName g = none :=
          noPrim_of_mem_ctors hQ (fun p hp => mem_program_ctors hc (List.mem_append_left _ hp))
        have hprim₂ : ∀ g ∈ e₂.fns, Prim.ofName g = none :=
          noPrim_of_mem_ctors hQ (fun p hp => mem_program_ctors hc (List.mem_append_right _ hp))
        have hb1 : (encodeAction fiatE (Action.union e₁ e₂) n).1
            = (encodeBuild e₁ n).2.1 ++ (encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1
              ++ [Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]] := by
          change (encodeBuild e₁ n).2.1 ++ (encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1
            ++ [Action.set ufName
                [maxE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1]
                [minE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1,
                 fiatE]] = _
          rw [encodeBuild_fst, encodeBuild_fst]
        have hsetsA : ∀ b ∈ (encodeAction fiatE (Action.union e₁ e₂) n).1, b.IsSet := by
          rw [hb1]
          intro b hb
          rcases List.mem_append.mp hb with hb' | hb'
          · rcases List.mem_append.mp hb' with hb'' | hb''
            · exact encodeBuild_isSet e₁ n b hb''
            · exact encodeBuild_isSet e₂ _ b hb''
          · obtain rfl : b = Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE] := by
              simpa using hb'
            trivial
        have hsets : ∀ c' ∈ (encodeCmd (Cmd.action (Action.union e₁ e₂)) n i).1,
            c'.ActionsAreSets := by
          change ∀ c' ∈ (encodeAction fiatE (Action.union e₁ e₂) n).1.map Cmd.action
            ++ [Cmd.saturate rebuildRuleset], c'.ActionsAreSets
          exact actionsAreSets_block hsetsA
        have hblk : (encodeCmd (Cmd.action (Action.union e₁ e₂)) n i).1
            = (encodeBuild e₁ n).2.1.map Cmd.action
              ++ ((encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1.map Cmd.action
                ++ [Cmd.action (Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]),
                    Cmd.saturate rebuildRuleset]) := by
          change (encodeAction fiatE (Action.union e₁ e₂) n).1.map Cmd.action
            ++ [Cmd.saturate rebuildRuleset] = _
          rw [hb1]; simp
        have htS1 : e₁.eval sd.sig td.env = some t₁ := by rw [hinv.env]; exact ht₁
        have htS2 : e₂.eval sd.sig td.env = some t₂ := by rw [hinv.env]; exact ht₂
        have hrun₁ : td.execProgramM ((encodeBuild e₁ n).2.1.map Cmd.action
            ++ (((encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1.map Cmd.action
              ++ [Cmd.action (Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]),
                  Cmd.saturate rebuildRuleset]) ++ rest)) = some D := by
          rw [← List.append_assoc, ← hblk]; exact hrun
        obtain ⟨tT₁, htT₁⟩ := exists_eval_of_execProgramM_encodeBuild e₁ n hrun₁
          (fun w hw => Expr.exists_lookup_of_eval e₁ htS1 w hw)
        have htT1' : e₁.eval td.sig td.env = some t₁ := by
          rw [htT₁, Expr.eval_sigIndep e₁ htT₁ htS1]
        have hall₁ : ∀ s ∈ t₁.subterms, ViewRepr D.toDatabase s s :=
          viewReprAll_self_of_execProgramM e₁ n hrun₁ hprim₁
            (fun w _ u hu => hinv.hvar hu) htT1'
        obtain ⟨td₁, hb₁, hrest₁⟩ := FDatabase.execProgramM_append hrun₁
        have hsig₁ : td₁.sig = td.sig :=
          FDatabase.execProgramM_sig_of_noDecl
            (by intro c' hc'; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc'; trivial) hb₁
        have henv₁ : td₁.env = td.env :=
          FDatabase.execProgramM_env
            (by intro c' hc'; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
                exact encodeBuild_isSet e₁ n b hb) hb₁
        have hrun₂ : td₁.execProgramM
            ((encodeBuild e₂ (encodeBuild e₁ n).2.2).2.1.map Cmd.action
              ++ ([Cmd.action (Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]),
                   Cmd.saturate rebuildRuleset] ++ rest)) = some D := by
          rw [← List.append_assoc]; exact hrest₁
        have htS2' : e₂.eval sd.sig td₁.env = some t₂ := by rw [henv₁]; exact htS2
        obtain ⟨tT₂, htT₂⟩ := exists_eval_of_execProgramM_encodeBuild e₂ _ hrun₂
          (fun w hw => Expr.exists_lookup_of_eval e₂ htS2' w hw)
        have htT2' : e₂.eval td₁.sig td₁.env = some t₂ := by
          rw [htT₂, Expr.eval_sigIndep e₂ htT₂ htS2']
        have hall₂ : ∀ s ∈ t₂.subterms, ViewRepr D.toDatabase s s :=
          viewReprAll_self_of_execProgramM e₂ _ hrun₂ hprim₂
            (fun w _ u hu => hinv.hvar (by rw [henv₁] at hu; exact hu)) htT2'
        obtain ⟨td₂, hb₂, hrest₂⟩ := FDatabase.execProgramM_append hrun₂
        have hsig₂ : td₂.sig = td₁.sig :=
          FDatabase.execProgramM_sig_of_noDecl
            (by intro c' hc'; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc'; trivial) hb₂
        have henv₂ : td₂.env = td₁.env :=
          FDatabase.execProgramM_env
            (by intro c' hc'; obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
                exact encodeBuild_isSet e₂ _ b hb) hb₂
        have hedge : (∃ pf, D.toDatabase.Out ufName [t₁] [t₂, pf]) ∨
            (∃ pf, D.toDatabase.Out ufName [t₂] [t₁, pf]) :=
          out_uf_of_execProgramM hrest₂ (by rw [hsig₂, hsig₁, henv₂, henv₁]; exact htT1')
            (by rw [hsig₂, henv₂]; exact htT2')
        refine ⟨?_, ?_, ?_, hstate'⟩
        · intro t ht
          rw [Database.addEq_terms] at ht
          rcases ht with ht' | ht'
          · rcases ht' with ht'' | ht''
            · exact hinv.terms t ht''
            · exact hall₁ t ht''
          · exact hall₂ t ht'
        · intro x y hxy hne
          rcases mem_addEq_eqs hxy with hxy' | hxy' | hxy'
          · obtain ⟨rfl, rfl⟩ : x = t₁ ∧ y = t₂ := by
              have := hxy'
              simp only [Prod.mk.injEq] at this
              exact this
            exact hedge
          · exact hinv.edges x y hxy' hne
          · exact absurd hxy' hne
        · rw [FDatabase.execProgramM_env hsets hblock]; exact hinv.env
      · exact (show False from hQ.noSet _ hc).elim

/-! ##### Every command

The induction. `Q` is the whole source program, fixed, so that `hQ`'s clauses are available at
each command; `p` is the suffix still to run, and `rest` is whatever the encoded run does after
it. -/

/-- Running `p` and then `q` is running `p ++ q`, forwards. -/
theorem FDatabase.execProgramM_append' {p q : Program} : ∀ {d m D : FDatabase},
    d.execProgramM p = some m → m.execProgramM q = some D →
      d.execProgramM (p ++ q) = some D := by
  induction p with
  | nil =>
    intro d m D h hq
    rw [FDatabase.execProgramM, Option.some.injEq] at h
    rw [List.nil_append, h]
    exact hq
  | cons c cs ih =>
    intro d m D h hq
    rw [FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [List.cons_append, FDatabase.execProgramM, h₁, Option.bind_some]
    exact ih h₂ hq

/-- **The command induction.** One `readsSelfInv_step` per source command, threading the state
the encoded block left. -/
theorem readsSelfInv_of_programStep {Q : Program} (hQ : Q.EncodeDomain) :
    ∀ (p : Program) {n i : Nat} {sd sd' : Database} {td D : FDatabase} {rest : Program},
      (∀ c ∈ p, c ∈ Q) → ProgramStep sd p sd' →
      td.execProgramM ((encodeCmds p n i).1 ++ rest) = some D →
      ReadsSelfInv sd td D →
      ∃ td', td.execProgramM (encodeCmds p n i).1 = some td' ∧ ReadsSelfInv sd' td' D := by
  intro p
  induction p with
  | nil =>
    intro n i sd sd' td D rest _ hsrc _ hinv
    obtain rfl := hsrc.nil_inv
    exact ⟨td, rfl, hinv⟩
  | cons c cs ih =>
    intro n i sd sd' td D rest hsub hsrc hrun hinv
    obtain ⟨sd₁, hstep, hrest⟩ := hsrc.cons_inv
    have hcmds : (encodeCmds (c :: cs) n i).1
        = (encodeCmd c n i).1
          ++ (encodeCmds cs (encodeCmd c n i).2.1 (encodeCmd c n i).2.2).1 := rfl
    rw [hcmds, List.append_assoc] at hrun
    obtain ⟨td₁, hb, hinv₁⟩ :=
      readsSelfInv_step hQ (hsub c List.mem_cons_self) hstep hrun hinv
    obtain ⟨m, hm, hafter⟩ := FDatabase.execProgramM_append hrun
    obtain rfl : m = td₁ := Option.some.inj (hm.symm.trans hb)
    obtain ⟨td₂, hb₂, hinv₂⟩ :=
      ih (fun c' hc' => hsub c' (List.mem_cons_of_mem c hc')) hrest hafter hinv₁
    exact ⟨td₂, by rw [hcmds]; exact FDatabase.execProgramM_append' hb hb₂, hinv₂⟩

/-! ##### From the empty state

`encode P` is the prelude and then `encodeCmds P`. The prelude is declarations and maintenance
rules — it runs no action at all — so the environment it leaves is the empty one the source
starts with, and the invariant holds there with both data clauses vacuous. -/

theorem actionsAreSets_ruleProofDecls : ∀ (rs : List Rule) (i : Nat),
    ∀ c ∈ ruleProofDecls rs i, c.ActionsAreSets
  | [], _ => by simp [ruleProofDecls]
  | r :: rs, i => by
      intro c hc
      rw [ruleProofDecls, List.mem_cons] at hc
      rcases hc with rfl | hc
      · trivial
      · exact actionsAreSets_ruleProofDecls rs (i + 1) c hc

/-- **The prelude runs no action**, so it moves neither the environment nor anything else the
invariant reads. -/
theorem actionsAreSets_encodePrelude (P : Program) :
    ∀ c ∈ encodePrelude P, c.ActionsAreSets := by
  intro c hc
  rw [encodePrelude] at hc
  rcases List.mem_append.mp hc with h | h
  · rcases List.mem_append.mp h with h₁ | h₁
    · rw [proofDecls] at h₁
      rcases List.mem_append.mp h₁ with h₂ | h₂
      · rcases List.mem_append.mp h₂ with h₃ | h₃
        · have h₄ : c = Cmd.decl fiatName (proofDecl 0) ∨ c = Cmd.decl symName (proofDecl 1) ∨
              c = Cmd.decl transName (proofDecl 2) := by simpa using h₃
          rcases h₄ with rfl | rfl | rfl <;> trivial
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h₃
          trivial
      · exact actionsAreSets_ruleProofDecls _ _ c h₂
    · rcases List.mem_cons.mp h₁ with rfl | h₂
      · trivial
      · obtain ⟨fk, -, h₃⟩ := List.mem_flatMap.mp h₂
        have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
        rcases h₄ with rfl | rfl | rfl <;> trivial
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
    trivial

/-- **The invariant at the state `execM` returned**, which is the two clauses `execM_readsSelf`
and `execM_edges` state. Both `td` and `D` are the final state: the induction started at the
empty source database and the state the prelude left, and finished where the run did. -/
theorem readsSelfInv_execM {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : ReadsSelfInv src tgt tgt := by
  rw [execM, encode] at htgt
  obtain ⟨td₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have henv₀ : td₀.env = [] := by
    rw [FDatabase.execProgramM_env (actionsAreSets_encodePrelude P) hprel]
    rfl
  have hinv₀ : ReadsSelfInv Database.empty td₀ tgt := by
    refine ⟨?_, ?_, ?_, Database.CtorState.empty⟩
    · intro t ht
      exact absurd ht (by simp)
    · intro a b hab
      exact absurd hab (by simp [Database.empty])
    · rw [henv₀]
      rfl
  obtain ⟨td', hb, hinv⟩ := readsSelfInv_of_programStep hdom P (fun c hc => hc) hsrc
    (by rw [List.append_nil]; exact hcmds) hinv₀
  obtain rfl : td' = tgt := Option.some.inj (hb.symm.trans hcmds)
  exact hinv

/-! ##### The invariant is not vacuous

`ENCODING.md`'s discipline: an invariant nothing satisfies carries an induction that proves
nothing. Here it is at a **source state a program reaches** and the target state the read-back
above computed, with the `terms` clause non-vacuous at positive arity and the environment
non-empty — which is what makes `ReadsSelfInv.hvar` do work rather than hold trivially. The
program is `rbState2`'s: two declarations, a top-level `let`, and a build over the variable it
bound. -/

/-- Two constructors, a global `let`, and a build over it. -/
def rbProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "W" { arity := 1, outArity := 1, merge := none },
   .action (.letBind "x" (.app "A" [])),
   .action (.expr (.app "W" [.var "x"]))]

/-- The signature the two declarations install. -/
def rbSrcSig : Signature :=
  Function.update (Function.update Database.empty.sig
    "A" (some { arity := 0, outArity := 1, merge := none }))
    "W" (some { arity := 1, outArity := 1, merge := none })

/-- After the two declarations: no term yet. -/
def rbSrcBase : Database := { Database.empty with sig := rbSrcSig }

/-- **The source state `rbProgram` runs to**: `(A)` bound to `x` and `(W (A))` built. -/
def rbSrc : Database :=
  { (rbSrcBase.addTerm (.app "A" [])).addTerm (.app "W" [.app "A" []]) with env := rbEnv }

private theorem rbSrcBase_terms : rbSrcBase.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [rbSrcBase, Database.empty] at hu

theorem rbSrc_terms :
    rbSrc.terms = (Term.app "A" []).subterms ∪ (Term.app "W" [Term.app "A" []]).subterms := by
  rw [Database.terms_eq_of_eqs_eq (d₁ := rbSrc)
      (d₂ := (rbSrcBase.addTerm (.app "A" [])).addTerm (.app "W" [.app "A" []])) rfl,
    Database.addTerm_terms, Database.addTerm_terms, rbSrcBase_terms, Set.empty_union]

theorem rbSrc_mem_A : Term.app "A" [] ∈ rbSrc.terms := by
  rw [rbSrc_terms]
  exact Or.inl (Term.self_mem_subterms _)

private theorem rbSrcBase_wf : rbSrcBase.WF where
  eqsRefl := fun t ht => absurd (rbSrcBase_terms ▸ ht) (by simp)
  subtermClosed := fun t ht => absurd (rbSrcBase_terms ▸ ht) (by simp)
  envInTerms := by simp [rbSrcBase, Database.empty]
  litsIsolated := by simp [Database.LitsIsolated, rbSrcBase, Database.empty]

theorem rbSrc_wf : rbSrc.WF :=
  Database.WF.setEnv ((rbSrcBase_wf.addTerm _).addTerm _)
    (by intro b hb
        obtain rfl : b = ("x", Term.app "A" []) := by simpa [rbEnv] using hb
        change Term.app "A" [] ∈ _
        rw [Database.addTerm_terms, Database.addTerm_terms, rbSrcBase_terms, Set.empty_union]
        exact Or.inl (Term.self_mem_subterms _))

theorem rbSrc_ctorState : rbSrc.CtorState where
  wf := rbSrc_wf
  sig := by
    intro f
    change ((rbSrcSig f).bind FnDecl.merge) = none
    rw [rbSrcSig]
    by_cases h₁ : f = "W"
    · rw [h₁, Function.update_self]; rfl
    · rw [Function.update_of_ne h₁]
      by_cases h₂ : f = "A"
      · rw [h₂, Function.update_self]; rfl
      · rw [Function.update_of_ne h₂]; rfl

/-- The source asserts nothing but reflexive equations, so the `edges` clause is vacuous here —
`witnessProgram` is where it is not (`execM_edges`). -/
theorem rbSrc_diag : rbSrc.Diag :=
  Database.Diag.addTerm (Database.Diag.addTerm
    (fun p hp => absurd hp (by simp [rbSrcBase, Database.empty])) _) _

/-- **And the source state is reachable.** -/
theorem rbProgram_programStep : ProgramStep Database.empty rbProgram rbSrc := by
  refine .cons ⟨_, rfl, .refl⟩ (.cons ⟨_, rfl, .refl⟩
    (.cons ⟨_, rfl, .refl⟩ (.cons ⟨rbSrc, ?_, .refl⟩ .nil)))
  change cmdEffect _ (.action (.expr (.app "W" [.var "x"]))) = some rbSrc
  simp only [cmdEffect, evalAction, Expr.eval, Expr.evalList, rbSrc]
  rfl

/-- **`ReadsSelfInv` holds, with both of the clauses that do work doing it.** `terms` is asked
at `(W (A))` — a positive-arity application, answered by the build's own view row — and at
`(A)`, answered by the *earlier* build's; `env` is a one-binding environment, so
`ReadsSelfInv.hvar` below is the composition the `let` case performs. -/
theorem rbState2_readsSelfInv : ReadsSelfInv rbSrc rbState2 rbState2 where
  terms := by
    intro t ht
    rw [rbSrc_terms] at ht
    rcases ht with ht' | ht'
    · obtain rfl : t = Term.app "A" [] := by simpa using ht'
      exact rbState2_viewRepr_A
    · rcases Set.mem_insert_iff.mp (by rwa [Term.subterms_app] at ht') with rfl | ht''
      · exact rbState2_viewRepr_W
      · obtain ⟨a, ha, hs⟩ := Set.mem_iUnion₂.mp ht''
        obtain rfl : a = Term.app "A" [] := by simpa using ha
        obtain rfl : t = Term.app "A" [] := by simpa using hs
        exact rbState2_viewRepr_A
  edges := fun a b hab hne => absurd (rbSrc_diag (a, b) hab) hne
  env := rfl
  state := rbSrc_ctorState

/-- **And `ReadsSelfInv.hvar` is discharged non-vacuously at the variable the `let` bound.**
This is `rbState2_viewRepr_W`'s `hvar` argument, now read off the invariant rather than supplied
by hand — which is exactly what `readsSelfInv_step` does once per command. -/
theorem rbState2_readsSelfInv_hvar :
    ∀ s ∈ (Term.app "A" []).subterms, ViewRepr rbState2.toDatabase s s :=
  rbState2_readsSelfInv.hvar (w := "x") rfl

/-- **The source holds no rule, so a round adds nothing.** -/
theorem rbSrc_runRules (R : RulesetName) : RunRules R rbSrc = rbSrc :=
  (runRules_eq_self_iff R rbSrc).mpr fun r hr =>
    absurd hr (by simp [rbSrc, rbSrcBase, Database.addTerm, Database.empty])

@[inherit_doc rbSrc_runRules]
theorem rbSrc_cmdStep_run (R : RulesetName) : CmdStep rbSrc (.run R) rbSrc :=
  ⟨RunRules R rbSrc, rfl, by rw [rbSrc_runRules]; exact .refl⟩

/-- A ruleset name for the round below; the program registers no rule under it, or any other. -/
def rbRuleset : RulesetName := "r"

set_option maxRecDepth 100000 in
/-- **And the encoded round writes nothing either**: `rbState2` holds no rule, so the round the
encoding emits — the source's own, followed by the rebuild — leaves the state alone. -/
theorem rbState2_execProgramM_run :
    rbState2.execProgramM [Cmd.run rbRuleset, Cmd.saturate rebuildRuleset] = some rbState2 := rfl

/-- **And `builtRead_fire`'s hypotheses are simultaneously satisfiable**, so the residue is not
a statement nothing reaches — `ENCODING.md`'s failure, twice.

Degenerately, and deliberately so: the source holds no rule, so the round adds nothing and the
encoded round writes nothing either, while the fifth hypothesis is the invariant above. The case
with content is a round that *fires*, and that one is measured rather than compiled:
`difftest correspond`'s **LOST** column is `Cong src a b` without `SameClass tgt a b`, swept with
the diagonal included over the 70 cases in `encode`'s domain — rules and runs among them — and it
is 0. That says every source term has *some* id in the target; `readsSelf` asks for the id to be
the term itself, which is the stronger claim `builtRead_fire` would supply. -/
theorem builtRead_fire_satisfiable :
    CmdStep rbSrc (.run rbRuleset) rbSrc ∧
      rbState2.execProgramM [Cmd.run rbRuleset, Cmd.saturate rebuildRuleset] = some rbState2 ∧
      (∀ t ∈ rbState2.terms, t ∈ rbState2.terms) ∧ ReadsSelfInv rbSrc rbState2 rbState2 :=
  ⟨rbSrc_cmdStep_run rbRuleset, rbState2_execProgramM_run, fun _ h => h, rbState2_readsSelfInv⟩

/-! #### The rebuild fixpoint, and the row it does not reach

All five residues want one mechanism, and it is a postcondition of `FDatabase.runSaturateM
rebuildRuleset` — the interpreter's own rebuild fixpoint, which is the only one available:
`execM_contained` says the enumerator under-fires, so `RunSaturated`, and with it `Rebuilt`,
is not a consequence of a successful run. `Proofs/Merge.lean` states and proves that
postcondition. `FDatabase.runSaturateM_roundClosed`: the state a `Cmd.saturate R` returns is
`FDatabase.RoundClosed R` — **every term one more round of `R` would derive is already
held** — and `roundClosed_of_execProgramM` below locates one at the end of every block
`encodeCmd` emits for a writing command, since every such block ends with `Cmd.saturate
rebuildRuleset`.

**That is the right shape for the residues' conclusions.** A rebuild rule's head is a `set`,
`FDatabase.addRow` records its entry term, and `Database.Out` reads `terms` and nothing else —
so "the e-class rule has fired here" and "its entry term is present" are the same statement,
and `FDatabase.RoundClosed.fired` is the second one.

**It is not the right shape for their premises, and `rows` against `terms` is exactly why.**
A round is `execRunRules`, which unions each firing into the accumulator and so only ever
adds, followed by `mergeSaturateF`, which adds terms (`mergeRound_confined`) and *deletes*
rows — `mergeOneOriented` drops the row a collision displaced. The fixpoint pins the round's
terms equal to the pre-state's, which sandwiches `execRunRules`' terms between the two; over
`rows` the sandwich does not close, because the merge phase is free to remove what the rule
phase added. So `terms` is the only field the fixpoint speaks about, while `matchQuery` — what
"the rule fired" needs — reads `d.rows` at a `.merge` function (`patternHolds`), which every
`@fView` is. The two fields genuinely differ here, and this section is the compiled statement
of the difference. -/

/-- **Where a `RoundClosed` state is.** `runSaturateM` returns only from the branch that tested
`sameData`, so the state a trailing `Cmd.saturate R` produces is a round fixpoint — and
`encodeCmd` ends every block that writes with one. -/
theorem roundClosed_of_execProgramM {R : RulesetName} {d D : FDatabase} {p : Program}
    (h : d.execProgramM (p ++ [Cmd.saturate R]) = some D) : D.RoundClosed R := by
  obtain ⟨td, -, hlast⟩ := FDatabase.execProgramM_append h
  rw [FDatabase.execProgramM] at hlast
  obtain ⟨e, he, he'⟩ := Option.bind_eq_some_iff.mp hlast
  obtain rfl : e = D := by
    rw [FDatabase.execProgramM, Option.some.injEq] at he'; exact he'
  exact FDatabase.runSaturateM_roundClosed he

/-- **And that its hypothesis is the shape `encodeCmd` emits.** A `Cmd.run`'s block is the
source round followed by the rebuild; the `.saturate` and top-level-action blocks are the same
shape (`encodeCmd`). -/
theorem encodeCmd_run_tail (R : RulesetName) (n i : Nat) :
    (encodeCmd (.run R) n i).1 = [Cmd.run R] ++ [Cmd.saturate rebuildRuleset] := rfl

/-- **The fixpoint at a state a program reaches.** Degenerately, as `builtRead_fire_satisfiable`
is: `rbState2` holds no rule, so the round it is a fixpoint of fires nothing. The
non-degenerate reading is measured rather than compiled — every one of `difftest correspond`'s
70 in-domain cases ends at a `Cmd.saturate rebuildRuleset`. -/
theorem rbState2_roundClosed : rbState2.RoundClosed rebuildRuleset :=
  roundClosed_of_execProgramM (p := [Cmd.run rbRuleset]) rbState2_execProgramM_run

/-! ##### And the half it does not give, refuted

`FDatabase.IndexCurrent` (`Proofs/Merge.lean`) is the converse of `FDatabase.IndexOk.entry`:
every merge function's entry term still current in the index, at a congruent key and the value
columns it was written with. That is what a rule firing needs of its premise, and
`cxTgt_not_indexCurrent` below refutes it — so `IndexOk` is *not* the right home for the
currency claim, and the claim is not a fourth field of it, because nothing preserves it.

The state: one nullary constructor `B`, its view entry `@BView() ↦ ((B), @Fiat)` as
`encodeBuild` writes it, the `@UF` edge `@UF((B)) ↦ ((A), @Fiat)` as a source `union` between
`(A)` and `(B)` becomes it, and the entry `@BView() ↦ ((A), @Trans @Fiat @Fiat)` the e-class
rebuild rule re-keys onto the leader. Written with `FDatabase.addRow`, which is what
`execAction` runs at a `set`, and then one `FDatabase.mergeRound`, which is what a merge phase
runs — the same discipline as `Proofs/Counterexamples.lean`'s `cexD`. Running the whole
`encode` of the source program through the *kernel* instead is not available: `matchQuery`'s
own definition computes one congruence closure per candidate substitution, and a rebuild
saturation over it exhausts the elaborator's heartbeat budget. `difftest correspond`'s
`unionCase` is the same program measured rather than compiled. -/

/-- `satSig` with a nullary `B`'s table triple added. -/
def cxSig : Signature :=
  Function.update (Function.update (Function.update satSig
    "B" (some (skolemDecl 0))) (viewName "B") (some (viewDecl 0)))
    (termName "B") (some (termDecl 0))

/-- The two e-classes the `union` puts at one view key. -/
def cxA : Term := .app "A" []

@[inherit_doc cxA] def cxB : Term := .app "B" []

/-- `@Fiat`, the justification a build writes. -/
def cxFiat : Term := .app fiatName []

/-- `@Trans @Fiat @Fiat`, the justification the e-class rebuild rule composes. -/
def cxTransFiat : Term := .app transName [cxFiat, cxFiat]

/-- The state the prelude leaves. -/
def cxBase : FDatabase := { FDatabase.empty with sig := cxSig }

/-- The three `set`s: `(B)`'s own view entry, the `union`'s `@UF` edge, and the entry the
e-class rebuild rule re-keys onto `(A)`. -/
def cxPre : FDatabase :=
  ((cxBase.addRow (viewName "B") [] [cxB, cxFiat]).addRow ufName [cxB] [cxA, cxFiat]).addRow
    (viewName "B") [] [cxA, cxTransFiat]

/-- And the merge phase that resolves the collision the third `set` created. -/
def cxTgt : FDatabase := cxPre.mergeRound

set_option maxRecDepth 100000 in
/-- **The entry term is still there.** `terms` is monotone: `mergeOneOriented` deletes rows and
never a term (`mergeOneOriented_confined`). -/
theorem cxTgt_mem_entry : Term.app (viewName "B") ([] ++ [cxB, cxFiat]) ∈ cxTgt.terms := by decide

set_option maxRecDepth 100000 in
/-- The `@UF` edge the `union` wrote, likewise. -/
theorem cxTgt_mem_uf : Term.app ufName ([cxB] ++ [cxA, cxFiat]) ∈ cxTgt.terms := by decide

set_option maxRecDepth 100000 in
theorem cxTgt_mem_B : cxB ∈ cxTgt.terms := by decide

set_option maxRecDepth 100000 in
/-- **And the index no longer holds it.** One `@BView` row survives the pass and its e-class
column is `(A)`: the two rows collided at the one (empty) key, `mergeOneOriented` kept the
smaller e-class — `mergeResult` is `ordering-min` — and dropped the other. -/
theorem cxTgt_rows_view : ∀ r ∈ cxTgt.rows, r.fn = viewName "B" →
    r = ⟨viewName "B", [], [cxA, cxTransFiat]⟩ := by decide

set_option maxRecDepth 100000 in
theorem cxTgt_mergeOf : cxTgt.sig.mergeOf (viewName "B") ≠ none := by decide

@[inherit_doc cxTgt_mem_entry]
theorem cxTgt_out_view : cxTgt.toDatabase.Out (viewName "B") [] [cxB, cxFiat] :=
  ⟨[], CongList.refl (by simp), by rw [FDatabase.toDatabase_terms]; exact cxTgt_mem_entry⟩

@[inherit_doc cxTgt_mem_uf]
theorem cxTgt_out_uf : cxTgt.toDatabase.Out ufName [cxB] [cxA, cxFiat] :=
  ⟨[cxB], CongList.refl (by
      intro a ha
      obtain rfl : a = cxB := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact cxTgt_mem_B),
    by rw [FDatabase.toDatabase_terms]; exact cxTgt_mem_uf⟩

set_option maxRecDepth 100000 in
/-- **`FDatabase.IndexCurrent` is false**, at a state built by the interpreter's own writers,
at the encoding's own declarations, over the collision a source `union` creates. This is why
`FDatabase.RoundClosed` closes none of the five residues by itself: it delivers a rule's
conclusion and the premise has to come from the index, which no longer records what
`Database.Out` still reads. -/
theorem cxTgt_not_indexCurrent : ¬ cxTgt.IndexCurrent := by
  intro h
  obtain ⟨r, hr, hfn, -, hout⟩ :=
    h (viewName "B") [] [cxB, cxFiat] cxTgt_mergeOf cxTgt_out_view
  rw [cxTgt_rows_view r hr hfn] at hout
  exact absurd hout (by decide)

/-! ##### What restores it, and what that costs

**The row the merge kept is not arbitrary.** It carries the `@UF` *parent* of the e-class
column the displaced row carried — `mergeBody` writes `@UF (ordering-max) ↦ (ordering-min, …)`
and `mergeResult` keeps `ordering-min`, so the survivor sits at the smaller class and the
larger one gets an edge to it. `cxTgt_rows_view` is the survivor here and `cxTgt_out_uf` is
the edge — written by the `union` and written again by `mergeBody`. So the repaired invariant
is *current up to the union-find*: for every merge-function entry term there is a row at a
congruent key whose e-class column is `@UF`-reachable from the entry's.

**That weakening does not close the residues as they stand.** `execM_eclassFollowed` is handed
an edge out of `t` and would be handed a row at some `u` further down the chain; the two do not
compose, and the entry its conclusion needs is one an *earlier* round wrote and only `terms`
remembers. The mechanism is therefore run-wide — each writing block's rows are current at the
`Cmd.saturate rebuildRuleset` that immediately follows it, and `terms` carries the result
forward past every later merge — and not a property of the final index. That is a stronger
induction than `ReadsSelfInv`, carrying a clause per *entry term* rather than per source term,
and it is what `builtRead_fire` needs at the round's pre-state as well.

**Restoring `IndexCurrent` outright is not a side condition worth having.** What it needs is
that the source assert no equation between distinct terms (`Database.Diag`), decidable on the
source text as "no `union` action and no `union` in any rule head" — a `union` between distinct
built terms is exactly what puts two e-classes at one view key. The in-domain census is 70 of
166 and the `union` cases are the ones the correspondence exists for: `Encoding/Match.lean`'s
`uProgram` and `witnessProgram` would both leave the domain, and with them the only witnesses
`execM_edges` and `execM_unionsJoined` are non-vacuous at. The clause is therefore not added,
and the census stays 70. -/

/-! #### The three residues, by clause -/

/-- **The residue of obligation `trans`. Not proved.**

What is missing: that the ids a source term reads to at an `execM` target are `@UF`-connected
and that the connection has a unique endpoint. Two entries at one view key collide, and
`mergeBody` writes the edge between their e-class columns; `rebuildRules`' e-class rule
follows an edge, so an id's `lead` is read by every term that reads the id;
`pathCompressRule` is what makes the endpoint unique. All three are *specification* rules
fired to saturation, and the hypothesis here is an `execM` target — so what it has to be
proved from is `FDatabase.runSaturateM`'s own fixpoint, and that is strictly weaker than
`RunSaturated` (`execM_contained`: the enumerator under-fires).

**That fixpoint is now proved and is not enough.** `FDatabase.RoundClosed` gives every term one
more rebuild round would derive, which is the *conclusion* of each of those three rules; their
*premise* is a row, and `cxTgt_not_indexCurrent` is the compiled statement that the index need
not hold every entry term `Database.Out` reads. What is left is the
run-wide index argument described at "What restores it, and what that costs", plus — for `lead`
being a *function* rather than a relation — `pathCompressRule`'s own fixpoint, which is a
second, independent use of it. -/
theorem execM_viewLeader {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewLeader := by
  sorry

/-- **`Database.ViewsCover.keyed`, at an `execM` target. Not proved**, and the one residue that
needs *both* halves of the missing mechanism.

The read-back gives the entry at the key the build itself wrote — the tuple where each child
reads to itself (`holdsBuild_of_execProgramM`). `keyed` asks for an entry at *every* tuple of
ids the children are given, which is the product `rebuildRules`' column rules cover, so what is
missing beyond the induction is `FDatabase.runSaturateM`'s own fixpoint — the same thing
`execM_viewLeader` and `execM_eclassFollowed` need.

That fixpoint is `FDatabase.RoundClosed`, proved, and it supplies the column rules'
conclusions; their premises are the view row and the `@UF` row, and those are what
`cxTgt_not_indexCurrent` says the index need not still hold. This residue needs the
command induction *and* that run-wide index argument, which is why it is the last of the five
to be reachable. -/
theorem execM_viewsCover_keyed {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ f as es, Term.app f as ∈ src.terms → ViewReprList tgt.toDatabase as es →
      ∃ e pf, tgt.toDatabase.Out (viewName f) es [e, pf] := by
  sorry

/-- **The residue of obligations `congr` and of `assert`'s reflexive half**, which is its one
clause. -/
theorem execM_viewsCover {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewsCover src :=
  ⟨execM_viewsCover_keyed hdom hsrc htgt⟩

/-- **`Database.UnionsJoined.readsSelf`, at an `execM` target. Proved from the command
induction**, whose one open case is `builtRead_fire`.

The `terms` clause of `ReadsSelfInv`, read off `readsSelfInv_execM`. A literal is free
(`ViewRepr.lit`); an application the source built is the read-back of its own block's two `set`s
(`viewReprAll_self_of_execProgramM`), located by the induction over `encode P`'s commands. -/
theorem execM_readsSelf {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ t ∈ src.terms, ViewRepr tgt.toDatabase t t :=
  (readsSelfInv_execM hdom hsrc htgt).terms

/-- **`Database.UnionsJoined.edges`, at an `execM` target. Proved from the same induction**, and
the reason the invariant carries both clauses at once: a source `union` records its equation at
the same command that records its two terms.

The `edges` clause of `ReadsSelfInv`. `out_uf_of_execProgramM` is the read-back at
`encodeAction`'s `union` shape — `.set @UF [ordering-max x₁ x₂] [ordering-min x₁ x₂, pf]`, whose
operands are the source expressions themselves (`encodeBuild_fst`) — threaded through the two
operands' builds, which precede it in the block; the disjunction is which endpoint
`ordering-max` picked, and `eval_ifGt` is that choice. -/
theorem execM_edges {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
      (∃ pf, tgt.toDatabase.Out ufName [a] [b, pf]) ∨
        (∃ pf, tgt.toDatabase.Out ufName [b] [a, pf]) :=
  (readsSelfInv_execM hdom hsrc htgt).edges

/-- **`Database.UnionsJoined.eclassFollowed`, at an `execM` target. Not proved**, and the one
clause of the three that is a *fixpoint* claim rather than a read-back of an emitted action.

`rebuildRules`' e-class rule re-`set`s a view entry at the `@UF` parent of its e-class column,
and what has to be shown is that `FDatabase.runSaturateM` ran it — which is the same thing
`execM_viewLeader` and `execM_viewsCover_keyed` need and is strictly weaker than `RunSaturated`
(`execM_contained`: the enumerator under-fires). The action read-back says nothing about it:
no `set` the encoder emitted writes this row.

**Exactly one step is missing, and it is named.** `FDatabase.RoundClosed` (proved, and located
at every encoded block's end by `roundClosed_of_execProgramM`) turns "the e-class rule fired at
this row pair" into the entry term this clause concludes with — `FDatabase.RoundClosed.fired`.
Its hypothesis is a *row* pair, and the two hypotheses here are `Database.Out` facts, which read
`terms`. `FDatabase.IndexCurrent` is the bridge and `cxTgt_not_indexCurrent` refutes it: the
row carrying `t` is deleted the moment a `union` collides it with a smaller class, while the
entry term stays. Weakened to "current up to the union-find" the bridge survives — the surviving
row sits at the `@UF` leader (`cxTgt_out_uf`) — but the weakening does not compose with this
clause's edge, which starts at `t` rather than at the leader. -/
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
  | .lit _, _, ha, .lit => ha
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

/-- **A literal is never in one class with an application**, at any target `ViewsSound` holds
of. This is the literal clause's soundness, and it is a property of the *source*: the join
would need a view row with a literal in its e-class column
(`SameClass.out_of_lit_app`), `ViewsSound` turns that row into `Cong src (.app f as) (.lit l)`,
and `Database.WF.litsIsolated` — which `evalAction`'s refusal of a `union` on a literal
establishes and `ProgramStep.wf` carries — says a literal is congruent to nothing but itself.

Every writer is covered at once, the rebuild rules included: they preserve `ViewsSound`
(`EntrySound.eclass`, `EntrySound.column`, `EntrySound.select`), which is all this needs. -/
theorem not_sameClass_lit_app {src d : Database} (hw : src.WF) (hs : d.ViewsSound src)
    {l : Lit} {f : FnName} {as : List Term} (ha : Term.app f as ∈ src.terms) :
    ¬ SameClass d (.lit l) (.app f as) := by
  intro h
  obtain ⟨es, pf, hl, ho⟩ := h.out_of_lit_app
  have hcong : Cong src (.app f as) (.lit l) :=
    cong_of_viewRepr hw hs (.app f as) ha (.app hl ho)
  exact absurd (Cong.eq_of_isLit hw.litsIsolated hcong (Or.inr rfl)) (by simp)

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

/-- **The literal clause's soundness, at a state a program reaches.** Every literal has an id
here — the state holds none of them, and the clause asks for nothing — and none of those ids is
`(A)`'s. Non-vacuous in both halves: `ViewRepr satTarget (.lit l) (.lit l)` holds and
`satSrc_mem` says `(A)` is a source e-node. -/
theorem satTarget_not_sameClass_lit_app (l : Lit) :
    ViewRepr satTarget (.lit l) (.lit l) ∧ ¬ SameClass satTarget (.lit l) (.app "A" []) :=
  ⟨.lit, not_sameClass_lit_app satSrc_wf satTarget_viewsSound satSrc_mem⟩

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
* `execM`'s rule firing is `FDatabase.runSaturateM`'s fixpoint — now proved, as
  `FDatabase.RoundClosed` (`Proofs/Merge.lean`), and located at every encoded block's end by
  `roundClosed_of_execProgramM`. It is strictly weaker than
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
equivalence live downstream in `DiffTest.lean`, so the clauses are discharged here
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
