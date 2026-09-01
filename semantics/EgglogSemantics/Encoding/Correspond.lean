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
  `sameClass_congr_of_shared`, `viewRepr_total`, `sameClass_self_of_viewsCover`) are proved
  outright. So the forward half is one lemma from done, and that lemma is "the state `execM`
  returned has the three properties". Each of the two clause-shaped properties is stated at
  exactly what its consumers spend — `ViewsCover.shared` at *one* shared id tuple and not the
  product (`ncTgt_not_viewsProduct` is the product refuted), `UnionsJoined` at the endpoints'
  *ids* and not at the endpoints (`ncTgt_not_readsSelf` is the difference), and the rebuild's
  edge-following in `ViewLeader.ufClosed` where both halves of it are needed at once.
  `Encoding/Match.lean`'s `uRebuilt_cong_sameClass` runs the whole argument at a state with a
  real `union`, with all three properties discharged there and no clause vacuous.
* **Proved, and it is where the weakened coverage clause pays**:
  `Database.ViewsCover.of_viewLeaderRows`. The tuple `ViewsCover.shared` answers with is the
  *leader* tuple, always — so the clause follows from two things and nothing else: an id for
  the source's own term, and a row at the leader tuple (`Database.ViewLeaderRows`' `rowLead`,
  the rebuild's **column** rules where `ViewLeader.ufClosed` is its e-class rule). No index
  argument beyond the one `ViewLeader` already needs, and the transport that puts a
  pointwise-congruent argument list on the same tuple is `viewReprList_map_lead_of_forall₂`,
  proved. `ncTgt_viewsCover` runs the reduction at the state that refutes
  `Database.ViewsProduct` — positive arity, the key `((B))` moved to `((A))` — which is what
  says the leader tuple generalises the instance `ncTgt_shared_FB` answers by hand.
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
* **Proved, and the shared crux of the command induction's five closed cases**: the
  **action read-back**.
  `holdsBuild_of_execActions` reads both rows a build's `set`s wrote off the block that ran
  them, `viewRepr_self_of_execActions` assembles them into the reading a `SameClass` is two
  of, and `holdsBuild_of_execProgramM`/`viewRepr_self_of_execProgramM` are the same where the
  block is the *top-level* `Cmd.action`s `encodeCmd` emits. `FDatabase.execProgramM_terms` is
  what carries the rows to the end of the run, and it is the only form the read-back can take:
  the row a rebuild displaced is gone, the entry term is not.
* **Proved, and what joins the read-back's blocks**: the **command induction**, and it is
  where the weakening pays. `UnionsInv` is the invariant it carries — `Database.UnionsJoined`
  at the state the *whole* run finishes at, every global binding's value reading to itself
  there, the two environments coinciding, and the source staying in the constructor fragment —
  every source term having an id there, every global binding's value reading to itself there,
  the two environments coinciding, and the source staying in the constructor fragment —
  and `unionsInv_step` carries it across a source command in five of its six cases: `.decl`,
  `.rule`, a top-level build (whose `joined` clause is trivial, `addTerm` writing only
  reflexive equations, and whose `reads` clause is the block's own read-back), a top-level
  `let` (whose `hvar` obligation the invariant supplies, `UnionsInv.hvar`) and a top-level
  `union` (whose edge `out_uf_of_execProgramM` reads back off the emitted `set`, between ids
  the same block's builds made). `unionsInv_execM` runs it from
  the empty source database and the state the prelude leaves, and `execM_unionsJoined` is its
  data clause. Three lemmas make it go through and each is worth naming:
  `Expr.eval_sigIndep` — two successful evaluations in one environment agree, whatever the two
  signatures — `encodeBuild_fst`, and `viewReprAll_self_of_execProgramM`, the read-back
  strengthened to every *subterm*, which is what `Database.addTerm` records. And it is not
  vacuous: `rbState2_unionsInv` is the invariant at a source state a program reaches
  (`rbProgram_programStep`) with a non-empty environment, `rbState2_unionsInv_hvar` is the
  `hvar` composition read off it, `unionsJoined_fire_satisfiable` is the residue's five
  hypotheses holding together, and `uRebuilt_unionsJoined` is the data clause at a source with
  a real equation.

  **The invariant this replaces was false.** It asked every source *term* to read to itself
  (`Database.ReadsSelf`, kept as the record) and every source equation to have a direct `@UF`
  edge between its two endpoints; both fail at `ncTgt`, so its rule-firing case was refuted
  rather than open. `Database.UnionsJoined.of_readsSelf` is the proof that what is carried now
  is weaker than what was carried then.
* **Proved, and the rebuild fixpoint the residues were waiting for**:
  `FDatabase.RoundClosed` (`Proofs/Merge.lean`). `runSaturateM` returns only from the branch
  that tested `sameData`, so a successful `Cmd.saturate R` leaves a state where **one more
  round of `R` derives no new term**; `roundClosed_of_execProgramM` locates one at the end of
  every block `encodeCmd` emits for a writing command. It is the only fixpoint available —
  `execM_contained` says the enumerator under-fires, so `RunSaturated`, and `Rebuilt` with it,
  is not a consequence — and it is a `terms` fact, because a round adds terms and *deletes*
  rows, so the sandwich that closes over the first does not close over the second.
* **Refuted, and it is why the fixpoint closes neither target-side residue**:
  `FDatabase.IndexCurrent`,
  the converse of `FDatabase.IndexOk.entry` — every entry term still current in the index.
  `cxTgt_not_indexCurrent` refutes it at a state built by the interpreter's own writers at the
  encoding's own declarations, where a source `union` collides two e-classes at one view key,
  `mergeOneOriented` deletes the displaced row, and `Database.Out` still reads its entry term.
  A rebuild rule's *conclusion* is a `terms` fact the fixpoint supplies; its *premise* is a
  `rows` fact only this would, so `IndexOk` needs a companion rather than a fourth field, and
  the companion is false. What survives is the same claim up to the union-find
  (`cxTgt_out_uf`), which does not compose with the clauses as stated.
* **Refuted, and it is what the fixpoint was being sought for**: `Database.ReadsSelf` and
  `Database.ViewsProduct`, the two over-strong clauses this file used to factor the forward half
  through. `ncTgt_not_readsSelf` and `ncTgt_not_viewsProduct` are a compiled source state a
  program reaches, paired with the state the encoded program runs to, at which both **fail**. A
  source rule fires once per *member* of a premise's congruence class (`ValidEnv` binds any held
  term, `Matches` reads up to congruence) while the encoded rule reads `d.rows`, and the rows sit
  at the union-find leader — so a source term a firing built over a non-leader member has no view
  entry carrying it in an e-class column. `encode_readsSelf_false` and
  `encode_viewsProduct_false` are the same two with the encoded run as a hypothesis, in
  `encode_corresponds_witness`'s discipline. What survives is `Database.UnionsRead`
  (`ncTgt_unionsRead`) and the correspondence at the pair the clauses fail on
  (`ncSrc_cong_FA_FB`, `ncTgt_sameClass_FA_FB`) — which is why `difftest correspond` still
  agrees on all seventy in-domain cases: the sweep measures the conclusion, and it was the
  *factorisation* that was false.

  **So the clauses are now stated at what their consumers spend**, each derived from the
  consumer and not guessed: `Database.ViewsCover.shared` at *one* id tuple shared by both
  argument lists, which is all `sameClass_congr_of_shared` reads and, at the diagonal, all
  `viewRepr_total` reads; `Database.UnionsJoined` at the endpoints' *ids* with the `@UF` edge
  between those, which is all `unionsRead_of_unionsJoined` reads once the edge-following is
  `Database.ViewLeader.ufClosed`. Both hold at the counterexample's own state —
  `ncTgt_shared_FB`, `ncTgt_unionsJoined` — and `Database.ViewsCover.of_viewsProduct` is the
  proof that the first really is weaker than what it replaced.
* **Measured, and now exact**: the kernel cannot run an encoded program because
  `Impl/Closure.lean`'s `closure` is well-founded-recursive, so `FDatabase.closureF` is
  *irreducible* and `patternHolds` gets stuck rather than slow. `unseal Egglog.closure` makes it
  reduce and one `FDatabase.mergeRound` on a sixteen-term state then runs past ten minutes,
  against 0.2 s compiled. Witnesses on the target side are therefore built from
  `FDatabase.addRow`/`addTerm` (the `cexD` idiom) or take the run as a hypothesis; witnesses on
  the *source* side run in the kernel outright (`ncSrc_exec`).
* **`sorry`**, three, and they are three *mechanisms* rather than three clauses — which is
  what the factorisation above bought. `execM_viewLeaderRows` is the whole of the run-wide
  **index** argument: `rebuildRules`' e-class rule in `ufClosed`, its column rules in
  `rowLead`, and `pathCompressRule` for `lead` being a function. `unionsJoined_fire` is the
  whole of a **target firing behind a source firing** — the one command case the read-back does
  not reach — and it now carries both of the command induction's data clauses, `joined` and
  `reads`, because a rule head builds as well as unions and one firing answers both.
  `execM_viewsSound` is the completeness half. `execM_viewLeader`, `execM_viewsCover`,
  `execM_viewsCover_shared`, `execM_unionsJoined` and `execM_unionsRead` are assembled from
  them, proved. `Encoding/Match.lean`'s `uRebuilt_unionsJoined`, `uRebuilt_viewLeaderRows` and
  `uRebuilt_viewsCover` are the properties at a state a program reaches, with
  `uRebuilt_cong_sameClass` running the forward half there; `uTgt_not_unionsRead` and
  `uTgt_not_viewLeader` are the conclusion and the responsible clause failing one rebuild
  firing earlier; `ncTgt_viewLeaderRows` is the fourth clause at positive arity, where the
  three earlier witnesses have only the empty key. `encode_assert`, `encode_trans`,
  `encode_congr`, `encode_corresponds_forward`, `encode_corresponds_complete` and
  `encode_corresponds` are assembled from them and carry `sorryAx` through them.
* **Refuted, and it was the *reading* that was wrong**: two of those clauses were once false
  at `litBuildProgram`, one `.action (.expr (.lit 5))`, whose build emits no action at all, and
  `Program.EncodeDomain.noBareBuild` was the repair. The defect was `ViewRepr`'s literal clause
  asking the target to hold the literal, where the encoding mints no e-node for one. The
  premise is gone and the domain clause with it;
  `litBuild_viewsCover`/`litBuild_unionsJoined`/`litBuild_forward` are the two once-false
  statements holding at that program, now in the domain (`litBuildProgram_encodeDomain`) and
  both vacuous in their clause, `uRebuilt`'s three being where they are not. What
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
reading that id also reads; two ids one source term reads have the same `lead`; and an id and
its `@UF` parent have the same `lead`.

Not `Database.Out`'s functionality, which is false — see the section header. `lead` is
egglog's union-find representative, but it is existentially quantified rather than computed:
`Database.Out` records every parent a merge displaced, so `UFLeader` is a relation.

**`ufClosed` is where the rebuild's edge-following lives**, and it is the whole of what
obligation `assert`'s `union` half spends on top of the `union`'s own write: an edge between
two ids gives them one `lead`, and `hmem` hands that `lead` to every term reading either end.
The clause it replaces asked a *source term* to read its own `@UF` parent — `ViewRepr d t t`
and an edge out of `t` — and that is unavailable, because a source term need not be an id of
itself at all (`ncTgt_not_readsSelf`). -/
def Database.ViewLeader (d : Database) : Prop :=
  ∃ lead : Term → Term,
    (∀ t e, ViewRepr d t e → ViewRepr d t (lead e)) ∧
    (∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → lead e₁ = lead e₂) ∧
    (∀ x y pf, d.Out ufName [x] [y, pf] → lead x = lead y)

/-- **Obligation `trans` reduces to `Database.ViewLeader`.** The two witnesses are both ids
of `b`, so they share a `lead`, and that `lead` is an id of `a` and of `c`. -/
theorem SameClass.trans_of_viewLeader {d : Database} (h : d.ViewLeader) {a b c : Term}
    (hab : SameClass d a b) (hbc : SameClass d b c) : SameClass d a c := by
  obtain ⟨lead, hmem, huniq, -⟩ := h
  obtain ⟨e₁, ha₁, hb₁⟩ := hab
  obtain ⟨e₂, hb₂, hc₂⟩ := hbc
  refine ⟨lead e₁, hmem a e₁ ha₁, ?_⟩
  rw [← huniq b e₂ e₁ hb₂ hb₁]
  exact hmem c e₂ hc₂

/-- **`Database.ViewLeader`, and the rows keyed at the leader tuple.**

The three clauses above, and a fourth: a view row's key transports along `lead`, so the tuple
of leaders carries a row wherever any tuple does. That fourth clause is the whole of what
`Database.ViewsCover` costs beyond *every source term having an id* —
`Database.ViewsCover.of_viewLeaderRows` is the reduction — and it is the same mechanism the
first three are, one step over: `rebuildRules`' **column** rules follow an `@UF` edge into a
*key* column exactly as its e-class rule follows one into a value column.

Kept apart from `Database.ViewLeader` rather than made a fourth field of it because
`cong_sameClass_of_state` spends only the three — the forward half's reading never looks at a
key — and because `satTarget_viewLeader` and `uTgt_not_viewLeader` are statements about those
three. `Database.ViewLeaderRows.toViewLeader` is the forgetting. -/
def Database.ViewLeaderRows (d : Database) : Prop :=
  ∃ lead : Term → Term,
    (∀ t e, ViewRepr d t e → ViewRepr d t (lead e)) ∧
    (∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → lead e₁ = lead e₂) ∧
    (∀ x y pf, d.Out ufName [x] [y, pf] → lead x = lead y) ∧
    (∀ f es e pf, d.Out (viewName f) es [e, pf] →
      ∃ e' pf', d.Out (viewName f) (es.map lead) [e', pf'])

/-- The three clauses `Database.ViewLeader` is, out of the four. -/
theorem Database.ViewLeaderRows.toViewLeader {d : Database} (h : d.ViewLeaderRows) :
    d.ViewLeader := by
  obtain ⟨lead, hmem, huniq, huf, -⟩ := h
  exact ⟨lead, hmem, huniq, huf⟩


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

/-- **`Database.ViewLeaderRows` holds at `satTarget`**, with the identity as its `lead`. The
literal case needs nothing of the state: a literal's only id is itself. `ufClosed` is vacuous
here and `satTarget_no_uf` is why — `satProgram` has no `union`, so nothing writes an edge —
and `rowLead` is the identity on keys for the same reason; `uRebuilt_viewLeaderRows` is the
property at a state that writes an edge and `ncTgt_viewLeaderRows` at one where `rowLead` moves
a key. -/
theorem satTarget_viewLeaderRows : satTarget.ViewLeaderRows :=
  ⟨id, fun _ _ h => h, fun t _ _ h₁ h₂ =>
    show id _ = id _ from match t with
      | .lit _ => (h₁.eq_of_lit).trans h₂.eq_of_lit.symm
      | .app _ _ => (satTarget_viewRepr h₁).trans (satTarget_viewRepr h₂).symm,
    fun _ _ _ ⟨_, _, hmem⟩ => absurd hmem (satTarget_no_uf _),
    fun _ _ e pf ho => ⟨e, pf, by simpa using ho⟩⟩

@[inherit_doc satTarget_viewLeaderRows]
theorem satTarget_viewLeader : satTarget.ViewLeader :=
  satTarget_viewLeaderRows.toViewLeader

/-- **The keys the target's views carry**, relative to what the source holds.

`shared` is exactly what obligation `congr` spends and no more: given an application the source
holds and any argument list the target already puts pointwise in one class with its own, *some*
id tuple both lists read to carries a view entry for `f`. **Which** tuple is existential, and
that existential is the whole of the weakening — the tuple is a leader tuple in practice, and
the tuple the build wrote is not available, since a rule firing over a non-leader class member
builds a term whose own children's ids no row is keyed at (`ncTgt_not_viewsProduct`).

`difftest correspond-dump 64 union` is the reading: for `witnessProgram` the `@AddView` keys are
`(One,One)`, `(One,Two)` and `(Two,One)` and every pointwise-equal pair of argument lists lands
on one of them.

**One clause, and it is about applications only.** A literal is its own id unconditionally
(`ViewRepr.lit`), so the target owes it nothing — which is why there is no `lits` clause here
and why a source action building a bare literal costs the domain nothing. -/
structure Database.ViewsCover (d src : Database) : Prop where
  /-- An application the source holds, and any argument list pointwise in one class with its
  own, read to one shared id tuple that a view entry for `f` is keyed at. -/
  shared : ∀ f as bs, Term.app f as ∈ src.terms → List.Forall₂ (SameClass d) as bs →
    ∃ es e pf, ViewReprList d as es ∧ ViewReprList d bs es ∧ d.Out (viewName f) es [e, pf]

/-- **The product form of that clause, which is what `Database.ViewsCover` used to state.
REFUTED** — `ncTgt_not_viewsProduct`, `encode_viewsProduct_false`.

An entry for `f` at *every* tuple of ids its children are given, not only at one. It is what
`rebuildRules`' column rules cover where they run — one `set` per column per `@UF` edge, so a
saturated ruleset covers the product — and it is more than an encoded run delivers: after a
`union` a non-leader member is still an id of itself while no row is keyed there. Kept as the
record of why the clause above reads *some* tuple, and paired with
`Database.ViewsCover.of_viewsProduct` so that the weakening is checked rather than asserted. -/
def Database.ViewsProduct (d src : Database) : Prop :=
  ∀ f as es, Term.app f as ∈ src.terms → ViewReprList d as es →
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

/-- **The product form implies the shared form**, and this is the proof that `ViewsCover` is a
weakening of `Database.ViewsProduct` rather than a different claim: `viewReprList_of_forall₂`
turns the pointwise hypothesis into one shared tuple and the product covers whatever tuple that
is. -/
theorem Database.ViewsCover.of_viewsProduct {src d : Database} (h : d.ViewsProduct src) :
    d.ViewsCover src where
  shared f as bs ha hl := by
    obtain ⟨es, h₁, h₂⟩ := viewReprList_of_forall₂ hl
    obtain ⟨e, pf, ho⟩ := h f as es ha h₁
    exact ⟨es, e, pf, h₁, h₂, ho⟩

/-- A reading transported to the leader tuple, pointwise. -/
theorem viewReprList_map_lead {d : Database} {lead : Term → Term}
    (hmem : ∀ t e, ViewRepr d t e → ViewRepr d t (lead e)) :
    ∀ {as es : List Term}, ViewReprList d as es → ViewReprList d as (es.map lead)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons (hmem _ _ h) (viewReprList_map_lead hmem hl)

/-- **A pointwise-congruent list reads the same leader tuple.** This is what makes the tuple
`Database.ViewsCover.shared` answers with independent of the list handed in: the two lists
share an id per position, `huniq` makes that id's `lead` the `lead` of the first list's own,
and `hmem` hands it to the second. Nothing here is about a row. -/
theorem viewReprList_map_lead_of_forall₂ {d : Database} {lead : Term → Term}
    (hmem : ∀ t e, ViewRepr d t e → ViewRepr d t (lead e))
    (huniq : ∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → lead e₁ = lead e₂)
    : ∀ {as bs : List Term}, List.Forall₂ (SameClass d) as bs →
      ∀ {es : List Term}, ViewReprList d as es → ViewReprList d bs (es.map lead)
  | [], [], .nil, [], .nil => .nil
  | a :: _, b :: _, .cons hab hl, e :: _, .cons ha hes => by
      obtain ⟨c, hac, hbc⟩ := hab
      refine .cons ?_ (viewReprList_map_lead_of_forall₂ hmem huniq hl hes)
      rw [huniq a e c ha hac]
      exact hmem b c hbc

/-- **The leader tuple answers the clause**, given an id for the source's own term: this is the
reduction that says `Database.ViewsCover` is `Database.ViewLeaderRows` plus *totality* and
nothing else.

The tuple handed in is never used. The source term's own reading supplies a tuple carrying a
row, `rowLead` moves that row to the leader tuple, and `viewReprList_map_lead_of_forall₂` puts
both argument lists on it — which is exactly the shape `ncTgt_shared_FB` exhibits by hand at
the instance where `Database.ViewsProduct` fails, and `ncTgt_viewsCover` is this reduction run
there. -/
theorem Database.ViewsCover.of_viewLeaderRows {src d : Database} (h : d.ViewLeaderRows)
    (ht : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) : d.ViewsCover src where
  shared f as bs ha hl := by
    obtain ⟨lead, hmem, huniq, -, hrow⟩ := h
    obtain ⟨e, he⟩ := ht _ ha
    match he with
    | @ViewRepr.app _ _ _ es _ pf hes ho =>
      obtain ⟨e', pf', ho'⟩ := hrow _ _ _ _ ho
      exact ⟨es.map lead, e', pf', viewReprList_map_lead hmem hes,
        viewReprList_map_lead_of_forall₂ hmem huniq hl hes, ho'⟩


/-- **Obligation `congr` reduces to `Database.ViewsCover.shared`.** The clause *is* that
obligation with the target's side spelled out — one shared id tuple and an entry keyed at it —
so the reduction is the entry's e-class column being an id of both applications. The second
self-congruence premise is not used. -/
theorem sameClass_congr_of_shared {src d : Database} (hc : d.ViewsCover src) {f : FnName}
    {as bs : List Term} (ha : Term.app f as ∈ src.terms)
    (hl : List.Forall₂ (SameClass d) as bs) :
    SameClass d (.app f as) (.app f bs) := by
  obtain ⟨es, e, pf, h₁, h₂, ho⟩ := hc.shared f as bs ha hl
  exact ⟨e, .app h₁ ho, .app h₂ ho⟩

/-- Every term of a list that has an id is in one class with itself: the pointwise premise
`Database.ViewsCover.shared` asks for, at the *diagonal*, off the ids a recursion found. -/
theorem sameClass_self_of_viewReprList {d : Database} : ∀ {as es : List Term},
    ViewReprList d as es → List.Forall₂ (SameClass d) as as
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons ⟨_, h, h⟩ (sameClass_self_of_viewReprList hl)

mutual

/-- **Every term the source holds has an id**, by `ViewsCover` and structural recursion:
`ViewRepr.lit` at a literal, and `shared` at its *diagonal* — which is the second thing the
clause is spent on and the reason it asks for no particular tuple. The recursion supplies the
children's ids, `sameClass_self_of_viewReprList` turns them into the pointwise premise, and the
tuple the clause answers with need not be the one handed in. `Database.WF` is what says the
children are held, and `ProgramStep.wf` delivers it from the empty state. -/
theorem viewRepr_total {d src : Database} (hc : d.ViewsCover src) (hw : src.WF) :
    ∀ t : Term, t ∈ src.terms → ∃ e, ViewRepr d t e
  | .lit l, _ => ⟨.lit l, .lit⟩
  | .app f as, ht => by
      obtain ⟨es, hes⟩ := viewRepr_list_total hc hw as fun a ha =>
        hw.subtermClosed _ ht (Term.arg_subterms ha (Term.self_mem_subterms a))
      obtain ⟨es', e, pf, h₁, -, ho⟩ :=
        hc.shared f as as ht (sameClass_self_of_viewReprList hes)
      exact ⟨e, .app h₁ ho⟩

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

/-- **`Database.UnionsRead`, at the one writer it has.**

`UnionsRead` is a statement about `SameClass`, which is two `ViewRepr`s at one id. This is the
`union`'s own write and nothing else: the two endpoints have ids, and the `@UF` edge runs
between *those*. What turns the edge into a shared id is `Database.ViewLeader.ufClosed`, so the
reduction (`unionsRead_of_unionsJoined`) takes both properties and uses nothing more.

**Stated at the endpoints' ids and not at the endpoints**, which is the whole of the weakening.
A source term need not be an id of itself — a rule fires once per class *member* and the
target's rows sit at the leader (`ncTgt_not_readsSelf`) — so neither `∀ t ∈ src.terms,
ViewRepr d t t` nor a *direct* edge between the two endpoints is available: a rule head's
`union` at a non-leader substitution writes its edge between the ids the target matched, which
are not the terms the source's own firing built.

Stated at *source* equations, so it quantifies over no stale view row a rebuild displaced —
`Database.Out` reads every row `terms` ever held (`MERGE.md`, "Constraint (3): monotonicity"),
and the fixpoint the interpreter reaches is a fixpoint over its *current* tables.

The disjunction is which endpoint `encodeAction`'s `@UF (ordering-max x₁ x₂) ↦
(ordering-min x₁ x₂, pf)` keyed the edge at, exactly as `cong_of_eqs` and `cong_headUnion`
take `ho`. -/
def Database.UnionsJoined (d src : Database) : Prop :=
  ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
    ∃ e₁ e₂ pf, ViewRepr d a e₁ ∧ ViewRepr d b e₂ ∧
      (d.Out ufName [e₁] [e₂, pf] ∨ d.Out ufName [e₂] [e₁, pf])

/-- **The clause `Database.UnionsJoined` used to carry first. REFUTED** —
`ncTgt_not_readsSelf`, `encode_readsSelf_false`.

Every source term is an id of itself: the entry its own build wrote, read with each child read
as itself. True of a term a *top-level* block built, and false of one a rule firing built over
a non-leader member of a congruence class, which the encoded rule never fires at. Kept as the
record of why both this clause and the direct-edge form of `UnionsJoined` are gone. -/
def Database.ReadsSelf (d src : Database) : Prop :=
  ∀ t ∈ src.terms, ViewRepr d t t

/-- **The two clauses that stood here imply the one that stands here now**, which is the check
that `Database.UnionsJoined` is a weakening rather than a different claim: with every source
term an id of itself, the ids it asks for are the endpoints themselves and the edge is the
direct one. Both premises fail at an `execM` target — `ncTgt_not_readsSelf`, and a head `union`
at a non-leader substitution for the second — while the conclusion does not
(`ncTgt_unionsJoined`). -/
theorem Database.UnionsJoined.of_readsSelf {src d : Database} (hr : d.ReadsSelf src)
    (he : ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
      (∃ pf, d.Out ufName [a] [b, pf]) ∨ (∃ pf, d.Out ufName [b] [a, pf])) :
    d.UnionsJoined src := by
  intro a b hab hne
  have ha : a ∈ src.terms := (eqsInTerms_free (Cong.assert hab)).1
  have hb : b ∈ src.terms := (eqsInTerms_free (Cong.assert hab)).2
  rcases he a b hab hne with ⟨pf, ho⟩ | ⟨pf, ho⟩
  · exact ⟨a, b, pf, hr a ha, hr b hb, Or.inl ho⟩
  · exact ⟨a, b, pf, hr a ha, hr b hb, Or.inr ho⟩

/-- **Obligation `assert`'s `union` half reduces to `Database.UnionsJoined` and
`Database.ViewLeader`.** The edge runs between an id of each endpoint, so `ufClosed` gives
those two ids one `lead` and `ViewLeader`'s first clause gives that `lead` to both endpoints —
which makes it the shared id.

No `Database.WF`, and in particular no `LitsIsolated`: the literal case is not excluded here
but discharged, since a literal is an id of itself (`ViewRepr.lit`) and the clause asks for an
id, never for the term. -/
theorem unionsRead_of_unionsJoined {src d : Database} (hlead : d.ViewLeader)
    (h : d.UnionsJoined src) : d.UnionsRead src := by
  intro a b hab hne
  obtain ⟨lead, hmem, -, huf⟩ := hlead
  obtain ⟨e₁, e₂, pf, h₁, h₂, ho⟩ := h a b hab hne
  refine ⟨lead e₁, hmem a e₁ h₁, ?_⟩
  rcases ho with ho | ho
  · rw [huf e₁ e₂ pf ho]; exact hmem b e₂ h₂
  · rw [← huf e₂ e₁ pf ho]; exact hmem b e₂ h₂

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
     fun _ _ _ ha _ hl => sameClass_congr_of_shared hcov ha hl⟩ h

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
  `ViewRepr d t t` — what a top-level build's own operand needs and what a `SameClass` is two
  of.
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
into `ViewRepr`, which is what a top-level `union`'s operands need and what a `SameClass`
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

/-! #### The three properties

Each is a property of the state `execM` returned rather than a restatement of an obligation,
and each holds at `witnessProgram`, the program the vacuity witness at the end of this file is
stated over; `difftest correspond-dump 64 union` prints the state and its `reprs`/`leaders`
block is the reading. Two of the three are *derived* below —
`Database.ViewsCover.of_viewLeaderRows` and `unionsRead_of_unionsJoined` — so what carries a
`sorry` is not three properties but two mechanisms.

* `Database.ViewLeader` — `leaders` is a single term for every source term: `(One)` for
  `(One)` and for `(Two)`, `(Add (One) (Two))` for both `Add`s. `difftest correspond`'s
  `leader-diff` column is the same reading over the whole corpus, and it is 0.
* `Database.ViewsCover` — every pointwise-equal pair of argument lists reads to one of the
  three `@AddView` keys, which are the product of the two children's `reprs`; the clause asks
  for one such key and not for the product, and the source holds no literal. It is *derived*
  from the first, strengthened by `rowLead` to `Database.ViewLeaderRows`, plus every source
  term having an id (`Database.ViewsCover.of_viewLeaderRows`).
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
case: `UnionsInv` is its invariant, `unionsInv_execM` runs it over `encode P`, and both of its
data clauses come out of it — `execM_unionsJoined`, `Database.UnionsRead`'s one write clause,
and the totality `Database.ViewsCover` is derived from. Both of the two things that make the
induction more than bookkeeping are handled there:

* a source term reached through a **variable** needs the earlier `let`'s own read-back, which is
  the `hvar` hypothesis of `viewRepr_self_of_execActions`; the invariant's `env` and `envReads`
  clauses together supply it (`UnionsInv.hvar`);
* an equation asserted by a **rule firing**'s head needs the source's firing to have a target
  firing behind it, which is the *opposite* direction from
  `exists_validQuerySubst_of_encodeQuery`. This is the case that does not close, and the reason
  is one step below the firing: `matchQuery` reads the *index* at a `.merge` function, and the
  read-back gives entry terms. `unionsJoined_fire` is it, alone.

What the induction no longer carries is every source *term* reading to itself
(`Database.ReadsSelf`), which is false at a firing over a non-leader class member and is what
made its predecessor unsound rather than incomplete.

**Two of these statements were once false**, at a program the domain admitted, and the state
that showed it is below — now with the sign reversed: `ViewRepr`'s literal clause carries no
membership premise, so the bare-literal build is in the domain and both statements hold there
(`litBuild_viewsCover`, `litBuild_unionsJoined`). -/

/-! #### The bare leaf, admitted

`.action (.expr (.lit 5))` writes nothing at all in the target — `encodeBuild` emits no action
for a leaf — and for that reason used to refute `Database.ViewsCover`'s since-deleted `lits`
clause and `Database.ReadsSelf`, which is what
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

/-- **`Database.ViewsCover` holds** — vacuously in `shared`, the only clause, since the source
holds no application. The literal is covered by the reading itself (`ViewRepr.lit`), which asks
the target for no e-node because the encoding writes none. `satTarget_viewsCover` is the clause
discharged against a row, and `ncTgt_shared_FB` is it at positive arity. -/
theorem litBuild_viewsCover {tgt : FDatabase} : tgt.toDatabase.ViewsCover litBuildSrc where
  shared := by
    intro f as bs hmem
    rw [litBuildSrc_terms] at hmem
    exact absurd hmem (by simp)

/-- **And so does `Database.UnionsJoined`**, vacuously: the source asserts no equation between
distinct terms. The bare leaf costs the union half nothing precisely because the clause is about
equations and not about terms — `uRebuilt_unionsJoined` is where it is not vacuous. -/
theorem litBuild_unionsJoined {tgt : FDatabase} :
    tgt.toDatabase.UnionsJoined litBuildSrc :=
  fun a b hab hne => absurd (litBuildSrc_diag (a, b) hab) hne

/-- **The forward half holds at the very program that refuted it**: the source asserts the
literal's reflexive equation and the target reads it back, with nothing in the target at
all. -/
theorem litBuild_forward {tgt : FDatabase} :
    Cong litBuildSrc (.lit (.int 5)) (.lit (.int 5)) ∧
      SameClass tgt.toDatabase (.lit (.int 5)) (.lit (.int 5)) :=
  ⟨litBuildSrc_mem, ⟨_, .lit, .lit⟩⟩

/-! #### The command induction

`Database.UnionsJoined` is a read-back of the `@UF` set the encoder emitted, and the read-back
above is stated at **one** block. What joins the blocks is an induction over `encode P`'s
commands, and what that induction has to carry is a little more than the clause itself: the
`union`'s two operands are *expressions*, and one reached through a variable needs the earlier
`let`'s own reading — the `hvar` hypothesis of `viewRepr_self_of_execActions` — so the readings
of the environment's values have to be carried alongside.

`UnionsInv` is that invariant. Its data clause is stated at the **final** state `D`, which is
what makes it composable: the rebuild overwrites rows and only the entry term survives
(`FDatabase.execProgramM_terms`), so "the block wrote it" is a fact about the state the whole run
finishes at, never about the state the next command starts from. Its other two clauses are
bookkeeping — the two environments coincide, so a source `let`'s value is the encoded `let`'s
value, and the source state stays in the constructor fragment, which is what makes every source
command's merge phase empty.

**What it deliberately does not carry** is every source term reading to itself
(`Database.ReadsSelf`). That is what the invariant used to be built on, and it is false at a
term a rule firing built over a non-leader class member — so the clause is now about equations
and ids, and the induction's build case, which used to spend the whole read-back on it, has
nothing left to prove.

Five of the six command cases close. The sixth — a command that **fires rules** — is
`unionsJoined_fire`, alone, with a docstring saying exactly what it needs and why the read-back
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

`Database.addTerm` records a reflexive equation per **subterm** of the term built, and a global
`let` binds a value whose every subterm a later build may read, so the reading is wanted at all
of them and not only at the term itself. `ViewRepr d t t` does not give that on its own — its
children read to *ids*, which need not be themselves — so the recursion has to deliver it, and it
does: an argument's subterms are covered by the argument's own build, a variable's by `hvar`, and
a literal's are itself. -/

mutual
/-- **Every subterm of a build's own term reads to itself.** `viewRepr_self_of_execActions` with
its conclusion and its `hvar` both closed under subterms, which is the form `UnionsInv.envReads`
consumes: a `let` binds the term, and a later build over the variable asks for the reading at
every subterm of it. -/
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

`joined` is the clause the induction is for — `Database.UnionsJoined` at the state `D` the
*whole* run finishes at, which is what makes it composable: the rebuild overwrites rows and only
the entry term survives, so "the block wrote it" is never a fact about the state the next
command starts from.

`envReads` is carried because a build over a **variable** needs the earlier `let`'s own
read-back (the `hvar` hypothesis of `viewReprAll_self_of_execProgramM`), and a global binding's
value is a term a top-level block built — so it *is* an id of itself, which a term a rule
firing built need not be. That restriction to the environment is what this clause has that its
predecessor, `∀ t ∈ sd.terms, ViewRepr D t t` (`Database.ReadsSelf`), did not: the predecessor
is false (`ncTgt_not_readsSelf`) and this is not asked about a fired term at all.

The last two are bookkeeping. `env` is what makes a source `let`'s value the encoded `let`'s
value — `encodeBuild`'s naming expression *is* the source expression (`encodeBuild_fst`), and
`Expr.eval_sigIndep` needs nothing of the two signatures. `state` is what makes every source
command's merge phase empty. -/
structure UnionsInv (sd : Database) (td D : FDatabase) : Prop where
  /-- Every equation the source asserts between distinct terms has ids for both endpoints and
  a `@UF` edge between those, at the state the run finishes at. -/
  joined : D.toDatabase.UnionsJoined sd
  /-- Every term the source holds has *some* id there. Not the term itself
  (`Database.ReadsSelf`, refuted by `ncTgt_not_readsSelf`) — a term a rule firing built over a
  non-leader class member is an id of nothing, and reads the leader's row instead. -/
  reads : ∀ t ∈ sd.terms, ∃ e, ViewRepr D.toDatabase t e
  /-- Every subterm of a value the source's environment binds reads to itself there. -/
  envReads : ∀ b ∈ sd.env, ∀ s ∈ b.2.subterms, ViewRepr D.toDatabase s s
  /-- The two environments are the same list. -/
  env : td.env = sd.env
  /-- The source is still in the constructor fragment. -/
  state : sd.CtorState

/-- **The `hvar` obligation, out of the invariant.** A build over a variable asks for the
reading of every subterm of the variable's value, which is `envReads` at the binding
`Env.lookup` found. This is the shape `rbState2_viewRepr_W` exhibits at one command; here it is
at every command. -/
theorem UnionsInv.hvar {sd : Database} {td D : FDatabase} (h : UnionsInv sd td D)
    {w : Var} {u : Term} (hu : Env.lookup w td.env = some u) :
    ∀ s ∈ u.subterms, ViewRepr D.toDatabase s s := by
  intro s hs
  rw [h.env] at hu
  exact h.envReads (w, u) (Env.mem_of_lookup hu) s hs

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
`Cmd.saturate` is not one: the equations it adds are the ones a **source rule firing**'s head
`union` asserted, and to read one back the encoded rule has to have fired — at a substitution
whose ids are ids of the terms the source's own firing built.

**What this may not ask for, and what refutes the stronger form.** What it used to conclude was
the pair `Database.UnionsJoined.of_readsSelf` takes: every source term reading to *itself*
(`Database.ReadsSelf`), and a direct `@UF` edge between the two endpoints of every source
equation. Both are false at the state an encoded run reaches
(`ncTgt_not_readsSelf`, `Database.ReadsSelf`), and for one reason: a source rule fires once per
*member* of a premise's congruence class — `Spec/Match.lean`'s `ValidEnv` binds a variable to
any term the source holds and `Matches` reads the instance up to congruence — while the encoded
rule reads `d.rows` at a `.merge` function (`patternHolds`) and the target holds one row per
recorded key. The rows sit at the union-find *leader*, because `mergeResult` keeps
`ordering-min` and `@UF`'s edges run max-to-min, so a source term built over a non-leader member
is a term no view entry carries in its e-class column, and a head `union` over such a member is
a source equation with no target edge between those two terms.

`Database.UnionsJoined` asks for neither: an id for each endpoint, and the edge between the
*ids*. At the very state the counterexample is built from that holds — `ncTgt_unionsJoined` —
so this is a hole and not a falsity. What has to fill it is a target firing behind the source's,
which is `Encoding/Match.lean`'s correspondence in the direction
`exists_validQuerySubst_of_encodeQuery` does not run.

**Both data clauses at once, and for the same reason.** `reads` — every source term having
*some* id — is the other half of the conclusion, and its five other command cases are the
build read-back (`viewReprAll_self_of_execProgramM`), discharged in `unionsInv_step`. A rule
head **builds** as well as unions, and the term it builds at a non-leader substitution is a
term no block ran a `set` for; the id it has is the leader's row, and the leader's row is the
target's own firing. One firing answers both clauses, which is why they are one residue rather
than two: `Database.ViewsCover` is now `Database.ViewLeaderRows` plus `reads`
(`Database.ViewsCover.of_viewLeaderRows`), so this residue and `execM_viewLeaderRows` between
them are the whole forward half.

**What it was blamed on before, and what that turned out to be.** `FDatabase.IndexCurrent`
(`Proofs/Merge.lean`, refuted by `cxTgt_not_indexCurrent`) and the run-wide index argument that
would replace it are about the row a *rebuild* displaced. They are real, and they are not this:
here the row was never written, at any state, by any block. That argument is
`execM_viewLeaderRows`'s, and this residue does not share it — a target firing is a `rows`
fact about the state the encoded rule ran at, not about a row the rebuild moved.

Stated over both firing commands at once, because `encodeCmd` gives them the same block:
`[c, Cmd.saturate rebuildRuleset]`. -/
theorem unionsJoined_fire {R : RulesetName} {c : Cmd} {sd sd' : Database} {td td' D : FDatabase}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hrun : td.execProgramM [c, Cmd.saturate rebuildRuleset] = some td')
    (hmono : ∀ t ∈ td'.terms, t ∈ D.terms) (hinv : UnionsInv sd td D) :
    D.toDatabase.UnionsJoined sd' ∧ ∀ t ∈ sd'.terms, ∃ e, ViewRepr D.toDatabase t e := by
  sorry

/-! ##### One command -/

/-- **The invariant survives one source command.** Six cases: five read-backs of the `set`s
`encodeCmd` emitted for that command — `reads` off the build's own reading, `joined` off the
`union`'s own `@UF` write — and `unionsJoined_fire`, which is both data clauses at once. -/
theorem unionsInv_step {Q : Program} (hQ : Q.EncodeDomain) {c : Cmd} (hc : c ∈ Q)
    {n i : Nat} {sd sd' : Database} {td D : FDatabase} {rest : Program}
    (hstep : CmdStep sd c sd')
    (hrun : td.execProgramM ((encodeCmd c n i).1 ++ rest) = some D)
    (hinv : UnionsInv sd td D) :
    ∃ td', td.execProgramM (encodeCmd c n i).1 = some td' ∧ UnionsInv sd' td' D := by
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
      have hterms : sd'.terms = sd.terms := Database.terms_eq_of_eqs_eq heqs
      refine ⟨fun a b hab hne => hinv.joined a b (hsub hab) hne,
        fun t ht => hinv.reads t (by rw [hterms] at ht; exact ht), ?_, ?_, hstate'⟩
      · rw [henv]; exact hinv.envReads
      · rw [hinv.env, henv]
  | rule r =>
      obtain ⟨heqs, henv⟩ := cmdStep_rule_fields hinv.state.sig hstep
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.rule r) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.rule (encodeRule i r n).1] := hc'
        obtain rfl : c' = Cmd.rule (encodeRule i r n).1 := by simpa using hc2
        trivial
      have hsub : sd'.eqs ⊆ sd.eqs := fun p hp => by rw [heqs] at hp; exact hp
      have hterms : sd'.terms = sd.terms := Database.terms_eq_of_eqs_eq heqs
      refine ⟨fun a b hab hne => hinv.joined a b (hsub hab) hne,
        fun t ht => hinv.reads t (by rw [hterms] at ht; exact ht), ?_, ?_, hstate'⟩
      · rw [henv]; exact hinv.envReads
      · rw [FDatabase.execProgramM_env hsets hblock, hinv.env, henv]
  | run R =>
      have hjoin := unionsJoined_fire (Or.inl rfl) hstep hblock hmono hinv
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.run R) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.run R, Cmd.saturate rebuildRuleset] := hc'
        have hd : c' = Cmd.run R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using hc2
        rcases hd with rfl | rfl <;> trivial
      refine ⟨hjoin.1, hjoin.2, ?_, ?_, hstate'⟩
      · rw [cmdStep_env_of_run hstep]; exact hinv.envReads
      · rw [FDatabase.execProgramM_env hsets hblock, hinv.env, cmdStep_env_of_run hstep]
  | saturate R =>
      have hjoin := unionsJoined_fire (Or.inr rfl) hstep hblock hmono hinv
      have hsets : ∀ c' ∈ (encodeCmd (Cmd.saturate R) n i).1, c'.ActionsAreSets := by
        intro c' hc'
        have hc2 : c' ∈ [Cmd.saturate R, Cmd.saturate rebuildRuleset] := hc'
        have hd : c' = Cmd.saturate R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using hc2
        rcases hd with rfl | rfl <;> trivial
      refine ⟨hjoin.1, hjoin.2, ?_, ?_, hstate'⟩
      · rw [cmdStep_env_of_saturate hstep]; exact hinv.envReads
      · rw [FDatabase.execProgramM_env hsets hblock, hinv.env, cmdStep_env_of_saturate hstep]
  | action a =>
      have hev : evalAction sd a = some sd' := cmdStep_action_eq hinv.state.sig hstep
      rcases evalAction_eq_some hev with
        ⟨e, tS, rfl, htS, rfl⟩ | ⟨v, e, tS, rfl, htS, rfl⟩ |
        ⟨e₁, e₂, t₁, t₂, rfl, ht₁, ht₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, -, -, -⟩
      · -- a top-level build: `addTerm` writes only reflexive equations, so `joined` is
        -- untouched — which is the weakened clause's first dividend — and `reads` is the
        -- block's own read-back, at every subterm `addTerm` recorded.
        have hprim : ∀ g ∈ e.fns, Prim.ofName g = none :=
          noPrim_of_mem_ctors hQ (fun p hp => mem_program_ctors hc hp)
        have hsets : ∀ c' ∈ (encodeCmd (Cmd.action (Action.expr e)) n i).1,
            c'.ActionsAreSets := by
          change ∀ c' ∈ (encodeBuild e n).2.1.map Cmd.action
            ++ [Cmd.saturate rebuildRuleset], c'.ActionsAreSets
          exact actionsAreSets_block (encodeBuild_isSet e n)
        have hblk : (encodeCmd (Cmd.action (Action.expr e)) n i).1
            = (encodeBuild e n).2.1.map Cmd.action ++ [Cmd.saturate rebuildRuleset] := rfl
        have hrun' : td.execProgramM ((encodeBuild e n).2.1.map Cmd.action
            ++ ([Cmd.saturate rebuildRuleset] ++ rest)) = some D := by
          rw [← List.append_assoc, ← hblk]; exact hrun
        have htS2 : e.eval sd.sig td.env = some tS := by rw [hinv.env]; exact htS
        obtain ⟨tT, htT⟩ := exists_eval_of_execProgramM_encodeBuild e n hrun'
          (fun w hw => Expr.exists_lookup_of_eval e htS2 w hw)
        have htT2 : e.eval td.sig td.env = some tS := by
          rw [htT, Expr.eval_sigIndep e htT htS2]
        have hall : ∀ s ∈ tS.subterms, ViewRepr D.toDatabase s s :=
          viewReprAll_self_of_execProgramM e n hrun' hprim (fun w _ u hu => hinv.hvar hu) htT2
        refine ⟨?_, ?_, ?_, ?_, hstate'⟩
        · intro x y hxy hne
          rcases eq_of_mem_addTerm_eqs hxy with hxy' | hxy'
          · exact hinv.joined x y hxy' hne
          · exact absurd hxy' hne
        · intro t ht
          rcases Database.addTerm_terms ▸ ht with ht' | ht'
          · exact hinv.reads t ht'
          · exact ⟨t, hall t ht'⟩
        · exact hinv.envReads
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
        refine ⟨?_, ?_, ?_, ?_, hstate'⟩
        · intro x y hxy hne
          rcases eq_of_mem_addTerm_eqs (hxy : (x, y) ∈ (sd.addTerm tS).eqs) with hxy' | hxy'
          · exact hinv.joined x y hxy' hne
          · exact absurd hxy' hne
        · intro t ht
          rcases Database.addTerm_terms ▸ Database.terms_setEnv ▸ ht with ht' | ht'
          · exact hinv.reads t ht'
          · exact ⟨t, hall t ht'⟩
        · intro b hb s hs
          have hb2 : b ∈ (v, tS) :: sd.env := hb
          rcases List.mem_cons.mp hb2 with rfl | hb'
          · exact hall s hs
          · exact hinv.envReads b hb' s hs
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
        refine ⟨?_, ?_, ?_, ?_, hstate'⟩
        · intro x y hxy hne
          rcases mem_addEq_eqs hxy with hxy' | hxy' | hxy'
          · obtain ⟨rfl, rfl⟩ : x = t₁ ∧ y = t₂ := by
              have := hxy'
              simp only [Prod.mk.injEq] at this
              exact this
            refine ⟨x, y, ?_⟩
            rcases hedge with ⟨pf, ho⟩ | ⟨pf, ho⟩
            · exact ⟨pf, hall₁ x (Term.self_mem_subterms _),
                hall₂ y (Term.self_mem_subterms _), Or.inl ho⟩
            · exact ⟨pf, hall₁ x (Term.self_mem_subterms _),
                hall₂ y (Term.self_mem_subterms _), Or.inr ho⟩
          · exact hinv.joined x y hxy' hne
          · exact absurd hxy' hne
        · intro t ht
          rcases Database.addEq_terms ▸ ht with ht' | ht'
          · rcases ht' with ht'' | ht''
            · exact hinv.reads t ht''
            · exact ⟨t, hall₁ t ht''⟩
          · exact ⟨t, hall₂ t ht'⟩
        · exact hinv.envReads
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

/-- **The command induction.** One `unionsInv_step` per source command, threading the state
the encoded block left. -/
theorem unionsInv_of_programStep {Q : Program} (hQ : Q.EncodeDomain) :
    ∀ (p : Program) {n i : Nat} {sd sd' : Database} {td D : FDatabase} {rest : Program},
      (∀ c ∈ p, c ∈ Q) → ProgramStep sd p sd' →
      td.execProgramM ((encodeCmds p n i).1 ++ rest) = some D →
      UnionsInv sd td D →
      ∃ td', td.execProgramM (encodeCmds p n i).1 = some td' ∧ UnionsInv sd' td' D := by
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
      unionsInv_step hQ (hsub c List.mem_cons_self) hstep hrun hinv
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

/-- **The invariant at the state `execM` returned**, which is what `execM_unionsJoined` states.
Both `td` and `D` are the final state: the induction started at the empty source database and
the state the prelude left, and finished where the run did. -/
theorem unionsInv_execM {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : UnionsInv src tgt tgt := by
  rw [execM, encode] at htgt
  obtain ⟨td₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have henv₀ : td₀.env = [] := by
    rw [FDatabase.execProgramM_env (actionsAreSets_encodePrelude P) hprel]
    rfl
  have hinv₀ : UnionsInv Database.empty td₀ tgt := by
    refine ⟨?_, ?_, ?_, ?_, Database.CtorState.empty⟩
    · intro a b hab
      exact absurd hab (by simp [Database.empty])
    · intro t ht
      exact absurd ht (by simp)
    · intro b hb
      exact absurd hb (by simp [Database.empty])
    · rw [henv₀]
      rfl
  obtain ⟨td', hb, hinv⟩ := unionsInv_of_programStep hdom P (fun c hc => hc) hsrc
    (by rw [List.append_nil]; exact hcmds) hinv₀
  obtain rfl : td' = tgt := Option.some.inj (hb.symm.trans hcmds)
  exact hinv

/-! ##### The invariant is not vacuous

`ENCODING.md`'s discipline: an invariant nothing satisfies carries an induction that proves
nothing. Here it is at a **source state a program reaches** and the target state the read-back
above computed, with the `terms` clause non-vacuous at positive arity and the environment
non-empty — which is what makes `UnionsInv.hvar` do work rather than hold trivially. The
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

/-- The source asserts nothing but reflexive equations, so the `joined` clause is vacuous here —
`uProgram`, whose rule head unions two distinct terms, is where it is not
(`uRebuilt_unionsJoined`). -/
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

/-- **`UnionsInv` holds, with the clause that does work doing it.** `envReads` is asked at the
one binding a top-level `let` made, and answered by the *earlier* build's own reading — which is
the composition the `let` case of `unionsInv_step` performs, and the only thing the induction
still carries about terms. `joined` is vacuous here (`rbSrc_diag`); `uRebuilt_unionsJoined` is
that clause at a source with a real equation. -/
theorem rbState2_unionsInv : UnionsInv rbSrc rbState2 rbState2 where
  joined := fun a b hab hne => absurd (rbSrc_diag (a, b) hab) hne
  reads := by
    intro t ht
    rw [rbSrc_terms] at ht
    have ht' : t = Term.app "A" [] ∨ t = Term.app "W" [Term.app "A" []] := by
      rcases ht with h | h
      · exact Or.inl (by simpa using h)
      · simpa [or_comm] using h
    rcases ht' with rfl | rfl
    · exact ⟨_, rbState2_viewRepr_A⟩
    · exact ⟨_, rbState2_viewRepr_W⟩
  envReads := by
    intro b hb s hs
    have hb2 : b ∈ rbEnv := hb
    obtain rfl : b = ("x", Term.app "A" []) := by simpa [rbEnv] using hb2
    obtain rfl : s = Term.app "A" [] := by simpa using hs
    exact rbState2_viewRepr_A
  env := rfl
  state := rbSrc_ctorState

/-- **And `UnionsInv.hvar` is discharged non-vacuously at the variable the `let` bound.**
This is `rbState2_viewRepr_W`'s `hvar` argument, now read off the invariant rather than supplied
by hand — which is exactly what `unionsInv_step` does once per command. -/
theorem rbState2_unionsInv_hvar :
    ∀ s ∈ (Term.app "A" []).subterms, ViewRepr rbState2.toDatabase s s :=
  rbState2_unionsInv.hvar (w := "x") rfl

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

/-- **`unionsJoined_fire`'s hypotheses are simultaneously satisfiable**, so the residue is not
vacuous — `ENCODING.md`'s failure, twice.

Satisfiable degenerately, and deliberately so: the source holds no rule, so the round adds
nothing and the encoded round writes nothing either, while the fifth hypothesis is the invariant
above. The case with content is a round that fires a head `union` — or, for the `reads` half of
the conclusion, one that fires a head **build** — and that is where it is open.
`difftest correspond`'s **LOST** column — `Cong src a b` without `SameClass tgt a b`, swept with
the diagonal included over the 70 in-domain cases, rules and runs among them — is 0 and stays 0,
which is the `reads` clause measured: every source term has *some* id in the target. Asking for
that id to be the term itself is the stronger claim the counterexample refutes
(`Database.ReadsSelf`, `ncTgt_not_readsSelf`), and this clause does not ask it. -/
theorem unionsJoined_fire_satisfiable :
    CmdStep rbSrc (.run rbRuleset) rbSrc ∧
      rbState2.execProgramM [Cmd.run rbRuleset, Cmd.saturate rebuildRuleset] = some rbState2 ∧
      (∀ t ∈ rbState2.terms, t ∈ rbState2.terms) ∧ UnionsInv rbSrc rbState2 rbState2 :=
  ⟨rbSrc_cmdStep_run rbRuleset, rbState2_execProgramM_run, fun _ h => h, rbState2_unionsInv⟩

/-! #### The rebuild fixpoint, and the row it does not reach

The target-side residue wants one mechanism, and it is a postcondition of `FDatabase.runSaturateM
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

/-- **The fixpoint at a state a program reaches.** Degenerately, as
`unionsJoined_fire_satisfiable` is: `rbState2` holds no rule, so the round it is a fixpoint of
fires nothing. The non-degenerate reading is measured rather than compiled — every one of
`difftest correspond`'s 70 in-domain cases ends at a `Cmd.saturate rebuildRuleset`. -/
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
`encode` of the source program through the *kernel* instead is not available, and that is
measured rather than assumed: `matchQuery`'s own definition computes one congruence closure
per candidate substitution — the `csimp` fast paths are compiled code, which the elaborator
does not use — and `execM (encode …) = some _` on the two-constructor, one-`union` source did
not reduce to a value in 29 minutes at eight million heartbeats. `difftest correspond`'s
`unionCase` is that program measured rather than compiled. -/

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
`FDatabase.RoundClosed` closes neither residue by itself: it delivers a rule's
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

**That weakening does not close the residues as they stand.** `Database.ViewLeader.ufClosed`
is handed an edge out of an id and would be handed a row at some `u` further down the chain;
the two do not compose, and the entry its conclusion needs is one an *earlier* round wrote and
only `terms` remembers. The mechanism is therefore run-wide — each writing block's rows are
current at the `Cmd.saturate rebuildRuleset` that immediately follows it, and `terms` carries the
result forward past every later merge — and not a property of the final index.

**And it would not close `unionsJoined_fire`, because nothing about currency would.** The next
section is the counterexample the induction's old invariant died on: the row a firing needs was
never written at any state, so no statement about which rows are *current* reaches it. The
run-wide argument is what `execM_viewLeaderRows` still wants — its `rowLead` clause as much as
its `ufClosed` one, since `Database.ViewsCover` is now derived from those
(`Database.ViewsCover.of_viewLeaderRows`) — and it is not what the command induction wants.

**Restoring `IndexCurrent` outright is not a side condition worth having.** What it needs is
that the source assert no equation between distinct terms (`Database.Diag`), decidable on the
source text as "no `union` action and no `union` in any rule head" — a `union` between distinct
built terms is exactly what puts two e-classes at one view key. The in-domain census is 70 of
166 and the `union` cases are the ones the correspondence exists for: `Encoding/Match.lean`'s
`uProgram` and `witnessProgram` would both leave the domain, and with them the only witnesses
`execM_unionsJoined` and `Database.ViewLeader.ufClosed` are non-vacuous at. The clause is
therefore not added, and the census stays 70. -/

/-! #### The two clauses the fixpoint was for, refuted — and what replaced them

`FDatabase.RoundClosed` is not the missing step, because for these two there was no missing
step: `Database.ReadsSelf` — every source term reads to **itself** — and
`Database.ViewsProduct` — a view entry at every id tuple the children form — are both *false* at
the state an encoded program runs to. The command induction used to be built on the first of
them, which made it unsound rather than incomplete; it is now built on
`Database.UnionsJoined`, which holds here (`ncTgt_unionsJoined`).

**The mechanism, in one sentence.** A rule head builds over the ids the *target* matched, and
those are the keys the target's rows carry, while the source's own substitution ranges over
the whole congruence class. `Spec/Match.lean`'s `ValidEnv` binds a variable to any term the
source holds and `Matches` reads the instance up to congruence, so a source rule fires once
per class *member*; `matchQuery` reads `d.rows` at a `.merge` function and the target holds
one row per recorded key. Where a class's rows sit at the smaller e-class — which is where
`mergeResult`'s `ordering-min` and `@UF`'s max-to-min edges put them — the target fires at
the leader alone, and the term the source built over a non-leader member is a term no view
entry carries in its e-class column.

**The program.** `(F (A))`, `(B)`, `(union (A) (B))`, and `(rule ((F ?x)) ((F ?x)))` run
once. `(A)` is below `(B)` in `Term.blt`, so the `union` writes `@UF((B)) ↦ ((A), @Fiat)` and
`(A)` is the leader; `@FView` is keyed at `((A))` and nothing re-keys it, since the rebuild's
column rule needs an edge *out of* `(A)`. The source rule fires at `x := (A)` and at
`x := (B)` — `(F (B))` is congruent to the held `(F (A))`, and `Cong.congr`'s two
self-congruence premises are met because `Matches` adds the instance — and builds `(F (B))`.
The encoded rule fires at `x := (A)` alone and re-`set`s the row it already holds, so the
encoded run's final state is the state before it and `(F (B))` is in no e-class column.

**Both halves are compiled.** The source side runs in the *kernel*: `ncSrc_exec` is `exec
ncProgram` evaluated, `ncProgram_programStep` lifts it through `exec_programStep`, and
`ncSrc_mem_FB` is `(F (B))` at a state a program reaches. The target side is written with
`FDatabase.addRow` and `FDatabase.addTerm` — the writers `execAction` and the merge phase run
— because the kernel cannot run the encoded program, and that limit is now exact rather than a
timeout: `Impl/Closure.lean`'s `closure` is well-founded-recursive, so `closureF` is
irreducible and `patternHolds` gets **stuck** rather than slow. `unseal Egglog.closure` makes
it reduce, and then one `FDatabase.mergeRound` on this sixteen-term state runs past ten
minutes against 0.2 s compiled. `ncTgt` is the encoded run's final state row for row and term
for term; `encode_readsSelf_false` and `encode_viewsProduct_false` are the same two refutations
with that run as a *hypothesis*, in `encode_corresponds_witness`'s discipline, so nothing
rests on the transcription.

**What survives, and it is why the corpus agrees.** `Database.UnionsRead` — the property
`cong_sameClass_of_state` actually consumes — holds here (`ncTgt_unionsRead`), and so does the
correspondence at the very pair the two clauses fail on: `Cong src (F (A)) (F (B))` and
`SameClass tgt (F (A)) (F (B))`, both compiled. `(F (B))` has an id; it is `(F (A))` and not
itself. So `difftest correspond` stays 70 agreeing with 0 LOST — the sweep measures the
conclusion, and it is the *factorisation* that is false.

**What that cost the residues, and what they say now.** The weakenings are read off the
consumers rather than guessed at. `sameClass_congr_of_shared` uses the coverage clause only at
an id tuple *shared* by both argument lists and `viewRepr_total` only at the diagonal, so
`Database.ViewsCover.shared` asks for one such tuple and `Database.ViewsProduct` is what it
replaced (`Database.ViewsCover.of_viewsProduct` is the implication, so the weakening is checked).
`unionsRead_of_unionsJoined` uses the `union` clause only at the endpoints of a source
*equation*, and only through their *ids* — not through the endpoints themselves, which is why
`Database.UnionsJoined` reads ids: a rule head's `union` at a non-leader substitution is a source
equation with no target edge between those two terms either, so the direct-edge form fails for
the same reason `readsSelf` does. The edge-following that is left is
`Database.ViewLeader.ufClosed`, which is one residue instead of two.

`ncTgt_shared_FB` and `ncTgt_unionsJoined` are the two weakened clauses holding at this state,
at the very instances the strong ones fail on — and `ncTgt_viewsCover` is the first of them
holding *derivably*, out of `ncTgt_viewLeaderRows` and `ncTgt_viewRepr_total` rather than by
hand, which is what says the leader tuple answers every instance and not just this one. -/

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

/-- **A view is never the union-find table**, whatever the constructor: the two names differ
in their last character. The `@UF` row is as wide as a nullary view entry plus a column, so
nothing about lengths excludes it. -/
theorem viewName_ne_ufName {f : FnName} : viewName f ≠ ufName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, ufName, String.toList_append, List.reverse_append] at h2

/-- **A view is never a proof head**, by the same last character. -/
theorem viewName_ne_transName {f : FnName} : viewName f ≠ transName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, transName, String.toList_append, List.reverse_append] at h2

/-- The source rule: it fires once per member of `?x`'s class and builds `F` over each. Its
head is the premise, so the target's own firing writes a row it already holds and the encoded
run adds nothing at all — the smallest shape in which the source outruns it. -/
def ncRule : Rule where
  query := [.expr (.app "F" [.var "x"])]
  actions := [.expr (.app "F" [.var "x"])]
  ruleset := "r"

/-- Two nullary constructors and one unary, a build over the *smaller* of the two, a `union`
that puts the larger in its class, and one round. -/
def ncProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "B" { arity := 0, outArity := 1, merge := none },
   .decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "A" []])),
   .action (.expr (.app "B" [])),
   .action (.union (.app "A" []) (.app "B" [])),
   .rule ncRule,
   .run "r"]

/-- `(A)`, the leader: `Term.blt` puts it below `(B)`, so `ordering-min` keeps it. -/
def ncA : Term := .app "A" []

/-- `(B)`, the member whose row moves. -/
def ncB : Term := .app "B" []

/-- `(F (A))`, the application the program builds and the only e-class `@FView` records. -/
def ncFA : Term := .app "F" [ncA]

/-- `(F (B))`, the application the *source* rule builds and the target never names. -/
def ncFB : Term := .app "F" [ncB]

/-- `@Fiat`, the justification every build writes. -/
def ncFiat : Term := .app fiatName []

/-- `@Trans @Fiat @Fiat`, the e-class rebuild rule's composition at `@BView`. -/
def ncTFF : Term := .app transName [ncFiat, ncFiat]

/-- `@Trans (@Sym @Fiat) (@Trans @Fiat @Fiat)`, what `mergeBody` writes at the collision. -/
def ncTST : Term := .app transName [.app symName [ncFiat], ncTFF]

private theorem ncRule_noSet : (Cmd.rule ncRule).NoSet := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain rfl : a = Action.expr (.app "F" [.var "x"]) := by simpa [ncRule] using ha
    trivial
  · intro p hp
    obtain rfl : p = Pattern.expr (.app "F" [.var "x"]) := by simpa [ncRule] using hp
    trivial

private theorem ncRule_noLeafPattern : (Cmd.rule ncRule).NoLeafPattern := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain rfl : p = Pattern.expr (.app "F" [.var "x"]) := by simpa [ncRule] using hp
    intro l
    simp
  · intro v hv
    obtain rfl : v = "x" := by
      simpa [ncRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList] using hv
    refine ⟨Pattern.expr (.app "F" [.var "x"]), by simp [ncRule], ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar]

/-- **The program is in `encode`'s domain.** `Query.VarsKeyed` is the clause to check: `?x`
sits at `F`'s key column, which is what makes the encoded query read it at all. -/
theorem ncProgram_encodeDomain : ncProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc f dc heq
    subst heq
    simp only [ncProgram, List.mem_cons] at hc
    rcases hc with h | h | h | h | h | h | h | h <;> simp_all
  noSet := by
    intro c hc
    simp only [ncProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact ncRule_noSet
    · trivial
    · exact absurd h (by simp)
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  noAtVar := by decide +kernel
  noAtRuleset := by decide +kernel
  noLeafPattern := by
    intro c hc
    simp only [ncProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact ncRule_noLeafPattern
    · trivial
    · exact absurd h (by simp)

/-! ##### The source side, in the kernel

The source is in the constructor fragment, so `exec` and the specification agree on it
(`exec_programStep`) and there is nothing to transcribe: `valueTerms` is `terms` there, one
free variable is enumerated over four terms, and the four congruence closures the round pays
for reduce. -/

/-- The state `ncProgram` runs to. -/
def ncSrc : FDatabase := (exec ncProgram).getD FDatabase.empty

set_option maxRecDepth 100000 in
unseal Egglog.closure in
theorem ncSrc_exec : exec ncProgram = some ncSrc := by
  obtain ⟨d, hd⟩ : ∃ d, exec ncProgram = some d := Option.isSome_iff_exists.mp (by decide)
  rw [hd, ncSrc, hd]
  rfl

set_option maxRecDepth 100000 in
unseal Egglog.closure in
/-- **The source rule built `(F (B))`**, at the substitution `x := (B)` the target's query
cannot offer. -/
theorem ncSrc_mem_FB : ncFB ∈ ncSrc.terms := by decide

set_option maxRecDepth 100000 in
unseal Egglog.closure in
/-- The `union`'s equation, and the only non-reflexive one the source asserts. -/
theorem ncSrc_eqs : ncSrc.eqs = [(ncA, ncB)] := by decide

/-- **And the source state is reachable**, through the refinement theorem rather than by
hand. -/
theorem ncProgram_programStep : ProgramStep Database.empty ncProgram ncSrc.toDatabase :=
  (exec_programStep ncProgram_encodeDomain.ctorDecls
    (Or.inr (by rw [ncSrc_exec]; simp))).mp (by rw [ncSrc_exec]; rfl)

/-! ##### The target side, by the interpreter's own writers

`ncBase` is the state the encoded prelude leaves, computed — eighteen declarations and five
maintenance rules, nothing written. Everything after it is `FDatabase.addRow`, which is what
`execAction` runs at a `set`, plus two `FDatabase.addTerm`s for the entry terms a collision
displaced: `@BView((B), @Fiat)`, the row the e-class rebuild rule's re-keying overwrote, and
`@UF((B), (A), @Trans (@Sym @Fiat) (@Trans @Fiat @Fiat))`, `mergeBody`'s own write settling
against the resident row `identityVals := some 1` keeps. `ncTgt.terms` and `ncTgt.rows` are
`execM (encode ncProgram)`'s, element for element. -/

/-- The state the encoded prelude leaves. -/
def ncBase : FDatabase := (execM (encodePrelude ncProgram)).getD FDatabase.empty

/-- The state `encode ncProgram` runs to: the seven `set`s the blocks emit, and the two entry
terms the merge phases displaced. -/
def ncTgt : FDatabase :=
  ((((((({ ncBase with rules := (encodeRule 0 ncRule 0).1 :: ncBase.rules }
    ).addRow (termName "A") [ncA] []).addRow (viewName "A") [] [ncA, ncFiat]
    ).addRow (termName "F") [ncA, ncFA] []).addRow (viewName "F") [ncA] [ncFA, ncFiat]
    ).addRow (termName "B") [ncB] []).addRow ufName [ncB] [ncA, ncFiat]
    ).addRow (viewName "B") [] [ncA, ncTFF]
    |>.addTerm (Term.app (viewName "B") [ncB, ncFiat])
    |>.addTerm (Term.app ufName [ncB, ncA, ncTST])

/-- Whether `t` is *not* an `@FView` entry keyed at `(B)`. Decidable, and the whole of what
the `Database.ViewsProduct` refutation spends. -/
def ncNoFViewAtB (t : Term) : Bool :=
  match t with
  | .app g (c :: _) => !(g == viewName "F" && c == ncB)
  | _ => true

set_option maxRecDepth 100000 in
theorem ncTgt_subtermClosed : ncTgt.SubtermClosed :=
  (FDatabase.subtermClosedB_iff ncTgt).mp (by decide)

set_option maxRecDepth 100000 in
theorem ncTgt_eqsRefl : ncTgt.EqsRefl := (FDatabase.eqsReflB_iff ncTgt).mp (by decide)

set_option maxRecDepth 100000 in
/-- **`(F (B))`'s only id is `(F (A))`.** The reading is `viewReprsF`, which `mem_viewReprsF_iff`
proves decides `ViewRepr`. -/
theorem ncTgt_viewReprs_FB : viewReprsF ncTgt ncFB = [ncFA] := by decide

/-- **So `(F (B))` does not read to itself**, which is `Database.ReadsSelf` at one term. -/
theorem ncTgt_not_viewRepr_FB : ¬ ViewRepr ncTgt.toDatabase ncFB ncFB := by
  intro h
  have hm := mem_viewReprsF_of_viewRepr ncTgt_eqsRefl h
  rw [ncTgt_viewReprs_FB, List.mem_singleton] at hm
  exact absurd hm (by decide)

set_option maxRecDepth 100000 in
/-- `(B)` *does* read to itself: its own build's view entry survives the collision as an entry
term. This is what makes the product clause's premise available at the key `((B))`. -/
theorem ncTgt_viewRepr_B : ViewRepr ncTgt.toDatabase ncB ncB :=
  viewRepr_of_mem_viewReprsF ncTgt_subtermClosed ncB ncB (by decide)

set_option maxRecDepth 100000 in
/-- **But `(B)` reads to `(A)` as well**, off the row the e-class rebuild rule re-keyed onto the
leader. This is the id the weakened clauses use in place of the term itself. -/
theorem ncTgt_viewRepr_B_A : ViewRepr ncTgt.toDatabase ncB ncA :=
  viewRepr_of_mem_viewReprsF ncTgt_subtermClosed ncB ncA (by decide)

set_option maxRecDepth 100000 in
/-- And `(A)`, the leader, reads to itself: its own build's view entry, never displaced. -/
theorem ncTgt_viewRepr_A : ViewRepr ncTgt.toDatabase ncA ncA :=
  viewRepr_of_mem_viewReprsF ncTgt_subtermClosed ncA ncA (by decide)

set_option maxRecDepth 100000 in
theorem ncTgt_mem_A : ncA ∈ ncTgt.terms := by decide

set_option maxRecDepth 100000 in
theorem ncTgt_mem_B : ncB ∈ ncTgt.terms := by decide

set_option maxRecDepth 100000 in
/-- The `@UF` edge the `union` wrote, keyed at `ordering-max`. -/
theorem ncTgt_mem_uf : Term.app ufName ([ncB] ++ [ncA, ncFiat]) ∈ ncTgt.terms := by decide

set_option maxRecDepth 100000 in
/-- The `@FView` entry the build wrote, keyed at the leader and at nothing else. -/
theorem ncTgt_mem_fview :
    Term.app (viewName "F") ([ncA] ++ [ncFA, ncFiat]) ∈ ncTgt.terms := by decide

@[inherit_doc ncTgt_mem_uf]
theorem ncTgt_out_uf : ncTgt.toDatabase.Out ufName [ncB] [ncA, ncFiat] :=
  ⟨[ncB], CongList.refl (by
      intro a ha
      obtain rfl : a = ncB := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact ncTgt_mem_B),
    by rw [FDatabase.toDatabase_terms]; exact ncTgt_mem_uf⟩

@[inherit_doc ncTgt_mem_fview]
theorem ncTgt_out_fview : ncTgt.toDatabase.Out (viewName "F") [ncA] [ncFA, ncFiat] :=
  ⟨[ncA], CongList.refl (by
      intro a ha
      obtain rfl : a = ncA := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact ncTgt_mem_A),
    by rw [FDatabase.toDatabase_terms]; exact ncTgt_mem_fview⟩

set_option maxRecDepth 100000 in
/-- **No `@FView` row is keyed at `(B)`**: the index fact `patternHolds` reads, and the reason
the encoded rule cannot fire at the source's own substitution. -/
theorem ncTgt_rows_fview : ∀ r ∈ ncTgt.rows, r.fn = viewName "F" → r.args = [ncA] := by decide

set_option maxRecDepth 100000 in
/-- And no `@FView` **entry term** is keyed there either, which is what `Database.Out`
reads. -/
theorem ncTgt_terms_noFViewAtB : ncTgt.terms.all ncNoFViewAtB = true := by decide

@[inherit_doc ncTgt_terms_noFViewAtB]
theorem noFViewAtB_of_all {d : FDatabase} (h : d.terms.all ncNoFViewAtB = true) (e pf : Term) :
    Term.app (viewName "F") [ncB, e, pf] ∉ d.terms := by
  intro hm
  have h' := List.all_eq_true.mp h _ hm
  rw [show ncNoFViewAtB (Term.app (viewName "F") [ncB, e, pf]) = false from rfl] at h'
  exact absurd h' (by simp)

/-! ##### The two over-strong clauses, refuted -/

/-- **`Database.ReadsSelf` is false at the state the encoded program runs to.** It was the first
clause of `Database.UnionsJoined` and the `terms` clause of the command induction's invariant;
both now read *ids* instead, and `ncTgt_unionsJoined` below is that clause holding here. -/
theorem ncTgt_not_readsSelf : ¬ ncTgt.toDatabase.ReadsSelf ncSrc.toDatabase := fun h =>
  ncTgt_not_viewRepr_FB (h ncFB (by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB))

/-- **And `Database.ViewsProduct` is false**, at `f := F`, `as := ((B))` and the id tuple
`((B))` that `ncTgt_viewRepr_B` supplies: `(F (B))` is a source term, `(B)` reads to itself, and
there is no `@FView` entry at that key at all. `Database.ViewsCover.shared` asks for *some*
shared tuple instead, and `ncTgt_shared_FB` is it at this very instance. -/
theorem ncTgt_not_viewsProduct : ¬ ncTgt.toDatabase.ViewsProduct ncSrc.toDatabase := by
  intro h
  obtain ⟨e, pf, bs, hcl, hmem⟩ := h "F" [ncB] [ncB]
    (by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB)
    (.cons ncTgt_viewRepr_B .nil)
  obtain rfl : [ncB] = bs := CongList.eq_of_eqsRefl ncTgt_eqsRefl.toDatabase hcl
  rw [FDatabase.toDatabase_terms] at hmem
  exact noFViewAtB_of_all ncTgt_terms_noFViewAtB e pf hmem

/-! ##### And the conclusions that survive

Which is what says the counterexample kills the *reduction* and not the theorem: the property
`cong_sameClass_of_state` consumes still holds, and so does the correspondence at the pair the
two clauses fail on. -/

/-- **`Database.ViewsCover.shared` holds at the instance its product form fails at**, which is
what says the weakening is a weakening and not a retreat into vacuity: the hypotheses are the
same — `(F (B))` is a source term and `((B))` is pointwise in one class with itself — and the
tuple the clause answers with is `((A))`, the leader tuple, where `@FView` is keyed. -/
theorem ncTgt_shared_FB :
    ncFB ∈ ncSrc.toDatabase.terms ∧
      List.Forall₂ (SameClass ncTgt.toDatabase) [ncB] [ncB] ∧
      ∃ es e pf, ViewReprList ncTgt.toDatabase [ncB] es ∧
        ViewReprList ncTgt.toDatabase [ncB] es ∧
          ncTgt.toDatabase.Out (viewName "F") es [e, pf] :=
  ⟨by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB,
   .cons ⟨ncB, ncTgt_viewRepr_B, ncTgt_viewRepr_B⟩ .nil,
   [ncA], ncFA, ncFiat, .cons ncTgt_viewRepr_B_A .nil, .cons ncTgt_viewRepr_B_A .nil,
   ncTgt_out_fview⟩


/-! ##### And the reduction that answers the clause, here

`ncTgt_shared_FB` is one instance answered by hand. `Database.ViewsCover.of_viewLeaderRows`
answers every instance from two things — an id for the source's own term, and a row at the
*leader* tuple — and this is that reduction run at the state whose non-leader firing refutes the
product form. `rowLead` does real work here and at no earlier witness: the key `((B))` is moved
to `((A))`, which is a positive-arity key, where `satTarget_viewLeaderRows` and
`uRebuilt_viewLeaderRows` have only the empty one. -/

/-- The sixteen terms `ncTgt` holds, as a decidable predicate: seven rows' entry terms, the two
entry terms a merge phase displaced, and their subterms. -/
def ncTermB (t : Term) : Bool :=
  t == Term.app ufName [ncB, ncA, ncTST] || t == ncTST || t == Term.app symName [ncFiat] ||
  t == Term.app (viewName "B") [ncB, ncFiat] || t == Term.app (viewName "B") [ncA, ncTFF] ||
  t == ncTFF || t == Term.app ufName [ncB, ncA, ncFiat] ||
  t == Term.app (termName "B") [ncB] || t == ncB ||
  t == Term.app (viewName "F") [ncA, ncFA, ncFiat] ||
  t == Term.app (termName "F") [ncA, ncFA] || t == ncFA ||
  t == Term.app (viewName "A") [ncA, ncFiat] || t == ncFiat ||
  t == Term.app (termName "A") [ncA] || t == ncA

set_option maxRecDepth 100000 in
@[inherit_doc ncTermB]
theorem ncTgt_terms_all : ncTgt.terms.all ncTermB = true := by decide

@[inherit_doc ncTermB]
private theorem ncTgt_mem_cases {t : Term} (h : t ∈ ncTgt.toDatabase.terms) :
    ncTermB t = true := by
  rw [FDatabase.toDatabase_terms] at h
  exact List.all_eq_true.mp ncTgt_terms_all _ h

/-- A view entry's key is empty when the row is two columns wide. -/
private theorem nc_nil_of_len {cs : List Term} {e pf a b : Term}
    (h : cs ++ [e, pf] = [a, b]) : cs = [] := by
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  exact List.eq_nil_of_length_eq_zero (by omega)

@[inherit_doc nc_nil_of_len]
private theorem nc_singleton_of_len {cs : List Term} {e pf a b c : Term}
    (h : cs ++ [e, pf] = [a, b, c]) : ∃ x, cs = [x] := by
  rcases cs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact absurd (congrArg List.length h)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  · exact ⟨x, rfl⟩
  · exact absurd (congrArg List.length h)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- **The four view rows `ncTgt` holds.** `(B)`'s key carries two e-classes — its own build's,
which the collision displaced but did not delete, and the leader's, which the e-class rebuild
rule wrote — and `@FView` is keyed at `((A))` alone. Of the twelve other terms, three go by
name (`viewName_ne_ufName`, `viewName_ne_termName`, `viewName_ne_transName`) and the rest are
too narrow to be a view entry: a key plus two value columns is two columns at least. -/
private theorem ncTgt_out_view {f : FnName} {cs : List Term} {e pf : Term}
    (ho : ncTgt.toDatabase.Out (viewName f) cs [e, pf]) :
    (f = "A" ∧ cs = [] ∧ e = ncA) ∨ (f = "B" ∧ cs = [] ∧ (e = ncA ∨ e = ncB)) ∨
      (f = "F" ∧ cs = [ncA] ∧ e = ncFA) := by
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : cs = bs := CongList.eq_of_eqsRefl ncTgt_eqsRefl.toDatabase hcl
  have h := ncTgt_mem_cases hmem
  simp only [ncTermB, ncA, ncB, ncFA, ncFiat, ncTFF, ncTST, Bool.or_eq_true, beq_iff_eq] at h
  repeat' rcases h with h | h
  all_goals rw [Term.app.injEq] at h
  all_goals first
    | exact absurd h.1 viewName_ne_ufName
    | exact absurd h.1 viewName_ne_termName
    | exact absurd h.1 viewName_ne_transName
    | (exfalso; have hl := congrArg List.length h.2
       simp only [List.length_append, List.length_cons, List.length_nil] at hl
       all_goals omega)
    | skip
  · obtain rfl : cs = [] := nc_nil_of_len h.2
    obtain rfl : f = "B" := viewName_inj h.1
    have h2 : e = ncB ∧ pf = ncFiat := by simpa [ncB, ncFiat] using h.2
    exact Or.inr (Or.inl ⟨rfl, rfl, Or.inr h2.1⟩)
  · obtain rfl : cs = [] := nc_nil_of_len h.2
    obtain rfl : f = "B" := viewName_inj h.1
    have h2 : e = ncA ∧ pf = ncTFF := by simpa [ncA, ncTFF, ncFiat] using h.2
    exact Or.inr (Or.inl ⟨rfl, rfl, Or.inl h2.1⟩)
  · obtain rfl : f = "F" := viewName_inj h.1
    obtain ⟨x, rfl⟩ : ∃ x, cs = [x] := nc_singleton_of_len h.2
    have h2 : x = ncA ∧ e = ncFA ∧ pf = ncFiat := by simpa [ncA, ncFA, ncFiat] using h.2
    exact Or.inr (Or.inr ⟨rfl, by rw [h2.1], h2.2.1⟩)
  · obtain rfl : cs = [] := nc_nil_of_len h.2
    obtain rfl : f = "A" := viewName_inj h.1
    have h2 : e = ncA ∧ pf = ncFiat := by simpa [ncA, ncFiat] using h.2
    exact Or.inl ⟨rfl, rfl, h2.1⟩

/-- **And the two `@UF` rows, whose ends are both `(B)` and `(A)`**: the `union`'s own write and
`mergeBody`'s settling against it. The only other three-column term is `@FView((A))`, and that
goes by name. -/
private theorem ncTgt_out_uf_cases {x y pf : Term}
    (ho : ncTgt.toDatabase.Out ufName [x] [y, pf]) : x = ncB ∧ y = ncA := by
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : [x] = bs := CongList.eq_of_eqsRefl ncTgt_eqsRefl.toDatabase hcl
  have h := ncTgt_mem_cases hmem
  simp only [ncTermB, ncA, ncB, ncFA, ncFiat, ncTFF, ncTST, Bool.or_eq_true, beq_iff_eq] at h
  repeat' rcases h with h | h
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (rw [Term.app.injEq] at h
       first
         | exact absurd h.1.symm viewName_ne_ufName
         | (exfalso; have hl := congrArg List.length h.2
            simp only [List.length_append, List.length_cons, List.length_nil] at hl
            all_goals omega))

/-- **What `ncTgt` reads a source application as.** Three constructors, and `(B)` is the one
with two ids: its own displaced entry and the leader's. -/
private theorem ncTgt_viewRepr_cases {g : FnName} {bs : List Term} {e : Term}
    (h : ViewRepr ncTgt.toDatabase (.app g bs) e) :
    (g = "A" ∧ e = ncA) ∨ (g = "B" ∧ bs = [] ∧ (e = ncA ∨ e = ncB)) ∨ (g = "F" ∧ e = ncFA) := by
  match h with
  | @ViewRepr.app _ f as cs e pf hl ho =>
    rcases ncTgt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hE⟩ | ⟨rfl, -, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, by cases hl with | nil => rfl, hE⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The union-find representative at `ncTgt`: `(B)`'s class is `(A)`'s and nothing else
moves. -/
def ncLead (t : Term) : Term := if t = ncB then ncA else t

theorem ncLead_ncB : ncLead ncB = ncA := by simp [ncLead]

theorem ncLead_of_ne {t : Term} (h : t ≠ ncB) : ncLead t = t := by simp [ncLead, h]

/-- **`Database.ViewLeaderRows` holds at `ncTgt`, with every clause doing work**, and `rowLead`
at a *key* column for the first time: `@FView` is keyed at `((A))`, which is where `((B))` —
the tuple the source's own build over the non-leader member would name — goes under `lead`.
That is the whole of what `Database.ViewsCover.shared` needed and `Database.ViewsProduct` asked
for at every tuple instead (`ncTgt_not_viewsProduct`). -/
theorem ncTgt_viewLeaderRows : ncTgt.toDatabase.ViewLeaderRows := by
  refine ⟨ncLead, ?_, ?_, ?_, ?_⟩
  · intro t e h
    cases t with
    | lit l =>
        rw [h.eq_of_lit, ncLead_of_ne (by simp [ncB])]
        exact .lit
    | app g bs =>
        rcases ncTgt_viewRepr_cases h with ⟨-, rfl⟩ | ⟨rfl, rfl, (rfl | rfl)⟩ | ⟨-, rfl⟩
        · rwa [ncLead_of_ne (by simp [ncA, ncB])]
        · rwa [ncLead_of_ne (by simp [ncA, ncB])]
        · rw [ncLead_ncB]; exact ncTgt_viewRepr_B_A
        · rwa [ncLead_of_ne (by simp [ncFA, ncB])]
  · intro t e₁ e₂ h₁ h₂
    cases t with
    | lit l => rw [h₁.eq_of_lit, h₂.eq_of_lit]
    | app g bs =>
        rcases ncTgt_viewRepr_cases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, -, (rfl | rfl)⟩ | ⟨rfl, rfl⟩ <;>
            rcases ncTgt_viewRepr_cases h₂ with ⟨h', rfl⟩ | ⟨h', -, (rfl | rfl)⟩ | ⟨h', rfl⟩ <;>
          simp_all [ncLead, ncA, ncB, ncFA]
  · intro x y pf ho
    obtain ⟨rfl, rfl⟩ := ncTgt_out_uf_cases ho
    rw [ncLead_ncB, ncLead_of_ne (by simp [ncA, ncB])]
  · intro f es e pf ho
    refine ⟨e, pf, ?_⟩
    rcases ncTgt_out_view ho with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;>
      simpa [ncLead, ncA, ncB] using ho

set_option maxRecDepth 100000 in
unseal Egglog.closure in
/-- The four terms the source run leaves. -/
theorem ncSrc_terms_eq : ncSrc.terms = [ncFB, ncB, ncFA, ncA] := by decide

set_option maxRecDepth 100000 in
/-- **Every term the source holds has an id here**, which is the command induction's `reads`
clause at this state: four terms, and `(F (B))` — the one a firing built over the non-leader
member — reads the leader's `(F (A))` and nothing else (`ncTgt_viewReprs_FB`). -/
theorem ncTgt_viewRepr_total :
    ∀ t ∈ ncSrc.toDatabase.terms, ∃ e, ViewRepr ncTgt.toDatabase t e := by
  intro t ht
  rw [FDatabase.toDatabase_terms] at ht
  have h : t = ncFB ∨ t = ncB ∨ t = ncFA ∨ t = ncA := by
    rw [ncSrc_terms_eq] at ht
    simpa using ht
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨ncFA, viewRepr_of_mem_viewReprsF ncTgt_subtermClosed ncFB ncFA (by decide)⟩
  · exact ⟨ncB, ncTgt_viewRepr_B⟩
  · exact ⟨ncFA, viewRepr_of_mem_viewReprsF ncTgt_subtermClosed ncFA ncFA (by decide)⟩
  · exact ⟨ncA, ncTgt_viewRepr_A⟩

/-- **So `Database.ViewsCover` holds at `ncTgt`, out of the reduction and not by hand.**
This is the leader-tuple hypothesis checked where it matters: at the state that refutes
`Database.ViewsProduct`, the weakened clause is not merely true (`ncTgt_shared_FB`) but
*derivable* from a row-transport clause and totality, which is the factorisation
`execM_viewsCover` runs. -/
theorem ncTgt_viewsCover : ncTgt.toDatabase.ViewsCover ncSrc.toDatabase :=
  Database.ViewsCover.of_viewLeaderRows ncTgt_viewLeaderRows ncTgt_viewRepr_total

/-- **And `Database.UnionsJoined` holds here**, at the ids: `(A)` and `(B)` are ids of
themselves and the `@UF` edge the `union` wrote runs between them, keyed at `ordering-max`.
This is the clause `unionsJoined_fire` has to preserve, at the state the refutation of its
predecessor is built from. -/
theorem ncTgt_unionsJoined : ncTgt.toDatabase.UnionsJoined ncSrc.toDatabase := by
  intro a b hab hne
  rcases FDatabase.mem_toDatabase_eqs.mp hab with ⟨he, -⟩ | ⟨hm, -, -⟩
  · exact absurd he hne
  · rw [ncSrc_eqs, List.mem_singleton] at hm
    obtain ⟨rfl, rfl⟩ : a = ncA ∧ b = ncB := by
      constructor <;> simp_all [Prod.ext_iff]
    exact ⟨ncA, ncB, ncFiat, ncTgt_viewRepr_A, ncTgt_viewRepr_B, Or.inr ncTgt_out_uf⟩

/-- **`Database.UnionsRead` holds here.** The source asserts one non-reflexive equation and its
two endpoints share the id `(A)`. -/
theorem ncTgt_unionsRead : ncTgt.toDatabase.UnionsRead ncSrc.toDatabase := by
  intro a b hab hne
  rcases FDatabase.mem_toDatabase_eqs.mp hab with ⟨he, -⟩ | ⟨hm, -, -⟩
  · exact absurd he hne
  · rw [ncSrc_eqs, List.mem_singleton] at hm
    obtain ⟨rfl, rfl⟩ : a = ncA ∧ b = ncB := by
      constructor <;> simp_all [Prod.ext_iff]
    exact (sameClassF_iff ncTgt_subtermClosed ncTgt_eqsRefl ncA ncB).mp (by decide)

set_option maxRecDepth 100000 in
unseal Egglog.closure in
/-- **And the correspondence holds at `(F (A))`, `(F (B))`** — the source derives the equation
and the target shares an id for it, which is why the corpus sweep reports nothing here. -/
theorem ncSrc_cong_FA_FB : Cong ncSrc.toDatabase ncFA ncFB :=
  FDatabase.mem_closureF_iff.mp (by decide)

set_option maxRecDepth 100000 in
@[inherit_doc ncSrc_cong_FA_FB]
theorem ncTgt_sameClass_FA_FB : SameClass ncTgt.toDatabase ncFA ncFB :=
  (sameClassF_iff ncTgt_subtermClosed ncTgt_eqsRefl ncFA ncFB).mp (by decide)

/-! ##### The same two refutations at the state `execM` returns

`ncTgt` above is the encoded run's state transcribed; these two do not rely on the
transcription. Their hypotheses are the encoded run and three *decidable* facts about the state
it returns, which is `encode_corresponds_witness`'s discipline — the kernel cannot run an
encoded program, so the run is a hypothesis and the facts are evaluated. -/

/-- **`Database.ReadsSelf` is false at `execM (encode ncProgram)`'s own state.** -/
theorem encode_readsSelf_false {e : FDatabase}
    (he : execM (encode ncProgram) = some e) (hr : e.EqsRefl)
    (hno : ncFB ∉ viewReprsF e ncFB) :
    ∃ src, ncProgram.EncodeDomain ∧ ProgramStep Database.empty ncProgram src ∧
      execM (encode ncProgram) = some e ∧
      ncFB ∈ src.terms ∧ ¬ e.toDatabase.ReadsSelf src :=
  ⟨ncSrc.toDatabase, ncProgram_encodeDomain, ncProgram_programStep, he,
    by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB,
    fun h => hno (mem_viewReprsF_of_viewRepr hr
      (h ncFB (by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB)))⟩

/-- **And so is `Database.ViewsProduct`.** -/
theorem encode_viewsProduct_false {e : FDatabase}
    (he : execM (encode ncProgram) = some e) (hr : e.EqsRefl) (hsc : e.SubtermClosed)
    (hB : ncB ∈ viewReprsF e ncB) (hno : e.terms.all ncNoFViewAtB = true) :
    ∃ src, ncProgram.EncodeDomain ∧ ProgramStep Database.empty ncProgram src ∧
      execM (encode ncProgram) = some e ∧
      ncFB ∈ src.terms ∧ ¬ e.toDatabase.ViewsProduct src := by
  refine ⟨ncSrc.toDatabase, ncProgram_encodeDomain, ncProgram_programStep, he,
    by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB, ?_⟩
  intro h
  obtain ⟨ee, pf, bs, hcl, hmem⟩ := h "F" [ncB] [ncB]
    (by rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB)
    (.cons (viewRepr_of_mem_viewReprsF hsc ncB ncB hB) .nil)
  obtain rfl : [ncB] = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
  rw [FDatabase.toDatabase_terms] at hmem
  exact noFViewAtB_of_all hno ee pf hmem

/-! #### The two target-side residues, by clause -/

/-- **The residue of obligation `trans`, of the rebuild half of obligation `assert`'s `union`
case, and of the *key* half of obligation `congr`. Not proved.**

What is missing: that the ids a source term reads to at an `execM` target are `@UF`-connected
and that the connection has a unique endpoint. Two entries at one view key collide, and
`mergeBody` writes the edge between their e-class columns; `rebuildRules`' e-class rule
follows an edge, so an id's `lead` is read by every term that reads the id;
`pathCompressRule` is what makes the endpoint unique. All three are *specification* rules
fired to saturation, and the hypothesis here is an `execM` target — so what it has to be
proved from is `FDatabase.runSaturateM`'s own fixpoint, and that is strictly weaker than
`RunSaturated` (`execM_contained`: the enumerator under-fires).

**`ufClosed` is the third clause and it is the same mechanism**, which is why the clause that
used to stand beside it — a source term reading its own `@UF` parent — is gone rather than
restated: the edge-following the `union` half needs is edge-following *between ids*, and the
`lead` this residue already has to produce is what carries it. One residue where there were
two, and no weaker for it: `uTgt_not_viewLeader` is `ufClosed` failing one rebuild firing
early, at the state where `Database.UnionsRead` fails with it.

**`rowLead` is the fourth clause and it is the *column* rules, same mechanism one step over**,
which is why `execM_viewsCover_shared` is no longer a residue of its own: obligation `congr`
splits into an id for the source's own term — the command induction's `reads`, whose one open
case is `unionsJoined_fire` — and a row at the leader tuple, which is this. The split is
`Database.ViewsCover.of_viewLeaderRows`, and `ncTgt_viewsCover` is it run at the state whose
non-leader firing refutes `Database.ViewsProduct`.

**That fixpoint is now proved and is not enough.** `FDatabase.RoundClosed` gives every term one
more rebuild round would derive, which is the *conclusion* of each of those four rules; their
*premise* is a row, and `cxTgt_not_indexCurrent` is the compiled statement that the index need
not hold every entry term `Database.Out` reads. What is left is the
run-wide index argument described at "What restores it, and what that costs", plus — for `lead`
being a *function* rather than a relation — `pathCompressRule`'s own fixpoint, which is a
second, independent use of it.

**Non-vacuous at three states, with every clause doing work at one of them**:
`satTarget_viewLeaderRows` (the degenerate one), `Encoding/Match.lean`'s
`uRebuilt_viewLeaderRows` (a real `@UF` edge, two ids for one term) and `ncTgt_viewLeaderRows`
(positive arity, and `rowLead` at a key column the `union` moved). -/
theorem execM_viewLeaderRows {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewLeaderRows := by
  sorry

/-- **The three clauses obligation `trans` spends**, out of the four above. -/
theorem execM_viewLeader {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewLeader :=
  (execM_viewLeaderRows hdom htgt).toViewLeader

/-- **`Database.ViewsCover.shared`, at an `execM` target. Not proved.**

The *product* form of this clause is refuted — `ncTgt_not_viewsProduct`,
`encode_viewsProduct_false` — by the same counterexample that kills `Database.ReadsSelf`: it
asks for an entry at every tuple of ids the children are given, and after `(union (A) (B))` the
term `(B)` is an id of itself while no `@FView` row is keyed there, the rows sitting at the
leader `(A)`. `(F (B))` is a source term because a rule fired at `x := (B)`, so the hypothesis
holds and the conclusion does not.

**What the consumers spend is this, and it survives that state**: `sameClass_congr_of_shared`
uses the clause only at an id tuple *shared* by both argument lists, and `viewRepr_total` only
at the diagonal — neither asks for the product. `ncTgt_shared_FB` is the surviving instance at
the failing key: `(F (B))` and `(F (B))` share the tuple `((A))`, and `@FView((A))` is keyed.

**And that instance generalises, so this is no longer a residue.** The tuple the clause answers
with is the *leader* tuple, and the two things needed to produce it are already residues of
their own: an id for the source's own term, which is the command induction's `reads`, and a row
at the leader tuple, which is `Database.ViewLeaderRows`' `rowLead`.
`Database.ViewsCover.of_viewLeaderRows` is the assembly and it spends nothing else — in
particular no run-wide index argument beyond the one `execM_viewLeaderRows` already carries. -/
theorem execM_viewsCover {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewsCover src :=
  Database.ViewsCover.of_viewLeaderRows (execM_viewLeaderRows hdom htgt)
    (unionsInv_execM hdom hsrc htgt).reads

@[inherit_doc execM_viewsCover]
theorem execM_viewsCover_shared {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ f as bs, Term.app f as ∈ src.terms → List.Forall₂ (SameClass tgt.toDatabase) as bs →
      ∃ es e pf, ViewReprList tgt.toDatabase as es ∧ ViewReprList tgt.toDatabase bs es ∧
        tgt.toDatabase.Out (viewName f) es [e, pf] :=
  (execM_viewsCover hdom hsrc htgt).shared

/-- **The write half of obligation `assert`'s `union` case, at an `execM` target. Proved from
the command induction**, whose one open case is `unionsJoined_fire`.

`out_uf_of_execProgramM` is the read-back at `encodeAction`'s `union` shape — `.set @UF
[ordering-max x₁ x₂] [ordering-min x₁ x₂, pf]`, whose operands are the source expressions
themselves (`encodeBuild_fst`) — threaded through the two operands' builds, which precede it in
the block; the disjunction is which endpoint `ordering-max` picked, and `eval_ifGt` is that
choice. The two ids the clause asks for are the operands' own values, which a *top-level* block
does make ids of themselves (`viewReprAll_self_of_execProgramM`); a head `union` is
`unionsJoined_fire`, and that is the only case left.

**It holds at a state a program reaches, non-vacuously**: `uRebuilt_unionsJoined` in
`Encoding/Match.lean`, over `uProgram`, whose rule head unions two distinct terms.
`uTgt_not_unionsRead` there is the conclusion failing one rebuild firing *earlier*, where this
clause holds and `Database.ViewLeader.ufClosed` does not — so the two are load-bearing
separately. -/
theorem execM_unionsJoined {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.UnionsJoined src :=
  (unionsInv_execM hdom hsrc htgt).joined

/-- **The residue of obligation `assert`'s `union` half**, assembled from the `union`'s own
write and the rebuild that follows it — and from nothing about the source's terms, which is
what `ncTgt_not_readsSelf` costs. `UnionsRead` itself holds at that counterexample
(`ncTgt_unionsRead`); it is the factorisation through `Database.ReadsSelf` that did not. -/
theorem execM_unionsRead {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.UnionsRead src :=
  unionsRead_of_unionsJoined (execM_viewLeader hdom htgt) (execM_unionsJoined hdom hsrc htgt)

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
hypothesis is one shared id tuple, and `ViewsCover.shared` is the view entry at it — the
rebuild's whole contribution, isolated. The second self-congruence premise is unused. -/
theorem encode_congr {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (f : FnName) (as bs : List Term) (ha : Cong src (.app f as) (.app f as))
    (_hb : Cong src (.app f bs) (.app f bs))
    (hl : List.Forall₂ (SameClass tgt.toDatabase) as bs) :
    SameClass tgt.toDatabase (.app f as) (.app f bs) :=
  sameClass_congr_of_shared (execM_viewsCover hdom hsrc htgt) ha hl


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
