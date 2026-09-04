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
  target asserts no equation but a reflexive one. At an `execM` target this is now a
  **theorem** — `execM_encode_eqsRefl`, out of `execM_noUnions`: `encode` emits no
  `Action.union` anywhere (a source `union` becomes a `set` of a `@UF` edge) and
  `FDatabase.addEq` is the interpreter's only writer of `eqs`. `difftest correspond`'s
  `tgt-eqs` column is the same quantity measured, 0 on every case.

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
  rows, so the sandwich that closes over the first does not close over the second. The
  **rows** are settled all the same, and by the test rather than by the sandwich:
  `FDatabase.RowsClosed` and `rowsClosed_of_execProgramM` read the other conjunct of
  `FDatabase.sameData`, which pins a further round's row list *equal* to the pre-state's.
* **Refuted, and it is why the fixpoint closes neither target-side residue**:
  `FDatabase.IndexCurrent`,
  the converse of `FDatabase.IndexOk.entry` — every entry term still current in the index.
  `cxTgt_not_indexCurrent` refutes it at a state built by the interpreter's own writers at the
  encoding's own declarations, where a source `union` collides two e-classes at one view key,
  `mergeOneOriented` deletes the displaced row, and `Database.Out` still reads its entry term.
  A rebuild rule's *conclusion* is a `terms` fact the fixpoint supplies; its *premise* is a
  `rows` fact only this would, so `IndexOk` needs a companion rather than a fourth field, and
  the companion is false. What survives is the same claim **up to the union-find**, and
  `cxTgt_currentUF` is that at the refuting state itself: the entry's own value columns are in
  no row any more, and the row the merge kept sits at the `@UF` parent of the e-class column it
  displaced. That weakened claim is what `execM_rebuildClosed` is left waiting on, and it is
  still a `rows` fact wanted from a `terms` fact — which is why it is the *bridge* and not the
  residue's statement that carries the gap now.
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

* **Weakened, and the strong form kept with a separation against it**:
  `Database.ViewLeaderRows`. Its four clauses were assembled before that lesson and are
  over-strong in the same way: every consumer spends them through the *choice function* `lead`,
  and only ever to name one id it then hands to `hmem`. `Database.ViewJoined` is the three
  things actually spent — `ids` for `SameClass.trans_of_viewJoined`, `ufJoin` for
  `unionsRead_of_viewJoined`, `rowShared` for `Database.ViewsCover.of_viewJoined` — each an
  **upper bound** in `Database.Absorbs` rather than a representative.
  `Database.ViewLeaderRows.toViewJoined` is the check that this is a weakening, and `chainD` is
  the check that it is a *strict* one: an ascending chain of ids with upper bounds everywhere
  and no top, at which `chainD_viewJoined` holds and `chainD_not_viewLeader` fails. What that
  buys is a whole mechanism — `pathCompressRule` was in that residue only to make
  `lead` a function — and the diagonal instance of `rowShared`, which is all `viewRepr_total`
  spends, is now answered by the row already in hand rather than by the column rules.
  `uTgt_not_viewJoined` is the weakened clause still **failing** one rebuild firing early, at
  the state `uTgt_not_viewLeader` fails at, so the weakening is not into vacuity.

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
* **`sorry`**, two, and they are two *mechanisms* rather than three clauses — which is
  what the factorisation above bought. `execM_rebuildClosed` is the whole of the run-wide
  **index** argument, now stated per rule rather than per clause: `Database.RebuildClosed` is
  `rebuildRules`' e-class rule (`eclass`), its column rules (`column`) and the `@UF` edge a
  collision writes (`edged`), and `Database.RebuildClosed.toViewJoined` is what `execM_viewJoined`
  now is. `pathCompressRule` is no longer part of it — it was carried solely to make
  `lead` a *function*, and no consumer spends that. Each clause concludes a common
  `Database.Lands` and not absorption along the edge it is handed:
  `Database.RebuildClosedStrong` is the form that did, `cxStale_not_rebuildClosedStrong`
  refutes it at two `union`s in one block, and `Database.RebuildClosed.of_strong` is the check
  that the weakening is one. `unionsJoined_fire` is the
  whole of a **target firing behind a source firing** — the one command case the read-back does
  not reach — and it now carries both of the command induction's data clauses, `joined` and
  `reads`, because a rule head builds as well as unions and one firing answers both.
  `Encoding/Complete.lean`'s `execM_soundTerms` is the completeness half — it is stated there
  and not here because it consumes `Encoding/Match.lean`'s two head writers, which are
  downstream — and the state's own equations are no longer part of it: `execM_encode_eqsRefl`
  makes the target's `Cong` the identity, so `Database.ViewsSound` and `Database.EdgesSound`
  there are two clauses about the **term list** (`viewsSound_of_soundTerms` is the step back,
  `soundTerms_of_viewsSound` the step out), which is the form that is monotone along a run and
  so the form an induction can carry. The *source* firing behind the target's is proved —
  `mem_terms_of_headBuild_of_domain` and `mem_eqs_of_headUnion_of_domain` are `hfired`'s two
  shapes, out of `EncodeDomain.headsDeclared` and `EncodeDomain.noLitUnion` — and so is the
  **merge phase**: `mergeSaturateF_soundTerms` is every term a merge pass adds, justified,
  which is half the writer enumeration and the half the two named obstacles stood in front of
  (`Signature.MergeShape` for the body's shape, `eq_of_congrKeys` for the keys being equal
  rather than merely congruent). The fold over **rule firings** is now proved too —
  `execRunRules_soundTerms` through `fireRule_soundTerms` and `fireInto_soundTerms`, and
  `runRoundM_soundTerms` with the merge phase after it — as is the **rule invariant** it needed
  (`execM_encode_rules`, `mergeShapeOk_encodePrelude`'s shape one level up: every rule a target
  holds is an `encodeRule` of a source rule or one of `maintenanceRules`) and the three
  **maintenance families** the invariant splits off (`maintenance_soundTerms`, out of
  `pathCompressRule_soundTerms`, `eclassRule_soundTerms` and `columnRule_soundTerms`).
  `firingsSound_of_rulesEncoded` is the factorisation those leave, and both halves of it are
  now proved: `FDatabase.EncOk.stepCmds` is the per-command induction that aligns the source
  run with the target's, and `encodedHeadSound` is one firing of one **encoded source rule** —
  under `Program.HeadsScoped`, which is `EncodeDomain.headsScoped`.
  `bare_build_invents_equality` below is why that had to become a clause, and
  `Encoding/Complete.lean`'s `execM_soundTerms` is proved with it. No target fixpoint enters,
  since soundness is indifferent to the under-firing `execM_contained` records.
  `ncTgt_soundTerms` is both clauses at the state the two refuted forward clauses fail at, with
  a real `@UF` edge and positive arity. `execM_viewsCover`,
  `execM_viewsCover_shared`, `execM_unionsJoined` and `execM_unionsRead` are assembled from
  them, proved. `Encoding/Match.lean`'s `uRebuilt_unionsJoined`, `uRebuilt_viewLeaderRows`,
  `uRebuilt_viewJoined` and `uRebuilt_viewsCover` are the properties at a state a program
  reaches, with `uRebuilt_cong_sameClass` running the forward half there; `uTgt_not_unionsRead`,
  `uTgt_not_viewLeader` and `uTgt_not_viewJoined` are the conclusion and the responsible clause
  — strong form and weak — failing one rebuild firing earlier; `ncTgt_viewLeaderRows` is the
  fourth clause at positive arity, where the three earlier witnesses have only the empty key.
  `encode_assert`, `encode_trans`,
  `encode_congr`, `encode_corresponds_forward` and — in `Encoding/Complete.lean` —
  `encode_corresponds` are assembled from them and carry `sorryAx` through them.
  `Encoding/Complete.lean`'s `encode_corresponds_complete` does **not**: the completeness half
  is proved.
* **Refuted without a clause, and the clause is now the domain's.**
  `bare_build_invents_equality`: `encodeBuild` emits **no action** for a leaf, so a rule head
  that builds a bare variable the query does not bind stops the *source* block there and the
  encoded block skips it and runs on — a third shape of stuck head beside `noLitUnion`'s and
  `headsDeclared`'s. At `bareProgram` the source relates `(A)` and `(B)` in no way and the
  encoded run puts them in one class, so `encode_corresponds_complete` is false there, at a
  pair of source e-nodes. `EncodeDomain.headsScoped` is the clause that excludes it,
  `bareProgram_not_headsScoped` is that program failing it and
  `bareProgram_encodeDomain_but_headsScoped` is every other clause holding, so the clause is
  the only thing between the domain and the refutation. It is faithfulness rather than a
  narrowing — egglog raises `TypeError::Unbound` for an action's unbound variable in
  `to_core_actions` (`egglog/src/core.rs:663-670`) — and the census is unmoved at 70 of 166.
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

/-- **`EncodeDomain.setLegal` is "no `set` anywhere", in the form the cases below use.**
`Program.setLegal_iff_noSet` at the empty signature, which declares constructors only. -/
theorem Program.EncodeDomain.noSet {P : Program} (h : P.EncodeDomain) : ∀ c ∈ P, c.NoSet :=
  (Program.setLegal_iff_noSet (fun _ => rfl) h.ctorsOnly).mp h.setLegal

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

/-! #### And the same four clauses, at what their consumers spend

`Database.ViewLeaderRows` was assembled before `Database.ViewsCover` and
`Database.UnionsJoined` were cut down to their consumers, and it is over-strong in the same
way they were. Every one of its four clauses is spent through a *choice function* — `lead` is
total on `Term` and `huniq` forces it constant across the whole "some term reads both"
closure — while each of the three reductions downstream (`SameClass.trans_of_viewLeader`,
`unionsRead_of_unionsJoined`, `Database.ViewsCover.of_viewLeaderRows`) uses that function only
to name **one** id it then hands to `hmem`. What is spent is therefore a *join*, not a
representative, and `Database.ViewJoined` below is that. -/

/-- **`e'` absorbs `e`**: every source term that reads `e` also reads `e'`.

This is what `Database.ViewLeaderRows`' first clause says of `lead e`, and it is the only
shape in which the other three are consumed: each of them produces an id and then hands it to
`hmem` at a term that read the id it started from. A preorder rather than a function, which is
the whole of the weakening — `Database.ViewJoined` asks for upper bounds in it and never for a
representative. -/
def Database.Absorbs (d : Database) (e e' : Term) : Prop :=
  ∀ t, ViewRepr d t e → ViewRepr d t e'

/-- Absorption is reflexive and transitive; both are one unfolding. -/
theorem Database.Absorbs.refl (d : Database) (e : Term) : d.Absorbs e e := fun _ h => h

@[inherit_doc Database.Absorbs.refl]
theorem Database.Absorbs.trans {d : Database} {e₁ e₂ e₃ : Term} (h₁ : d.Absorbs e₁ e₂)
    (h₂ : d.Absorbs e₂ e₃) : d.Absorbs e₁ e₃ := fun t h => h₂ t (h₁ t h)

/-- **What the forward half's three reductions actually spend of `Database.ViewLeaderRows`.**

Three clauses, each read off one consumer and nothing else:

* `ids` is `SameClass.trans_of_viewLeader`. Two ids of one term have a common **absorber** —
  not a common `lead`. The choice function is what `pathCompressRule` was being sought for
  (`lead` a function rather than a relation), and no consumer asks for it: `trans` needs one id
  the outer two terms both reach, and an upper bound of the middle term's two ids is one.
* `ufJoin` is `unionsRead_of_unionsJoined`, at `Database.ViewLeader.ufClosed`'s own instance:
  an `@UF` edge's two ends have a common absorber. Same weakening — the reduction rewrites
  `lead x = lead y` and then applies `hmem` twice, which is an upper bound and nothing more.
* `rowShared` is `Database.ViewsCover.of_viewLeaderRows`, at `rowLead`'s own instance: a row
  and a pointwise-congruent argument list give **some** tuple both lists read that carries a
  row. Not the *leader* tuple — the tuple `Database.ViewsCover.shared` answers with is
  existential, so the answer need not move the key at all. In particular the diagonal
  (`as = bs`), which is all `viewRepr_total` spends, is answered by the row already in hand,
  where `rowLead` demanded the column rules even there.

`Database.ViewLeaderRows.toViewJoined` is the check that this is a weakening rather than a
different claim, and it uses all four of the strong clauses. `uTgt_not_viewJoined` is the
weakened form still **failing** one rebuild firing early, at the state
`uTgt_not_viewLeader` fails at — so the e-class rebuild rule is still load-bearing here and the
weakening is not into vacuity. What has dropped out is `pathCompressRule`: nothing below names
a function. -/
structure Database.ViewJoined (d : Database) : Prop where
  /-- Two ids of one term have a common absorber. -/
  ids : ∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ →
    ∃ e, d.Absorbs e₁ e ∧ d.Absorbs e₂ e
  /-- An `@UF` edge's two ends have a common absorber. -/
  ufJoin : ∀ x y pf, d.Out ufName [x] [y, pf] → ∃ e, d.Absorbs x e ∧ d.Absorbs y e
  /-- A row, and an argument list pointwise in one class with the one that read its key, share
  a tuple that carries a row. -/
  rowShared : ∀ f as bs es e pf, ViewReprList d as es → d.Out (viewName f) es [e, pf] →
    List.Forall₂ (SameClass d) as bs →
    ∃ es' e' pf', ViewReprList d as es' ∧ ViewReprList d bs es' ∧
      d.Out (viewName f) es' [e', pf']

/-- **Obligation `trans` reduces to `Database.ViewJoined.ids`**, which is the whole of what
`SameClass.trans_of_viewLeader` spends: the middle term's two ids have an absorber, and an
absorber of an id is read by everything that reads the id. -/
theorem SameClass.trans_of_viewJoined {d : Database} (h : d.ViewJoined) {a b c : Term}
    (hab : SameClass d a b) (hbc : SameClass d b c) : SameClass d a c := by
  obtain ⟨e₁, ha₁, hb₁⟩ := hab
  obtain ⟨e₂, hb₂, hc₂⟩ := hbc
  obtain ⟨e, k₁, k₂⟩ := h.ids b e₁ e₂ hb₁ hb₂
  exact ⟨e, k₁ a ha₁, k₂ c hc₂⟩


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

/-- **The strong form implies the weak one**, and this is the check that `Database.ViewJoined`
is a weakening of `Database.ViewLeaderRows` rather than a different claim — the same discipline
`Database.ViewsCover.of_viewsProduct` and `Database.UnionsJoined.of_readsSelf` are.

All four strong clauses are used: `hmem` in each of the three, `huniq` in `ids` and in the row
transport, `huf` in `ufJoin`, `hrow` in `rowShared`. Each absorber is `lead` of the *first* id,
and the second is carried onto it by `huniq`/`huf` — which is exactly the rewriting the three
reductions did by hand, now done once. -/
theorem Database.ViewLeaderRows.toViewJoined {d : Database} (h : d.ViewLeaderRows) :
    d.ViewJoined := by
  obtain ⟨lead, hmem, huniq, huf, hrow⟩ := h
  refine ⟨fun t e₁ e₂ h₁ h₂ => ⟨lead e₁, fun s hs => hmem s e₁ hs, fun s hs => ?_⟩,
    fun x y pf ho => ⟨lead x, fun s hs => hmem s x hs, fun s hs => ?_⟩,
    fun f as bs es e pf hes ho hl => ?_⟩
  · rw [← huniq t e₂ e₁ h₂ h₁]; exact hmem s e₂ hs
  · rw [huf x y pf ho]; exact hmem s y hs
  · obtain ⟨e', pf', ho'⟩ := hrow f es e pf ho
    exact ⟨es.map lead, e', pf', viewReprList_map_lead hmem hes,
      viewReprList_map_lead_of_forall₂ hmem huniq hl hes, ho'⟩

/-- **The weak form answers the clause too, and in one step.** `rowShared` *is* obligation
`congr`'s target side, stated at a row rather than at a source term, so the only thing this
reduction adds is the source term's own reading — which is the command induction's `reads`,
exactly as in `Database.ViewsCover.of_viewLeaderRows`.

No transport: where the strong reduction moved both argument lists onto `es.map lead`, the
clause here hands back a tuple both already read, so `viewReprList_map_lead` and
`viewReprList_map_lead_of_forall₂` are spent inside `Database.ViewLeaderRows.toViewJoined`
and nowhere else. -/
theorem Database.ViewsCover.of_viewJoined {src d : Database} (h : d.ViewJoined)
    (ht : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) : d.ViewsCover src where
  shared f as bs ha hl := by
    obtain ⟨e, he⟩ := ht _ ha
    match he with
    | @ViewRepr.app _ _ _ es _ pf hes ho => exact h.rowShared f as bs es e pf hes ho hl

/-! #### And the three maintenance closures those three clauses reduce to

`Database.ViewJoined` is stated at what its *consumers* spend. Its own content is the
maintenance ruleset, one mechanism per clause — `ufJoin` is the e-class rebuild rule
(`uTgt_not_viewJoined` is that clause failing one firing before it runs), `rowShared` is the
column rules, and `ids` is the `@UF` edge `mergeBody` writes between two entries that collide
at one view key. `Database.RebuildClosed` below is that reading, as three properties named
after the rules rather than after the consumers, and `Database.RebuildClosed.toViewJoined` is
the reduction.

**Everything here is stated over `Database.Out`, and so over `terms`.** No row, no choice
function, no leader. That is what makes the reduction independent of the index question — and
it is also why it does not *close* the residue: each of the three is a rule's **conclusion**,
and the premise of each is a row. -/

/-- **One `@UF` edge, as `Database.Out` reads it.** `UFEdge` is the same relation with the
self-loops taken out; nothing below needs an edge to move, so nothing below takes them out. -/
def Database.UFStep (d : Database) (a b : Term) : Prop := ∃ pf, d.Out ufName [a] [b, pf]

/-- Reachability along those edges: the chain a run of rebuild firings walks. -/
def Database.UFReach (d : Database) (a b : Term) : Prop :=
  Relation.ReflTransGen d.UFStep a b

/-- One edge is a chain. -/
theorem Database.UFStep.toReach {d : Database} {a b : Term} (h : d.UFStep a b) :
    d.UFReach a b := Relation.ReflTransGen.single h

/-- **A landing site of `e`**: a point the union-find reaches from `e` that also absorbs it.

Every clause of `Database.RebuildClosed` is stated over this conjunction, and neither half
can be dropped. `Database.UFReach` alone is too weak as a *conclusion* — an `@UF` entry the
run has since superseded is still reachable and nothing reads its far end, which is what
`cxStale_not_absorbs_CB` exhibits — and
`Database.Absorbs` alone is too weak as a *hypothesis*, since `column` is the rules moving a
key along the union-find and not onto an arbitrary upper bound.

A preorder, because both components are, which is what lets the clauses compose without a
chain induction. -/
def Database.Lands (d : Database) (e e' : Term) : Prop := d.UFReach e e' ∧ d.Absorbs e e'

/-- Landing is reflexive and transitive, componentwise. -/
theorem Database.Lands.refl (d : Database) (e : Term) : d.Lands e e :=
  ⟨.refl, Database.Absorbs.refl d e⟩

@[inherit_doc Database.Lands.refl]
theorem Database.Lands.trans {d : Database} {e₁ e₂ e₃ : Term} (h₁ : d.Lands e₁ e₂)
    (h₂ : d.Lands e₂ e₃) : d.Lands e₁ e₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- **The maintenance ruleset's three closures at their strongest, as they were first
stated. REFUTED at its `eclass` clause** — `cxStale_not_rebuildClosedStrong`, at a state built
by the interpreter's own writers over the encoding's own declarations — and kept for the reason
`Database.ViewsProduct` and `Database.ReadsSelf` are kept: so that the weakening below is
*checked* (`Database.RebuildClosed.of_strong`) rather than asserted, and so that the state it
fails at is written down. `uTgt_not_rebuildClosedStrong` is the *other* state it fails at, the
one the weak form fails at too.

The three clauses read off `rebuildRules` and `mergeBody` directly — `eclass` the e-class
rebuild rule, `edged` the `@UF` edge a collision at one view key leaves, `column` the column
rebuild rules — and it is `eclass` that is over-strong. `Database.UFStep` is an `@UF` **entry
term**, so it ranges over every edge the run ever wrote; a later `union` supersedes one and
`FDatabase.mergeOneOriented` deletes the row that carried it, and no firing at the fixpoint
puts a reader of `a` on the *stale* `b`. `Database.RebuildClosed` asks instead for a common
landing site, which is what `Database.ViewJoined.ufJoin` consumes and what the union-find
still delivers. -/
def Database.RebuildClosedStrong (d : Database) : Prop :=
  (∀ a b, d.UFStep a b → d.Absorbs a b) ∧
    (∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → ∃ e, d.UFReach e₁ e ∧ d.UFReach e₂ e) ∧
    (∀ f es ds e pf, d.Out (viewName f) es [e, pf] → List.Forall₂ d.UFReach es ds →
      ∃ e' pf', d.Out (viewName f) ds [e', pf'])

/-- **Absorption along a chain**, by induction on the chain: the strong `eclass` at one edge
and `Database.Absorbs.trans` to compose. This is where a *representative* would have been
needed had the clauses still asked for one — an upper bound composes and a choice function
does not.

Spent only inside `Database.RebuildClosed.of_strong`. The weakened clauses carry their own
absorption in `Database.Lands` and compose nothing. -/
theorem Database.absorbs_of_eclass {d : Database}
    (h : ∀ a b, d.UFStep a b → d.Absorbs a b) {a b : Term} (hr : d.UFReach a b) :
    d.Absorbs a b := by
  induction hr with
  | refl => exact Database.Absorbs.refl d a
  | tail _ hstep ih => exact ih.trans (h _ _ hstep)

/-- **The maintenance ruleset's three closures, at a state, and at what a stale edge can
still deliver.**

Read off `rebuildRules` and `mergeBody`, one clause each, and every one of them concluding a
common `Database.Lands`:

* `eclass` is the e-class rebuild rule. Its head re-`set`s a view entry at the `@UF` parent
  of the e-class column it read, so an id and the parent an entry records for it end up with
  a **common landing site** — the current leader, which both reach and which absorbs both.
  Absorption along the recorded edge itself is `Database.RebuildClosedStrong`'s clause and is
  what a superseded edge fails.
* `edged` is not a rule but the `:merge` body: two entries that collide at one view key leave
  an `@UF` edge between their e-class columns, so two ids of one term land on one point.
  Stated with absorption rather than with reachability alone because that is what `ids` and
  `rowShared` spend, and because a chain of edges no longer composes to absorption once
  `eclass` is join-shaped.
* `column` is the column rebuild rules, one per child position, each moving its column to the
  `@UF` parent it read. Restricted to landing sites for the same reason `eclass` is weakened:
  two `union`s that share their `ordering-max` endpoint collide inside one merge phase, so the
  displaced edge is an entry no rebuild ever ran on and no view row is keyed at its far end.

**`pathCompressRule` is absent**, and so is any function on `Term`. -/
structure Database.RebuildClosed (d : Database) : Prop where
  /-- The e-class rebuild rule: an id and a recorded parent of it land on one point. -/
  eclass : ∀ a b, d.UFStep a b → ∃ e, d.Lands a e ∧ d.Lands b e
  /-- The edge a collision writes: two ids of one term land on one point. -/
  edged : ∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → ∃ e, d.Lands e₁ e ∧ d.Lands e₂ e
  /-- The column rebuild rules: a row's key may be moved onto landing sites, column by
  column. -/
  column : ∀ f es ds e pf, d.Out (viewName f) es [e, pf] → List.Forall₂ d.Lands es ds →
    ∃ e' pf', d.Out (viewName f) ds [e', pf']

/-- **The strong form implies the weak one**, and this is the check that the weakening is a
weakening rather than a different claim — the same discipline
`Database.ViewsCover.of_viewsProduct`, `Database.UnionsJoined.of_readsSelf` and
`Database.ViewLeaderRows.toViewJoined` are.

All three strong clauses are used, and `eclass` twice: once as its own clause, where the
landing site is the edge's own far end, and once through `Database.absorbs_of_eclass` to give
`edged`'s reachability its absorption. `column` is the same clause on a smaller hypothesis. -/
theorem Database.RebuildClosed.of_strong {d : Database} (h : d.RebuildClosedStrong) :
    d.RebuildClosed where
  eclass a b hs := ⟨b, ⟨hs.toReach, h.1 a b hs⟩, Database.Lands.refl d b⟩
  edged t e₁ e₂ h₁ h₂ := by
    obtain ⟨e, r₁, r₂⟩ := h.2.1 t e₁ e₂ h₁ h₂
    exact ⟨e, ⟨r₁, Database.absorbs_of_eclass h.1 r₁⟩,
      ⟨r₂, Database.absorbs_of_eclass h.1 r₂⟩⟩
  column f es ds e pf ho hl := h.2.2 f es ds e pf ho (hl.imp fun _ _ k => k.1)

/-- **A pointwise-congruent pair of argument lists lands on a common id tuple**, and both
lists read it: `edged` at each position gives the tuple and the absorption it carries puts
both lists on it. This is what `Database.ViewLeaderRows` did with
`viewReprList_map_lead_of_forall₂`, without the function — and now without the chain walk
either, since `edged` delivers the absorption rather than `eclass` composing to it. -/
theorem Database.RebuildClosed.reach_of_forall₂ {d : Database} (h : d.RebuildClosed) :
    ∀ {as bs : List Term}, List.Forall₂ (SameClass d) as bs →
      ∀ {es : List Term}, ViewReprList d as es →
        ∃ ds, List.Forall₂ d.Lands es ds ∧ ViewReprList d as ds ∧ ViewReprList d bs ds
  | [], [], .nil, [], .nil => ⟨[], .nil, .nil, .nil⟩
  | a :: _, b :: _, .cons hab hl, e :: _, .cons hae hes => by
      obtain ⟨c, hac, hbc⟩ := hab
      obtain ⟨x, k₁, k₂⟩ := h.edged a e c hae hac
      obtain ⟨ds, hr, h₁, h₂⟩ := h.reach_of_forall₂ hl hes
      exact ⟨x :: ds, .cons k₁ hr, .cons (k₁.2 a hae) h₁, .cons (k₂.2 b hbc) h₂⟩

/-- **The three closures answer the three clauses**, one apiece and with nothing left over.

`ids` is `edged` read at its absorption half; `ufJoin` is `eclass` read at the same half, so
the clause costs one firing and no join at all; `rowShared` is `reach_of_forall₂` for the
tuple and `column` for the row on it.

The **diagonal** instance of `rowShared` (`as = bs`) still costs nothing: `reach_of_forall₂`
answers it with reflexivity at each position when the two readings coincide, and `column` is
then asked at `ds = es`. What the strong form demanded there — `rowLead` moving every key to
the leader tuple — is not asked at all. -/
theorem Database.RebuildClosed.toViewJoined {d : Database} (h : d.RebuildClosed) :
    d.ViewJoined where
  ids t e₁ e₂ h₁ h₂ := by
    obtain ⟨e, k₁, k₂⟩ := h.edged t e₁ e₂ h₁ h₂
    exact ⟨e, k₁.2, k₂.2⟩
  ufJoin x y pf ho := by
    obtain ⟨e, k₁, k₂⟩ := h.eclass x y ⟨pf, ho⟩
    exact ⟨e, k₁.2, k₂.2⟩
  rowShared f as bs es e pf hes ho hl := by
    obtain ⟨ds, hr, h₁, h₂⟩ := h.reach_of_forall₂ hl hes
    obtain ⟨e', pf', ho'⟩ := h.column f es ds e pf ho hr
    exact ⟨ds, e', pf', h₁, h₂, ho'⟩

/-- **A state with no `@UF` entry has no chain either**, which is what makes the two clauses
that read one vacuous at a union-free target. -/
theorem Database.UFReach.eq_of_no_uf {d : Database}
    (hno : ∀ a b, ¬ d.UFStep a b) {a b : Term} (h : d.UFReach a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd hstep (hno _ _)

/-- A `List.Forall₂` over a relation that forces equality is equality. -/
theorem Database.forall₂_ufReach_eq {d : Database} (hno : ∀ a b, ¬ d.UFStep a b) :
    ∀ {es ds : List Term}, List.Forall₂ d.UFReach es ds → es = ds
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by
      rw [Database.UFReach.eq_of_no_uf hno h, Database.forall₂_ufReach_eq hno hl]

/-- **`Database.ViewJoined` at `satTarget`**, out of the reduction. The degenerate case: one
nullary constructor, no `union`, so `ufJoin` is vacuous, `ids` is answered by reflexivity and
`rowShared` by the row already in hand. `Encoding/Match.lean`'s `uRebuilt_viewJoined` is the
first two clauses doing work and `ncTgt_viewJoined` the third. -/
theorem satTarget_viewJoined : satTarget.ViewJoined :=
  satTarget_viewLeaderRows.toViewJoined

/-- **And `Database.RebuildClosedStrong` at `satTarget`, out of the definition rather than
through `Database.ViewLeaderRows`** — that form does not imply it, since it says nothing about
which ids the union-find joins. `Database.RebuildClosed.of_strong` carries it to the residue's
own form below.

The degenerate case again, and every clause is degenerate for its own reason: `satTarget` has
no `@UF` entry (`satTarget_no_uf`), so `eclass` is vacuous and `Database.UFReach` is equality
(`Database.UFReach.eq_of_no_uf`); `edged` is then two ids of one term being *equal*, which
`satTarget_viewRepr` gives; and `column` is asked at `ds = es`, where the row handed in is the
answer. `Encoding/Match.lean`'s `uRebuilt_rebuildClosedStrong` is the same property where the
edge is real. -/
theorem satTarget_rebuildClosedStrong : satTarget.RebuildClosedStrong := by
  have hno : ∀ a b, ¬ satTarget.UFStep a b := by
    rintro a b ⟨pf, bs, -, hmem⟩
    exact satTarget_no_uf _ hmem
  refine ⟨fun a b h => absurd h (hno a b), fun t e₁ e₂ h₁ h₂ => ⟨e₁, .refl, ?_⟩,
    fun f es ds e pf ho hl => ?_⟩
  · obtain rfl : e₂ = e₁ := by
      cases t with
      | lit l => rw [h₁.eq_of_lit, h₂.eq_of_lit]
      | app g bs => rw [satTarget_viewRepr h₁, satTarget_viewRepr h₂]
    exact .refl
  · obtain rfl : es = ds := Database.forall₂_ufReach_eq hno hl
    exact ⟨e, pf, ho⟩

@[inherit_doc satTarget_rebuildClosedStrong]
theorem satTarget_rebuildClosed : satTarget.RebuildClosed :=
  Database.RebuildClosed.of_strong satTarget_rebuildClosedStrong

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

/-- **The same reduction at what it spends**: `Database.ViewJoined.ufJoin` in place of
`Database.ViewLeader`. The edge's two ends have an absorber and each endpoint's own id reaches
it, so the absorber is the shared id — the orientation is answered by taking the join in the
other order, since a common absorber is symmetric in the two ends. -/
theorem unionsRead_of_viewJoined {src d : Database} (hj : d.ViewJoined)
    (h : d.UnionsJoined src) : d.UnionsRead src := by
  intro a b hab hne
  obtain ⟨e₁, e₂, pf, h₁, h₂, ho⟩ := h a b hab hne
  rcases ho with ho | ho
  · obtain ⟨e, k₁, k₂⟩ := hj.ufJoin e₁ e₂ pf ho
    exact ⟨e, k₁ a h₁, k₂ b h₂⟩
  · obtain ⟨e, k₂, k₁⟩ := hj.ufJoin e₂ e₁ pf ho
    exact ⟨e, k₁ a h₁, k₂ b h₂⟩

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

/-- **The whole forward half again, at what the three obligations spend.** One target property
where `cong_sameClass_of_state` takes three, because `Database.ViewsCover` and
`Database.UnionsRead` are each `Database.ViewJoined` plus one of the *data* clauses the command
induction carries: `ht` (`UnionsInv.reads`, every source term having an id) and
`Database.UnionsJoined` (the `union`'s own write, at ids).

So the forward half is now `Database.ViewJoined` at an `execM` target plus `unionsJoined_fire`,
and nothing else. `cong_sameClass_of_state` stays because it is the statement the three
*named* properties support and `Encoding/Match.lean`'s `uRebuilt_cong_sameClass` runs it. -/
theorem cong_sameClass_of_joined {src d : Database} (hw : src.WF) (hj : d.ViewJoined)
    (ht : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) (hun : d.UnionsJoined src)
    {a b : Term} (h : Cong src a b) : SameClass d a b :=
  have hcov : d.ViewsCover src := Database.ViewsCover.of_viewJoined hj ht
  cong_sameClass
    ⟨fun x y hxy => if hxyeq : x = y then hxyeq ▸ sameClass_self_of_viewsCover hcov hw
        (hxyeq ▸ hxy) else unionsRead_of_viewJoined hj hun x y hxy hxyeq,
     fun _ _ _ => SameClass.trans_of_viewJoined hj,
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
  ctorsOnly := by
    intro c hc
    simp only [litBuildProgram, List.mem_singleton] at hc
    subst hc
    trivial
  setLegal := by decide
  noPrim := by simp [litBuildProgram, Program.ctors, Cmd.ctors, Action.ctors, Expr.ctors]
  noAt := by
    simp [litBuildProgram, Program.names, Program.ctors, Cmd.ctors, Action.ctors, Expr.ctors,
      Program.vars, Cmd.vars, Action.vars, Expr.vars, Program.rulesets, Cmd.rulesets]
  queryEncodable := by simp [litBuildProgram, Cmd.QueryEncodable]
  -- No `union`, so the literal it builds is never one.
  noLitUnion := Or.inl (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

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
than two: `Database.ViewsCover` is now `Database.ViewJoined` plus `reads`
(`Database.ViewsCover.of_viewJoined`), so this residue and `execM_viewJoined` between
them are the whole forward half.

**What it was blamed on before, and what that turned out to be.** `FDatabase.IndexCurrent`
(`Proofs/Merge.lean`, refuted by `cxTgt_not_indexCurrent`) and the run-wide index argument that
would replace it are about the row a *rebuild* displaced. They are real, and they are not this:
here the row was never written, at any state, by any block. That argument is
`execM_viewJoined`'s, and this residue does not share it — a target firing is a `rows`
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
  have hstate' : sd'.CtorState := hstep.ctorState hinv.state (hQ.ctorsOnly c hc)
  obtain ⟨td', hblock, hafter⟩ := FDatabase.execProgramM_append hrun
  have hmono : ∀ t ∈ td'.terms, t ∈ D.terms := FDatabase.execProgramM_terms hafter
  refine ⟨td', hblock, ?_⟩
  cases c with
  | decl f dc =>
      obtain ⟨heqs, henv⟩ := cmdStep_decl_fields hinv.state.sig (hQ.ctorsOnly _ hc) hstep
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

/-- **And the same state's rows, exactly.** `FDatabase.RowsClosed` is the other conjunct of the
`sameData` test `runSaturateM` returned from, and it says a further round of `R` here leaves
the row list *equal* — so any row a rebuild firing would add is one the same round's merge
phase would then delete. Located at the same place and by the same argument as
`roundClosed_of_execProgramM`. -/
theorem rowsClosed_of_execProgramM {R : RulesetName} {d D : FDatabase} {p : Program}
    (h : d.execProgramM (p ++ [Cmd.saturate R]) = some D) : D.RowsClosed R := by
  obtain ⟨td, -, hlast⟩ := FDatabase.execProgramM_append h
  rw [FDatabase.execProgramM] at hlast
  obtain ⟨e, he, he'⟩ := Option.bind_eq_some_iff.mp hlast
  obtain rfl : e = D := by
    rw [FDatabase.execProgramM, Option.some.injEq] at he'; exact he'
  exact FDatabase.runSaturateM_rowsClosed he

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

set_option maxRecDepth 100000 in
/-- The survivor is a row and not merely the unique candidate `cxTgt_rows_view` names. -/
theorem cxTgt_mem_row_view :
    (⟨viewName "B", [], [cxA, cxTransFiat]⟩ : Row) ∈ cxTgt.rows := by decide

/-- **And the union-find weakening of it survives, at the very state that refutes it.**

Three facts at one instance: the entry term is read (`cxTgt_out_view`), **no** row carries its
value columns any more — which is `FDatabase.IndexCurrent` failing here — and the row the merge
kept instead sits at `(A)`, which is the `@UF` parent of the displaced entry's e-class column
`(B)`. So "every merge-function entry term has a current row whose e-class column is
`@UF`-reachable from its own" is not refuted by this counterexample, and it is what
`execM_rebuildClosed` is left waiting on. `mergeResult` keeping `ordering-min` and `mergeBody`
writing `@UF (ordering-max) ↦ (ordering-min, …)` are the two halves of why: the survivor is the
smaller e-class and the larger one gets the edge to it. -/
theorem cxTgt_currentUF :
    cxTgt.toDatabase.Out (viewName "B") [] [cxB, cxFiat] ∧
      (¬ ∃ r ∈ cxTgt.rows, r.fn = viewName "B" ∧ r.out = [cxB, cxFiat]) ∧
      (⟨viewName "B", [], [cxA, cxTransFiat]⟩ : Row) ∈ cxTgt.rows ∧
      cxTgt.toDatabase.UFStep cxB cxA :=
  ⟨cxTgt_out_view,
    fun ⟨r, hr, hfn, hout⟩ => by
      rw [cxTgt_rows_view r hr hfn] at hout
      exact absurd hout (by decide),
    cxTgt_mem_row_view, ⟨cxFiat, cxTgt_out_uf⟩⟩

/-! ##### And the clause the weakening drops, refuted

`Database.RebuildClosedStrong`'s `eclass` reads an `@UF` **entry** and asks for absorption
along *that* edge. The state below refutes it, at the interpreter's own writers and the
encoding's own declarations, and it is the reason `Database.RebuildClosed` asks for a common
`Database.Lands` instead.

**Two `union`s in one block, sharing their `ordering-max` endpoint.** `(A)`, `(B)` and `(C)`
are ordered by `Term.blt` in that order, so `(union (C) (B))` writes `@UF((C)) ↦ ((B), @Fiat)`
and `(union (C) (A))` writes `@UF((C)) ↦ ((A), @Fiat)`, and the block's own merge phase — not a
later one — collides them at the key `((C))`. `mergeResult` keeps `ordering-min = (A)` and
`mergeBody` writes `@UF((B)) ↦ ((A), …)`, so the edge `(C) → (B)` is **superseded before any
rebuild ever ran on it**: its row is gone and no `@CView` entry is keyed at `(B)`. `terms`
keeps the entry term, so `Database.UFStep (C) (B)` still holds and `Database.Absorbs (C) (B)`
cannot.

The e-class rebuild rule's own firing is written in as the fourth `set`, exactly as `cxPre`
writes it, so the state is past the rebuild and not before it — which is what makes the
refutation about *staleness* and not about a firing that has yet to happen
(`uTgt_not_rebuildClosed` is that one). -/

/-- A third e-class, above both, and the one the two `union`s share. -/
def cxC : Term := .app "C" []

/-- `cxSig` with a nullary `C`'s table triple added. -/
def cxSig3 : Signature :=
  Function.update (Function.update (Function.update cxSig
    "C" (some (skolemDecl 0))) (viewName "C") (some (viewDecl 0)))
    (termName "C") (some (termDecl 0))

/-- The state the prelude leaves. -/
def cxBase3 : FDatabase := { FDatabase.empty with sig := cxSig3 }

/-- The four `set`s: `(C)`'s own view entry, the two `union`s, and the entry the e-class
rebuild rule re-keys onto the leader. -/
def cxStalePre : FDatabase :=
  (((cxBase3.addRow (viewName "C") [] [cxC, cxFiat]).addRow ufName [cxC] [cxB, cxFiat]).addRow
    ufName [cxC] [cxA, cxFiat]).addRow (viewName "C") [] [cxA, cxTransFiat]

/-- And the merge phase that resolves both collisions. -/
def cxStale : FDatabase := cxStalePre.mergeRound

/-- `@Trans (@Sym @Fiat) @Fiat`, the justification `mergeBody` composes for its own edge. -/
def cxSTF : Term := .app transName [.app symName [cxFiat], cxFiat]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
theorem cxStale_subtermClosed : cxStale.SubtermClosed :=
  (FDatabase.subtermClosedB_iff cxStale).mp (by decide)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
theorem cxStale_eqsRefl : cxStale.EqsRefl := (FDatabase.eqsReflB_iff cxStale).mp (by decide)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
theorem cxStale_mem_C : cxC ∈ cxStale.terms := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
theorem cxStale_mem_B : cxB ∈ cxStale.terms := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
/-- **The superseded edge, still an entry term.** -/
theorem cxStale_mem_uf_CB : Term.app ufName ([cxC] ++ [cxB, cxFiat]) ∈ cxStale.terms := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
/-- The edge that survived it, at the same key. -/
theorem cxStale_mem_uf_CA : Term.app ufName ([cxC] ++ [cxA, cxFiat]) ∈ cxStale.terms := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
/-- And the edge `mergeBody` wrote between the two displaced e-class columns. -/
theorem cxStale_mem_uf_BA : Term.app ufName ([cxB] ++ [cxA, cxSTF]) ∈ cxStale.terms := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- The kernel runs the merge phase here. `unseal` is what lets `closureF`'s `Finset`
-- membership reduce at all, and the four `set`s' collisions are what then exceed the default.
unseal Egglog.closure in
/-- **`(C)`'s two ids are `(A)` and `(C)` — and `(B)` is not one of them.** The reading is
`viewReprsF`, which `mem_viewReprsF_iff` proves decides `ViewRepr`. -/
theorem cxStale_viewReprs_C : viewReprsF cxStale cxC = [cxA, cxC] := by decide

@[inherit_doc cxStale_mem_uf_CB]
theorem cxStale_out_uf_CB : cxStale.toDatabase.Out ufName [cxC] [cxB, cxFiat] :=
  ⟨[cxC], CongList.refl (by
      intro a ha
      obtain rfl : a = cxC := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact cxStale_mem_C),
    by rw [FDatabase.toDatabase_terms]; exact cxStale_mem_uf_CB⟩

@[inherit_doc cxStale_mem_uf_CA]
theorem cxStale_out_uf_CA : cxStale.toDatabase.Out ufName [cxC] [cxA, cxFiat] :=
  ⟨[cxC], CongList.refl (by
      intro a ha
      obtain rfl : a = cxC := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact cxStale_mem_C),
    by rw [FDatabase.toDatabase_terms]; exact cxStale_mem_uf_CA⟩

@[inherit_doc cxStale_mem_uf_BA]
theorem cxStale_out_uf_BA : cxStale.toDatabase.Out ufName [cxB] [cxA, cxSTF] :=
  ⟨[cxB], CongList.refl (by
      intro a ha
      obtain rfl : a = cxB := by simpa using ha
      rw [FDatabase.toDatabase_terms]; exact cxStale_mem_B),
    by rw [FDatabase.toDatabase_terms]; exact cxStale_mem_uf_BA⟩

@[inherit_doc cxStale_viewReprs_C]
theorem cxStale_viewRepr_C_C : ViewRepr cxStale.toDatabase cxC cxC :=
  viewRepr_of_mem_viewReprsF cxStale_subtermClosed cxC cxC (by
    rw [cxStale_viewReprs_C]; simp)

@[inherit_doc cxStale_viewReprs_C]
theorem cxStale_viewRepr_C_A : ViewRepr cxStale.toDatabase cxC cxA :=
  viewRepr_of_mem_viewReprsF cxStale_subtermClosed cxC cxA (by
    rw [cxStale_viewReprs_C]; simp)

/-- **`(C)` does not read to `(B)`**: the rebuild never ran while `(C) → (B)` was a row, so no
`@CView` entry carries `(B)` in its e-class column. -/
theorem cxStale_not_viewRepr_C_B : ¬ ViewRepr cxStale.toDatabase cxC cxB := by
  intro h
  have hm := mem_viewReprsF_of_viewRepr cxStale_eqsRefl h
  rw [cxStale_viewReprs_C] at hm
  exact absurd hm (by decide)

/-- **So absorption along the superseded edge fails**, at the one term that reads its near
end. -/
theorem cxStale_not_absorbs_CB : ¬ cxStale.toDatabase.Absorbs cxC cxB :=
  fun h => cxStale_not_viewRepr_C_B (h cxC cxStale_viewRepr_C_C)

/-- **And `Database.RebuildClosedStrong` is false at a state the interpreter's own writers
build.** This is the counterexample the weakening is for, and it is the same kind of evidence
`cxTgt_not_indexCurrent` is: not a proof that did not go through, but a clause that a
two-`union` block refutes. -/
theorem cxStale_not_rebuildClosedStrong : ¬ cxStale.toDatabase.RebuildClosedStrong :=
  fun h => cxStale_not_absorbs_CB (h.1 cxC cxB ⟨cxFiat, cxStale_out_uf_CB⟩)

/-- **And the weakened clause survives at that very edge.** `Database.RebuildClosed.eclass`
asks the superseded edge's two ends for a common `Database.Lands`, and `(A)` is one: the
union-find reaches it from `(C)` along the row the collision kept and from `(B)` along the row
`mergeBody` wrote, and `(C)` — the only term that reads either end — reads it. That is the
landing site "current up to the union-find" delivers and the far end of a superseded edge does
not. -/
theorem cxStale_lands_CA :
    cxStale.toDatabase.UFStep cxC cxB ∧ ¬ cxStale.toDatabase.Absorbs cxC cxB ∧
      cxStale.toDatabase.UFReach cxC cxA ∧ cxStale.toDatabase.UFReach cxB cxA ∧
      ViewRepr cxStale.toDatabase cxC cxA :=
  ⟨⟨cxFiat, cxStale_out_uf_CB⟩, cxStale_not_absorbs_CB,
    Database.UFStep.toReach ⟨cxFiat, cxStale_out_uf_CA⟩,
    Database.UFStep.toReach ⟨cxSTF, cxStale_out_uf_BA⟩, cxStale_viewRepr_C_A⟩

/-! ##### What restores it, and what that costs

**The row the merge kept is not arbitrary.** It carries the `@UF` *parent* of the e-class
column the displaced row carried — `mergeBody` writes `@UF (ordering-max) ↦ (ordering-min, …)`
and `mergeResult` keeps `ordering-min`, so the survivor sits at the smaller class and the
larger one gets an edge to it. `cxTgt_rows_view` is the survivor here and `cxTgt_out_uf` is
the edge — written by the `union` and written again by `mergeBody`. So the repaired invariant
is *current up to the union-find*: for every merge-function entry term there is a row at a
congruent key whose e-class column is `@UF`-reachable from the entry's.

**What the landing-site weakening changed.** The clause is no longer handed an edge and asked
to absorb *along it*. `Database.RebuildClosed.eclass` asks the edge's two ends for a common
`Database.Lands`, so a superseded edge is answered by the point both ends still reach, and
`cxStale_lands_CA` is that at the state `cxStale_not_rebuildClosedStrong` refutes the strong
clause at. What the weakening cannot do on its own is produce the landing site: absorption's
conclusion is a `Database.Out`, an entry, and the only thing that writes one is a firing, whose
premise is a **row**. So the three obligations below are what the residue now is, and none of
them is a weakening away.

* **The bridge**, run-wide: every merge-function entry term has a current row at a congruent
  key whose e-class column the union-find reaches from its own. `cxTgt_currentUF` is a compiled
  instance and `mergeOneOriented_survivorUF` is the one writer that could break it, verified;
  every other writer only adds, so it is a per-command induction and not a new mechanism.
* **The fixpoint's roots.** `FDatabase.RowsClosed` pins a rebuild fixpoint's row list *equal*
  to the round's, so a surviving view row whose e-class column still had an outgoing `@UF` row
  would be displaced by the e-class rule's own firing and the list would move. That is one step
  and not a chain induction, and what it spends is a `matchQuery` completeness lemma of
  `cxRb_mem_matchQuery`'s shape together with `mergeResult`'s `ordering-min`.
* **The `@UF` rows are a forest.** `ufDecl`'s `identityVals := some 1` makes two rows at one
  key agree in their e-class column at a merge fixpoint, and every edge a `union` or
  `mergeBody` writes runs `ordering-max ↦ ordering-min`, so a row path strictly descends
  `Term.blt` inside a finite list. That is what makes the root of the first bullet's chain
  *unique*, and so makes the landing site the same for every reader — which is the step the
  leader form of the clause had no way to take.

The third bullet's own argument is proved — `FDatabase.exists_ufRowRoot` for the root and
`ufRowRoot_unique` for its uniqueness, from `FDatabase.UFRowsDescend` and
`FDatabase.UFRowsForest` — and so is the fixpoint mechanism the second and the first both
spend, at the views: `FDatabase.row_unique_of_settled`. `execM_rebuildClosed`'s docstring says
what each of the three is still waiting on.

**And it would not close `unionsJoined_fire`, because nothing about currency would.** The next
section is the counterexample the induction's old invariant died on: the row a firing needs was
never written at any state, so no statement about which rows are *current* reaches it. The
run-wide argument is what `execM_rebuildClosed` still wants — its `column` clause as much as
its `eclass` one, since `Database.ViewsCover` is derived from those
(`Database.RebuildClosed.toViewJoined`, `Database.ViewsCover.of_viewJoined`) — and it is not
what the command induction wants.

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

private theorem ncRule_queryEncodable : (Cmd.rule ncRule).QueryEncodable := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain rfl : p = Pattern.expr (.app "F" [.var "x"]) := by simpa [ncRule] using hp
    refine ⟨?_, trivial⟩
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
    intro c hc
    simp only [ncProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.CtorDecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [ncProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact ncRule_queryEncodable
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inr (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

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
  (exec_programStep ncProgram_encodeDomain.ctorsOnly
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

/-- **Two ids of one term have the same representative here.** The second clause of
`ncTgt_viewLeaderRows`, extracted because `ncTgt_rebuildClosed` wants it at the *named*
`ncLead` and the bundle only offers it at an opaque one. -/
private theorem ncTgt_lead_uniq (t e₁ e₂ : Term) (h₁ : ViewRepr ncTgt.toDatabase t e₁)
    (h₂ : ViewRepr ncTgt.toDatabase t e₂) : ncLead e₁ = ncLead e₂ := by
  cases t with
  | lit l => rw [h₁.eq_of_lit, h₂.eq_of_lit]
  | app g bs =>
      rcases ncTgt_viewRepr_cases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, -, (rfl | rfl)⟩ | ⟨rfl, rfl⟩ <;>
          rcases ncTgt_viewRepr_cases h₂ with ⟨h', rfl⟩ | ⟨h', -, (rfl | rfl)⟩ | ⟨h', rfl⟩ <;>
        simp_all [ncLead, ncA, ncB, ncFA]

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
  · exact ncTgt_lead_uniq
  · intro x y pf ho
    obtain ⟨rfl, rfl⟩ := ncTgt_out_uf_cases ho
    rw [ncLead_ncB, ncLead_of_ne (by simp [ncA, ncB])]
  · intro f es e pf ho
    refine ⟨e, pf, ?_⟩
    rcases ncTgt_out_view ho with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;>
      simpa [ncLead, ncA, ncB] using ho

/-- **And so does `Database.ViewJoined`**, out of the reduction. `rowShared` is the clause with
positive arity here — `@FView` is keyed at `((A))` — and `ids` is asked at `(B)`, the one term
with two ids; `ncTgt_rowShared_FB_FA` is `rowShared` at an instance with two *distinct*
argument lists, which is where `Database.ViewsProduct` failed. -/
theorem ncTgt_viewJoined : ncTgt.toDatabase.ViewJoined :=
  ncTgt_viewLeaderRows.toViewJoined

/-- **And `Database.RebuildClosedStrong` too, at the state with a positive-arity key**, with
`Database.RebuildClosed.of_strong` carrying it to the residue's own form.

`eclass` at the `union`'s own edge, `edged` at `(B)`'s two ids — `ncTgt_lead_uniq` says the two
have one representative, and `(B)` reaches it in one edge — and `column` asked at `@FView`'s key
`((A))`, where it is answered by the row already in hand: `(A)` is the leader, so no `@UF` entry
leaves it and the only tuple `Database.UFReach` reaches from `((A))` is `((A))` itself. That is
the honest reading of the third clause at every state this file builds — a key column that has
to move is a state where the *column* rebuild rules have not run yet, and every state here is
past them. -/
theorem ncTgt_rebuildClosedStrong : ncTgt.toDatabase.RebuildClosedStrong := by
  have hBA : ncTgt.toDatabase.UFStep ncB ncA := ⟨ncFiat, ncTgt_out_uf⟩
  have hnoA : ∀ b, ¬ ncTgt.toDatabase.UFStep ncA b := by
    rintro b ⟨pf, ho⟩
    exact absurd (ncTgt_out_uf_cases ho).1 (by simp [ncA, ncB])
  have hfixA : ∀ x, ncTgt.toDatabase.UFReach ncA x → x = ncA := by
    intro x hx
    induction hx with
    | refl => rfl
    | tail _ hs ih => exact absurd (ih ▸ hs) (hnoA _)
  have hlead : ∀ e : Term, ncTgt.toDatabase.UFReach e (ncLead e) := by
    intro e
    by_cases h : e = ncB
    · subst h; rw [ncLead_ncB]; exact hBA.toReach
    · rw [ncLead_of_ne h]; exact .refl
  refine ⟨?_, ?_, ?_⟩
  · rintro a b ⟨pf, ho⟩
    obtain ⟨rfl, rfl⟩ := ncTgt_out_uf_cases ho
    intro t ht
    cases t with
    | lit l => exact absurd ht.eq_of_lit (by simp [ncB])
    | app g bs =>
        rcases ncTgt_viewRepr_cases ht with ⟨-, h'⟩ | ⟨rfl, rfl, -⟩ | ⟨-, h'⟩
        · exact absurd h' (by simp [ncA, ncB])
        · exact ncTgt_viewRepr_B_A
        · exact absurd h' (by simp [ncB, ncFA])
  · exact fun t e₁ e₂ h₁ h₂ =>
      ⟨ncLead e₁, hlead e₁, (ncTgt_lead_uniq t e₂ e₁ h₂ h₁) ▸ hlead e₂⟩
  · intro f es ds e pf ho hl
    rcases ncTgt_out_view ho with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · cases hl; exact ⟨e, pf, ho⟩
    · cases hl; exact ⟨e, pf, ho⟩
    · cases hl with
      | cons hx hrest =>
          cases hrest
          obtain rfl := hfixA _ hx
          exact ⟨e, pf, ho⟩

@[inherit_doc ncTgt_rebuildClosedStrong]
theorem ncTgt_rebuildClosed : ncTgt.toDatabase.RebuildClosed :=
  Database.RebuildClosed.of_strong ncTgt_rebuildClosedStrong

/-- **`Database.ViewJoined.rowShared` at a positive-arity key, non-vacuously**: the row is
`@FView((A)) ↦ ((F (A)), @Fiat)`, the list that read its key is `((A))` and the list handed in
is `((B))` — a *different* list, in one class with it through the `union` — and the tuple the
clause answers with carries the row. Every hypothesis is inhabited and the conclusion is a real
row, which is what says the weakened clause is not vacuous at the state whose non-leader firing
refutes `Database.ViewsProduct`. -/
theorem ncTgt_rowShared_FB_FA :
    ViewReprList ncTgt.toDatabase [ncA] [ncA] ∧
      ncTgt.toDatabase.Out (viewName "F") [ncA] [ncFA, ncFiat] ∧
      List.Forall₂ (SameClass ncTgt.toDatabase) [ncA] [ncB] ∧ [ncA] ≠ [ncB] ∧
      ∃ es' e' pf', ViewReprList ncTgt.toDatabase [ncA] es' ∧
        ViewReprList ncTgt.toDatabase [ncB] es' ∧
          ncTgt.toDatabase.Out (viewName "F") es' [e', pf'] :=
  ⟨.cons ncTgt_viewRepr_A .nil, ncTgt_out_fview,
   .cons ⟨ncA, ncTgt_viewRepr_A, ncTgt_viewRepr_B_A⟩ .nil, by simp [ncA, ncB],
   ncTgt_viewJoined.rowShared "F" [ncA] [ncB] [ncA] ncFA ncFiat
     (.cons ncTgt_viewRepr_A .nil) ncTgt_out_fview
     (.cons ⟨ncA, ncTgt_viewRepr_A, ncTgt_viewRepr_B_A⟩ .nil)⟩

/-- **`Database.ViewJoined.ids` at the one term with two ids**, and both of them real: `(B)`'s
own build entry, which the collision displaced but did not delete, and the leader's, which the
e-class rebuild rule wrote. The absorber is `(A)`. -/
theorem ncTgt_ids_B :
    ViewRepr ncTgt.toDatabase ncB ncB ∧ ViewRepr ncTgt.toDatabase ncB ncA ∧ ncB ≠ ncA ∧
      ∃ e, ncTgt.toDatabase.Absorbs ncB e ∧ ncTgt.toDatabase.Absorbs ncA e :=
  ⟨ncTgt_viewRepr_B, ncTgt_viewRepr_B_A, by simp [ncA, ncB],
   ncTgt_viewJoined.ids ncB ncB ncA ncTgt_viewRepr_B ncTgt_viewRepr_B_A⟩

/-! ##### And the strong form is strictly stronger

`Database.ViewsProduct` and `Database.ReadsSelf` were kept because a state an encoded program
reaches **refutes** them, which is what said the weakening had to happen.
`Database.ViewLeaderRows` is not in that position — nothing refutes it at an `execM` target, and
`ncTgt_viewLeaderRows` is it holding at the hardest state this file has. So the evidence that it
is over-strong has to be of the other kind: a database at which the *weak* form holds and the
strong one **fails**, which is what says `Database.ViewJoined` is a genuine weakening and not a
re-spelling.

The separation is exactly the choice function. `Database.ViewJoined.ids` asks two ids of one
term for an upper bound in `Database.Absorbs`; `Database.ViewLeader` asks for one id that is
`lead` of *every* id any term co-reads with it, and an ascending chain with no top has upper
bounds everywhere and no such representative. `chainD` is that chain — not a state a program
reaches, and it is not offered as one: it separates the two properties, which is a statement
about the two definitions and not about the encoding. -/

/-- An injective family of function names: `n` copies of `'a'`. -/
def chainName (n : Nat) : FnName := String.ofList (List.replicate n 'a')

@[inherit_doc chainName]
theorem chainName_inj {n m : Nat} (h : chainName n = chainName m) : n = m := by
  have h2 := congrArg String.toList h
  rw [chainName, chainName, String.toList_ofList, String.toList_ofList] at h2
  simpa using congrArg List.length h2

/-- The proof column every row of `chainD` carries. -/
def chainPf : Term := .app "pf" []

/-- The `n`-th term: a nullary constructor, so its view key is empty and `rowShared` has
nothing to move. -/
def chainT (n : Nat) : Term := .app (chainName n) []

/-- The `n`-th id. A **positive-arity** application, so it is neither a `chainT` nor a literal:
a literal is an id of itself (`ViewRepr.lit`), and that alone would refute every absorption
below. -/
def chainId (n : Nat) : Term := .app (chainName n) [chainPf]

@[inherit_doc chainId]
theorem chainId_inj {n m : Nat} (h : chainId n = chainId m) : n = m := by
  rw [chainId, chainId, Term.app.injEq] at h
  exact chainName_inj h.1

/-- **The chain**: `chainT n`'s view carries `chainId j` for every `j ≥ n`, so a term's set of
ids is an up-set and the up-sets shrink as `n` grows. Nothing else is a term — no `@UF` row, no
positive-arity key. -/
def chainS : Set Term :=
  {t | ∃ n j, n ≤ j ∧ t = Term.app (viewName (chainName n)) [chainId j, chainPf]}

/-- The database those rows make, with nothing else in it: the diagonal of `chainS` as its
equations, so `Cong` is equality and `Database.Out` reads `chainS` directly. -/
def chainD : Database where
  sig := fun _ => none
  eqs := {p | p.1 = p.2 ∧ p.1 ∈ chainS}
  env := []
  rules := ∅

theorem chainD_diag : chainD.Diag := fun _ hp => hp.1

private theorem chainD_cong_mem {a b : Term} (h : Cong chainD a b) :
    a ∈ chainS ∧ b ∈ chainS := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | @assert a' b' hab =>
      have heq : a' = b' := hab.1
      have hm : a' ∈ chainS := hab.2
      exact ⟨hm, by rw [← heq]; exact hm⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | congr _ _ _ iha ihb _ => exact ⟨iha.1, ihb.1⟩
  | nil => trivial
  | cons _ _ _ _ => trivial

/-- `chainD` holds exactly `chainS`: `Cong.assert` one way, and the induction above the
other. -/
theorem chainD_mem_terms {t : Term} : t ∈ chainD.terms ↔ t ∈ chainS :=
  ⟨fun h => (chainD_cong_mem h).1, fun h => Cong.assert ⟨rfl, h⟩⟩

private theorem chainD_congList_eq : ∀ {as bs : List Term}, CongList chainD as bs → as = bs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab hl => by
      rw [Cong.eq_of_diag chainD_diag hab, chainD_congList_eq hl]

private theorem chainD_out {f : FnName} {as vs : List Term} (h : chainD.Out f as vs) :
    Term.app f (as ++ vs) ∈ chainS := by
  obtain ⟨bs, hcl, hmem⟩ := h
  obtain rfl : as = bs := chainD_congList_eq hcl
  exact chainD_mem_terms.mp hmem

/-- **What reads what at `chainD`**: only a nullary `chainT`, and only the ids above it. -/
private theorem chainD_viewRepr_cases {g : FnName} {bs : List Term} {e : Term}
    (h : ViewRepr chainD (.app g bs) e) :
    ∃ n j, n ≤ j ∧ g = chainName n ∧ bs = [] ∧ e = chainId j := by
  match h with
  | @ViewRepr.app _ f as es e pf hes ho =>
    obtain ⟨n, j, hnj, heq⟩ := chainD_out ho
    rw [Term.app.injEq] at heq
    obtain rfl : f = chainName n := viewName_inj heq.1
    obtain rfl : es = [] := by
      have hl := congrArg List.length heq.2
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : as = [] := by cases hes with | nil => rfl
    exact ⟨n, j, hnj, rfl, rfl, (show e = chainId j ∧ pf = chainPf by simpa using heq.2).1⟩

@[inherit_doc chainD_viewRepr_cases]
private theorem chainD_viewRepr_chainT {k : Nat} {e : Term}
    (h : ViewRepr chainD (chainT k) e) : ∃ j, k ≤ j ∧ e = chainId j := by
  rw [chainT] at h
  obtain ⟨n, j, hnj, hg, -, he⟩ := chainD_viewRepr_cases h
  obtain rfl : k = n := chainName_inj hg
  exact ⟨j, hnj, he⟩

@[inherit_doc chainD_viewRepr_cases]
theorem chainD_viewRepr_of_le {n j : Nat} (h : n ≤ j) : ViewRepr chainD (chainT n) (chainId j) :=
  .app .nil ⟨[], .nil, chainD_mem_terms.mpr ⟨n, j, h, rfl⟩⟩

/-- **Absorption at `chainD` is `≤`**: everything that reads `chainId i` reads `chainId m`
whenever `i ≤ m`, because the terms reading `chainId i` are the `chainT n` with `n ≤ i` and
their id sets are up-sets. -/
theorem chainD_absorbs {i m : Nat} (h : i ≤ m) : chainD.Absorbs (chainId i) (chainId m) := by
  intro t ht
  cases t with
  | lit l => exact absurd ht.eq_of_lit (by simp [chainId])
  | app g bs =>
      obtain ⟨n, j, hnj, rfl, rfl, hej⟩ := chainD_viewRepr_cases ht
      obtain rfl : i = j := chainId_inj hej
      exact chainD_viewRepr_of_le (hnj.trans h)

/-- **`Database.ViewJoined` holds at `chainD`**, and `ids` is the clause doing the work: a term
here has *infinitely* many ids and any two of them have an upper bound, which is the larger.
`ufJoin` and `rowShared` are vacuous and degenerate respectively — no `@UF` row exists and every
key is empty — which is the point: the separation is about `ids` alone. -/
theorem chainD_viewJoined : chainD.ViewJoined where
  ids t e₁ e₂ h₁ h₂ := by
    cases t with
    | lit l =>
        rw [h₁.eq_of_lit, h₂.eq_of_lit]
        exact ⟨.lit l, Database.Absorbs.refl _ _, Database.Absorbs.refl _ _⟩
    | app g bs =>
        obtain ⟨n₁, j₁, -, -, -, rfl⟩ := chainD_viewRepr_cases h₁
        obtain ⟨n₂, j₂, -, -, -, rfl⟩ := chainD_viewRepr_cases h₂
        exact ⟨chainId (max j₁ j₂), chainD_absorbs (Nat.le_max_left _ _),
          chainD_absorbs (Nat.le_max_right _ _)⟩
  ufJoin x y pf ho := by
    obtain ⟨n, j, -, heq⟩ := chainD_out ho
    rw [Term.app.injEq] at heq
    exact absurd heq.1.symm viewName_ne_ufName
  rowShared f as bs es e pf hes ho hl := by
    obtain ⟨n, j, -, heq⟩ := chainD_out ho
    rw [Term.app.injEq] at heq
    obtain rfl : es = [] := by
      have hl' := congrArg List.length heq.2
      simp only [List.length_append, List.length_cons, List.length_nil] at hl'
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : as = [] := by cases hes with | nil => rfl
    obtain rfl : bs = [] := by cases hl with | nil => rfl
    exact ⟨[], e, pf, .nil, .nil, ho⟩

/-- **And `Database.ViewLeader` fails there.** `chainT 0` reads every id, so `huniq` makes
`lead` constant on the whole family; `hmem` at `chainT 0` puts that constant at some `chainId m`;
and `hmem` at `chainT (m+1)`, which reads only ids above `m`, then asks for `m + 1 ≤ m`.

So the choice function is what `Database.ViewLeaderRows` asks for over and above what its three
consumers spend, and `pathCompressRule` — carried in the residue solely to supply it — is what
`execM_viewJoined` no longer needs. -/
theorem chainD_not_viewLeader : ¬ chainD.ViewLeader := by
  rintro ⟨lead, hmem, huniq, -⟩
  have h0 : ViewRepr chainD (chainT 0) (chainId 0) := chainD_viewRepr_of_le (Nat.le_refl 0)
  obtain ⟨m, -, hLm⟩ := chainD_viewRepr_chainT (hmem _ _ h0)
  have hup : ViewRepr chainD (chainT 0) (chainId (m + 1)) :=
    chainD_viewRepr_of_le (Nat.zero_le _)
  have huq : lead (chainId (m + 1)) = lead (chainId 0) :=
    huniq (chainT 0) (chainId (m + 1)) (chainId 0) hup h0
  have hnext : ViewRepr chainD (chainT (m + 1)) (lead (chainId (m + 1))) :=
    hmem _ _ (chainD_viewRepr_of_le (Nat.le_refl _))
  rw [huq, hLm] at hnext
  obtain ⟨j, hj, hej⟩ := chainD_viewRepr_chainT hnext
  obtain rfl : m = j := chainId_inj hej
  omega

@[inherit_doc chainD_not_viewLeader]
theorem chainD_not_viewLeaderRows : ¬ chainD.ViewLeaderRows :=
  fun h => chainD_not_viewLeader h.toViewLeader

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
case, and of the *key* half of obligation `congr`, at the rules it is waiting on. Not
proved.**

`Database.RebuildClosed` is `Database.ViewJoined` restated per *mechanism* instead of per
consumer — `eclass` the e-class rebuild rule, `column` the column rules, `edged` the `@UF`
edge `mergeBody` writes between two entries that collide at one view key — and
`Database.RebuildClosed.toViewJoined` is the reduction. Stating the residue here rather than
at the clauses is what lets the questions below be asked separately, because all three
clauses turn out to want the same one thing.

**The clause that asked for absorption along the edge is false, and `cxStale` is why.** Two
`union`s in one block that share their `ordering-max` endpoint collide in that block's *own*
merge phase, so the edge the collision displaces was never a row at any rebuild:
`cxStale_not_absorbs_CB` is `(C)` reading its own build entry and not reading `(B)`, and
`cxStale_not_rebuildClosedStrong` is `Database.RebuildClosedStrong` failing on it. So the
clause is stated at a common `Database.Lands` — the point both ends still reach and that
absorbs both — which is what `Database.ViewJoined.ufJoin` consumes and what `cxStale_lands_CA`
exhibits at the refuting state.

**What the weakening does not do is produce the landing site.** Absorption's conclusion is a
`Database.Out`, an entry, and the only thing that writes one is a firing, whose premise is a
**row**. So what the residue reduces to is three obligations, in this order:

* **The bridge**, run-wide: every merge-function entry term has a current row at a key
  congruent to its own whose e-class column is `@UF`-reachable from the entry's.
  `FDatabase.IndexCurrent` is that claim without the "up to `@UF`", and `cxTgt_not_indexCurrent`
  refutes it; the weakened claim survives that very state, and `cxTgt_currentUF` is the compiled
  instance — the row the merge kept sits at the `@UF` parent of the entry it displaced.
* **The fixpoint's roots**: at a `FDatabase.RowsClosed` state no surviving view row's e-class
  column has an outgoing `@UF` row, since the e-class rule's own firing would displace it and
  the row list would move. One step, and what it spends is a `matchQuery` completeness lemma of
  `cxRb_mem_matchQuery`'s shape together with `mergeResult`'s `ordering-min`.
* **The `@UF` rows are a forest**, so that root is *unique* and every reader of an id therefore
  lands on the same one. `ufDecl`'s `identityVals := some 1` makes two rows at one key agree in
  their e-class column at a merge fixpoint, and every edge a `union` or `mergeBody` writes runs
  `ordering-max ↦ ordering-min`, so a row path strictly descends `Term.blt` inside a finite
  list.

The third is what the leader form of the clause had no way to reach and the landing-site form
does: two terms reading one id are two rows displaced independently, but at a fixpoint over a
forest both displacements end at the same root, and that root is a `Database.Lands` of the id.

**The third obligation's own argument is proved, and so is the fixpoint mechanism the second
and the first both spend.** Two blocks below, at the merge phase:

* `FDatabase.exists_ufRowRoot` and `ufRowRoot_unique` are the forest: descent along
  `FDatabase.UFRowEdge` bounds a path by the `@UF` rows below its start and `rows` is a finite
  list, so a root exists; one outgoing edge per key makes it unique. Both hypotheses —
  `FDatabase.UFRowsDescend` and `FDatabase.UFRowsForest` — are named properties of a state and
  are what is left of the third obligation: descent is a run-wide induction over the three
  writers of an `@UF` row, and the forest clause is the fixpoint argument at `@UF`'s own table.
* `FDatabase.row_unique_of_settled` is that fixpoint argument, at the **views**: a
  `FDatabase.settled` state carries at most one row per view key, because
  `FDatabase.mergeOneOriented` deletes the arriving row of a collision whether or not the body
  runs, no firing anywhere adds a row at a view key, and `rebuild_diag` says the pass fires on
  the rows it started with. This is what identifies the two rows the bridge produces for two
  entries at **one** key, and what the second obligation contradicts against; it is not yet
  `FDatabase.UFRowsForest`, since `mergeBody` writes into `@UF` and the per-key count is
  therefore no measure there — that one wants the count of view rows first and a
  `FDatabase.UFRowsDescend` rank of the `@UF` key second.

**What the second obligation still needs, precisely.** The e-class rule has to have *fired*,
which is a `matchQuery` completeness lemma — `cxRb_mem_matchQuery` proved at one instance, and
the general form has to name `Query.freeVars`' order, compose `Env.canon` with itself and place
the columns in `FDatabase.valueTerms`. That yields the rule's conclusion; turning it into the
contradiction then wants either a **row** for it, which is the first obligation, or the
merge phase's own survival fact — some row stays at the key and its e-class column is
`blt`-below every column the key carried, which is `mergeResult`'s `ordering-min` carried
across a pass and across `FDatabase.mergeSaturateF`. Neither is one step.

**And a side condition that turned out to be load-bearing rather than bookkeeping**: the merge
body only runs if the signature declares `@Sym` and `@Trans` (`Expr.eval` reads
`Signature.IsCtor`), so a signature that does not leaves every collision standing at what would
otherwise be a fixpoint. `mergeOneWith_isSome_of_collide` carries the two hypotheses; the
prelude's `proofDecls` is what supplies them.

**The merge case of the bridge is discharged, and by construction rather than by luck.**
`FDatabase.mergeOneOriented` is the interpreter's only writer that removes a row, so it is the
only one that can break the claim; `mergeOneOriented_survivorUF` is that step verified, and
`mergeOneWith_survivorUF` is it at the orientation the pass actually calls. The two selectors
are complementary at one comparison — `mergeResult` keeps `ordering-min old0 new0` and
`mergeBody` writes `@UF (ordering-max old0 new0) ↦ (ordering-min old0 new0, …)` — so the
surviving row's e-class column is `Database.UFReach`-reachable from *both* colliding columns in
the state the firing itself returns: reflexivity on one side, the edge the firing just wrote on
the other. `mergeBody_result_paired` is the complementarity, and it is why no `Term.blt`
survives into the statement. The skip branch is the same fact degenerately, and it is what
`Signature.MergeShape`'s `identityVals = some 1` clause is for: at width one
`FDatabase.noConflict` compares exactly the e-class columns, so a collision runs no body only
when they are **equal**, where a width of zero would skip every collision and drop rows with no
edge behind them.

**And the rest of the bridge is inductive for free**, which is why this was the case worth
checking: every other writer only adds. `FDatabase.addRow` writes the row for the entry term it
mints, so a new entry is current reflexively; `execRunRules` unions firings in and removes
nothing; `FDatabase.union` and `FDatabase.addTerm` touch no row. So the bridge is a per-command
induction whose one hard case is now closed.

**Stating `Database.UFStep` over `FDatabase.rows` instead of over entry terms does not help.**
It would take the staleness out of `eclass`'s *hypothesis* — the clause would range over live
edges only — but `Database.ViewJoined.ufJoin`, which is what the residue exists to answer, is
stated over an `@UF` **entry**, so `Database.RebuildClosed.toViewJoined` would no longer close
and the superseded edge would have to be handled anyway, by the bridge applied to `@UF`'s own
table. What is left after that is the *conclusion* half, which is where the `rows`/`terms` gap
actually bites and which a rows-valued hypothesis does not touch: absorption still has to
produce an entry for a reader that reads through a displaced row. `Database.Lands` absorbs the
stale hypothesis without moving the residue into `FDatabase`, so the entry-valued statement is
kept.

**This is strictly stronger than `Database.ViewJoined`, deliberately, and here is the
separation.** `chainD` satisfies the clauses (`chainD_viewJoined`) with no `@UF` entry at all —
its ids absorb each other by having no other reader — and `edged` fails there, since its
`Database.Lands` carries a `Database.UFReach` no edge can supply. So the residue below asks for
more than its consumer does. What justifies asking for it is that it is what the *rules*
deliver: every id a view entry ever carried at a key is one a `set` wrote, and two `set`s at one
key are a collision, and a collision is an `@UF` edge.

**Non-vacuous, and still failing where it must**: `satTarget_rebuildClosed` is the degenerate
state, `Encoding/Match.lean`'s `uRebuilt_rebuildClosed` the one with a real `@UF` edge — where
`eclass` and `edged` both do work — `ncTgt_rebuildClosed` the one with a positive-arity key in
`column`, and `uTgt_not_rebuildClosed` is the same property one rebuild firing earlier, where it
fails because `uTgt_not_viewJoined` does. All three positive witnesses are proved at
`Database.RebuildClosedStrong` and transported by `Database.RebuildClosed.of_strong`, which is
what says the weakening is a weakening; `cxStale_not_rebuildClosedStrong` is where the two come
apart. -/
theorem execM_rebuildClosed {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.RebuildClosed := by
  sorry

/-- **The residue of obligation `trans`, of the rebuild half of obligation `assert`'s `union`
case, and of the *key* half of obligation `congr`**, through
`Database.RebuildClosed.toViewJoined`.

**Stated at what the three reductions spend, and that is one mechanism fewer than the four
clauses this replaces.** `Database.ViewLeaderRows` asked for a *choice function* `lead`, total
on `Term` and constant across the whole "some term reads both" closure; every consumer used it
only to name one id it then handed to `hmem`. So `Database.ViewJoined` asks for joins instead —
`ids` for `SameClass.trans_of_viewJoined`, `ufJoin` for `unionsRead_of_viewJoined`, `rowShared`
for `Database.ViewsCover.of_viewJoined` — and `pathCompressRule`, which was carried solely to
make `lead` a function rather than a relation, is no longer part of this residue.
`Database.ViewLeaderRows.toViewJoined` is the check that the weakening is a weakening, and it
is where the strong form's four clauses are still spent.

**`ufJoin` is the e-class rule and it is load-bearing after the weakening too**:
`uTgt_not_viewJoined` is this clause failing one rebuild firing early, at the state where
`Database.UnionsRead` fails with it — so the weakening did not weaken into vacuity.

**`rowShared` is the column rules, and only where the key has to move**: obligation `congr`
splits into an id for the source's own term — the command induction's `reads`, whose one open
case is `unionsJoined_fire` — and a row at a tuple both argument lists read, which is this. The
split is `Database.ViewsCover.of_viewJoined`, and the *diagonal* instance — all
`viewRepr_total` spends — is answered by the row already in hand, where the strong form's
`rowLead` demanded the column rules even there.

**The fixpoint is proved and is not enough.** `FDatabase.RoundClosed` gives every term one more
rebuild round would derive, which is the *conclusion* of each of those rules; their *premise* is
a row, and `cxTgt_not_indexCurrent` is the compiled statement that the index need not hold every
entry term `Database.Out` reads. `execM_rebuildClosed` is where what is left is written down,
and it is the same run-wide index argument, now weakened to "up to the union-find" and stated
per rule rather than per clause.

**Non-vacuous at three states, with every clause doing work at one of them**:
`satTarget_viewJoined` (the degenerate one), `Encoding/Match.lean`'s `uRebuilt_viewJoined` (a
real `@UF` edge in `ufJoin`, two ids for one term in `ids`) and `ncTgt_viewJoined` (positive
arity in `rowShared`, at the key the `union` moved) — with `ncTgt_rowShared_FB_FA` and
`ncTgt_ids_B` the two clauses at named instances with every hypothesis inhabited. -/
theorem execM_viewJoined {P : Program} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewJoined :=
  (execM_rebuildClosed hdom htgt).toViewJoined

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

**And that instance generalises, so this is no longer a residue.** The two things needed to
produce a shared tuple are already residues of their own: an id for the source's own term, which
is the command induction's `reads`, and a row at a tuple both argument lists read, which is
`Database.ViewJoined`' `rowShared`. `Database.ViewsCover.of_viewJoined` is the assembly and it
spends nothing else — in particular no run-wide index argument beyond the one `execM_viewJoined`
already carries, and none at all at the diagonal. -/
theorem execM_viewsCover {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewsCover src :=
  Database.ViewsCover.of_viewJoined (execM_viewJoined hdom htgt)
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
clause holds and `Database.ViewJoined.ufJoin` does not — so the two are load-bearing
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
  unionsRead_of_viewJoined (execM_viewJoined hdom htgt) (execM_unionsJoined hdom hsrc htgt)

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

/-- **Obligation `trans`, at the encoding. Proved from `execM_viewJoined`.** Not from the
view's functional dependency, which is false at this file's own witness — the section header
above has the refutation. And not from a union-find *representative* either: what the reduction
spends is a common absorber of the middle term's two ids, which is `Database.ViewJoined.ids`. -/
theorem encode_trans {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (_hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b c : Term) (hab : SameClass tgt.toDatabase a b) (hbc : SameClass tgt.toDatabase b c) :
    SameClass tgt.toDatabase a c :=
  SameClass.trans_of_viewJoined (execM_viewJoined hdom htgt) hab hbc

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

/-! #### The target asserts no equation

`Database.Out` searches the key's *congruence class*, so an invariant about view entries is a
statement about the term list only where the target's `Cong` is the identity. That is
`FDatabase.EqsRefl`, which `sameClassF_iff` takes as a hypothesis and `difftest correspond`
measures as its `tgt-eqs` column; at an `execM` target it is a **theorem**. `encodeAction`
turns a source `union` into a `set` of a `@UF` edge, so no `encode` output contains an
`Action.union` — command, rule head or `:merge` body (`encode_unionFree`) — and
`FDatabase.addEq` is the interpreter's only writer of `eqs`.

`Proofs/Merge.lean` carries `Database.NoUnions` along `Database.Recorded` instead, which costs
`Program.NoSaturate`; every writing command `encodeCmd` emits ends in
`Cmd.saturate rebuildRuleset`, so that route is closed at exactly the programs this file is
about, and what follows is the same fact proved on the interpreter's own components. -/

/-- **A state whose equations, merge bodies and rule heads are all union-free.**
`Database.NoUnions`' three fields, read off an `FDatabase`: the three phases read one
each. -/
structure FDatabase.NoUnions (d : FDatabase) : Prop where
  /-- The state asserts nothing, which is `Database.Diag` in its strongest form. -/
  eqs : d.eqs = []
  /-- No `:merge` body asserts anything, which is what a merge phase runs. -/
  sig : Signature.UnionFree d.sig
  /-- No rule head asserts anything, which is what a round runs. -/
  rules : ∀ r ∈ d.rules, Actions.UnionFree r.actions

/-- `addTerm` writes `terms` and `rows`, and nothing else. -/
theorem FDatabase.addTerm_eqs (t : Term) (d : FDatabase) : (d.addTerm t).eqs = d.eqs := rfl

/-- `addRow` is an `addTerm` and an index write. -/
theorem FDatabase.addRow_eqs (f : FnName) (as vs : List Term) (d : FDatabase) :
    (d.addRow f as vs).eqs = d.eqs := rfl

/-- A round's accumulator takes its signature and rules from the left and its equations from
both. -/
theorem FDatabase.NoUnions.union {d₁ d₂ : FDatabase} (h₁ : d₁.NoUnions) (h₂ : d₂.eqs = []) :
    (d₁.union d₂).NoUnions where
  eqs := by simp [FDatabase.union, h₁.eqs, h₂]
  sig := h₁.sig
  rules := h₁.rules

/-- **One action.** `Action.union` is the only case that reaches `addEq`, and `Action.UnionFree`
is exactly its exclusion. -/
theorem execAction_noUnions {d d' : FDatabase} {a : Action} (hu : a.UnionFree)
    (hn : d.NoUnions) (h : execAction d a = some d') : d'.NoUnions := by
  cases a with
  | expr e =>
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨by rw [FDatabase.addTerm_eqs]; exact hn.eqs, hn.sig, hn.rules⟩
  | letBind v e =>
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨by rw [show ({(d.addTerm t) with env := (v, t) :: d.env} : FDatabase).eqs
        = (d.addTerm t).eqs from rfl, FDatabase.addTerm_eqs]; exact hn.eqs, hn.sig, hn.rules⟩
  | union e₁ e₂ => exact absurd hu (by simp [Action.UnionFree])
  | set f args out =>
      rw [execAction] at h
      obtain ⟨as, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨by rw [FDatabase.addRow_eqs]; exact hn.eqs, hn.sig, hn.rules⟩

@[inherit_doc execAction_noUnions]
theorem execActions_noUnions : ∀ {as : List Action} {d d' : FDatabase},
    Actions.UnionFree as → d.NoUnions → execActions d as = some d' → d'.NoUnions
  | [], _, _, _, hn, h => by rw [execActions, Option.some.injEq] at h; exact h ▸ hn
  | a :: as, _, _, hu, hn, h => by
      rw [execActions] at h
      obtain ⟨e, he, hrest⟩ := Option.bind_eq_some_iff.mp h
      exact execActions_noUnions hu.2 (execAction_noUnions hu.1 hn he) hrest

/-- A rule head runs its block under the match and then restores the environment and the rule
set. -/
theorem execLocalActions_noUnions {d d' : FDatabase} {as : List Action} {σ : Env}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execLocalActions d as σ = some d') :
    d'.NoUnions := by
  rw [execLocalActions] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have := execActions_noUnions hu (show ({d with env := d.env ++ σ} : FDatabase).NoUnions from
    ⟨hn.eqs, hn.sig, hn.rules⟩) he
  exact ⟨this.eqs, this.sig, hn.rules⟩

/-- One firing, unioned into the accumulator. -/
theorem fireInto_noUnions {d acc : FDatabase} {r : Rule} {σ : Env}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) (ha : acc.NoUnions) :
    (fireInto d r acc σ).NoUnions := by
  rw [fireInto]
  cases hf : execLocalActions d r.actions σ with
  | none => exact ha
  | some d' => exact ha.union (execLocalActions_noUnions hu hn hf).eqs

@[inherit_doc fireInto_noUnions]
theorem fireRule_noUnions {d acc : FDatabase} {r : Rule}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) (ha : acc.NoUnions) :
    (fireRule d acc r).NoUnions := by
  rw [fireRule]
  induction matchQuery d r.query generalizing acc with
  | nil => exact ha
  | cons σ σs ih => exact ih (fireInto_noUnions hu hn ha)

/-- The round's fold, with the accumulator generalized; the pre-state the matches are read off
is fixed. -/
theorem foldl_fireRule_noUnions {d : FDatabase} (hn : d.NoUnions) :
    ∀ (rs : List Rule), (∀ r ∈ rs, Actions.UnionFree r.actions) →
      ∀ {acc : FDatabase}, acc.NoUnions → (rs.foldl (fireRule d) acc).NoUnions
  | [], _, _, ha => ha
  | r :: rs, hu, _, ha =>
      foldl_fireRule_noUnions hn rs (fun r' hr' => hu r' (List.mem_cons_of_mem _ hr'))
        (fireRule_noUnions (hu r List.mem_cons_self) hn ha)

/-- **One round.** Every rule of the ruleset is one the state holds, so `rules` covers them. -/
theorem execRunRules_noUnions {R : RulesetName} {d : FDatabase} (hn : d.NoUnions) :
    (execRunRules R d).NoUnions :=
  foldl_fireRule_noUnions hn _ (fun r hr => hn.rules r (List.mem_of_mem_filter hr)) hn

/-- **One `:merge` firing.** The body is read from the signature, which is where `sig` is
spent; the surviving row is an `addTerm`, and `env`/`rules` come back from the pre-state. -/
theorem mergeOneOriented_noUnions {cl : Finset (Term × Term)} {d d' : FDatabase} {r₁ r₂ : Row}
    (hn : d.NoUnions) (h : d.mergeOneOriented cl r₁ r₂ = some d') : d'.NoUnions := by
  rw [FDatabase.mergeOneOriented] at h
  split at h
  · rename_i body res hm
    obtain ⟨dc, hdc, hmm⟩ := Option.bind_eq_some_iff.mp hm
    have hbody : Actions.UnionFree body := hn.sig _ _ hdc _ hmm
    split at h
    · split at h
      · rw [Option.some.injEq] at h
        exact ⟨by rw [← h]; exact hn.eqs, by rw [← h]; exact hn.sig, by rw [← h]; exact hn.rules⟩
      · obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h
        have hE : e.NoUnions :=
          execActions_noUnions hbody
            (show ({d with env := mergeEnv r₂.out r₁.out} : FDatabase).NoUnions from
              ⟨hn.eqs, hn.sig, hn.rules⟩) he
        exact ⟨by rw [show _ = (e.addTerm (.app r₂.fn (r₂.args ++ vs))).eqs from rfl,
                  FDatabase.addTerm_eqs]; exact hE.eqs,
          hE.sig, hn.rules⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

@[inherit_doc mergeOneOriented_noUnions]
theorem mergeOneWith_noUnions {cl : Finset (Term × Term)} {d d' : FDatabase} {r₁ r₂ : Row}
    (hn : d.NoUnions) (h : FDatabase.mergeOneWith cl d r₁ r₂ = some d') : d'.NoUnions := by
  rw [FDatabase.mergeOneWith] at h
  split at h
  · exact mergeOneOriented_noUnions hn h
  · exact mergeOneOriented_noUnions hn h

/-- A rebuild moves rows only. -/
theorem rebuild_noUnions {cl : Finset (Term × Term)} {d : FDatabase} (hn : d.NoUnions) :
    (FDatabase.rebuild cl d).NoUnions := ⟨hn.eqs, hn.sig, hn.rules⟩

/-- A merge pass's inner fold: every firing runs at the accumulator. -/
theorem foldl_mergeInner_noUnions {cl : Finset (Term × Term)} {r₁ : Row} :
    ∀ (rows : List Row) {acc : FDatabase}, acc.NoUnions →
      (rows.foldl (fun acc' r₂ => if r₁ == r₂ then acc' else
        match FDatabase.mergeOneWith cl acc' r₁ r₂ with
        | some acc'' => acc''
        | none => acc') acc).NoUnions
  | [], _, ha => ha
  | _ :: rows, acc, ha => by
      rename_i r₂
      refine foldl_mergeInner_noUnions rows ?_
      by_cases hb : r₁ == r₂
      · simpa [hb] using ha
      · simp only [hb, Bool.false_eq_true, if_false]
        cases hm : FDatabase.mergeOneWith cl acc r₁ r₂ with
        | none => exact ha
        | some acc'' => exact mergeOneWith_noUnions ha hm

@[inherit_doc foldl_mergeInner_noUnions]
theorem foldl_mergeOuter_noUnions {cl : Finset (Term × Term)} {e : FDatabase} :
    ∀ (rows : List Row) {acc : FDatabase}, acc.NoUnions →
      (rows.foldl (fun acc r₁ =>
        e.rows.foldl (fun acc' r₂ => if r₁ == r₂ then acc' else
          match FDatabase.mergeOneWith cl acc' r₁ r₂ with
          | some acc'' => acc''
          | none => acc') acc) acc).NoUnions
  | [], _, ha => ha
  | _ :: rows, _, ha =>
      foldl_mergeOuter_noUnions rows (foldl_mergeInner_noUnions e.rows ha)

/-- **One merge pass.** -/
theorem mergeRound_noUnions {d : FDatabase} (hn : d.NoUnions) : d.mergeRound.NoUnions := by
  rw [FDatabase.mergeRound]
  split
  · exact hn
  · exact foldl_mergeOuter_noUnions _ (rebuild_noUnions hn)

/-- **A merge phase**, however many passes it takes. -/
theorem mergeSaturateF_noUnions : ∀ (n : Nat) {d d' : FDatabase}, d.NoUnions →
    FDatabase.mergeSaturateF n d = some d' → d'.NoUnions
  | 0, _, _, hn, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact absurd h (by simp)
  | n + 1, _, _, hn, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact mergeSaturateF_noUnions n (mergeRound_noUnions hn) h

/-- **One round of a ruleset, with its merge phase.** -/
theorem runRoundM_noUnions {R : RulesetName} {d d' : FDatabase} (hn : d.NoUnions)
    (h : d.runRoundM R = some d') : d'.NoUnions :=
  mergeSaturateF_noUnions _ (execRunRules_noUnions hn) h

/-- **Rounds to the interpreter's fixpoint.** -/
theorem runSaturateM_noUnions {R : RulesetName} : ∀ (n : Nat) {d d' : FDatabase}, d.NoUnions →
    FDatabase.runSaturateM R n d = some d' → d'.NoUnions
  | 0, _, _, hn, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact absurd h (by simp)
  | n + 1, _, _, hn, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact runSaturateM_noUnions n (runRoundM_noUnions hn he) h

/-- **One command.** `.decl` is the only writer of `sig` and `.rule` the only writer of
`rules`, which is why `Cmd.UnionFree` is stated at those two and at an action. -/
theorem execCmdM_noUnions {d d' : FDatabase} {c : Cmd} (hu : c.UnionFree) (hn : d.NoUnions)
    (h : d.execCmdM c = some d') : d'.NoUnions := by
  cases c with
  | action a =>
      rw [FDatabase.execCmdM] at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      exact mergeSaturateF_noUnions _ (execAction_noUnions hu hn he) h
  | rule r =>
      rw [FDatabase.execCmdM, Option.some.injEq] at h
      refine ⟨by rw [← h]; exact hn.eqs, by rw [← h]; exact hn.sig, ?_⟩
      intro r' hr'
      rcases List.mem_cons.mp (show r' ∈ r :: d.rules by rw [← h] at hr'; exact hr') with rfl | h'
      · exact hu
      · exact hn.rules r' h'
  | run R => exact runRoundM_noUnions hn h
  | saturate R => exact runSaturateM_noUnions _ hn h
  | decl f dc =>
      rw [FDatabase.execCmdM, Option.some.injEq] at h
      refine ⟨by rw [← h]; exact hn.eqs, ?_, by rw [← h]; exact hn.rules⟩
      intro g dc' hg
      rw [← h] at hg
      have hg' : Function.update d.sig f (some dc) g = some dc' := hg
      by_cases hgf : g = f
      · subst hgf
        rw [Function.update_self, Option.some.injEq] at hg'
        exact hg' ▸ hu
      · rw [Function.update_of_ne hgf] at hg'
        exact hn.sig g dc' hg' 

@[inherit_doc execCmdM_noUnions]
theorem execProgramM_noUnions : ∀ {p : Program} {d d' : FDatabase}, Program.UnionFree p →
    d.NoUnions → d.execProgramM p = some d' → d'.NoUnions
  | [], _, _, _, hn, h => by rw [FDatabase.execProgramM, Option.some.injEq] at h; exact h ▸ hn
  | c :: cs, _, _, hu, hn, h => by
      rw [FDatabase.execProgramM] at h
      obtain ⟨e, he, hrest⟩ := Option.bind_eq_some_iff.mp h
      exact execProgramM_noUnions hu.2 (execCmdM_noUnions hu.1 hn he) hrest

/-- The initial state asserts nothing, declares nothing and holds no rule. -/
theorem empty_noUnions : FDatabase.empty.NoUnions :=
  ⟨rfl, by intro f dc h; exact absurd h (by simp [FDatabase.empty]),
    by intro r hr; exact absurd hr (by simp [FDatabase.empty])⟩

/-- **A union-free program reaches no state that asserts anything.** -/
theorem execM_noUnions {p : Program} (hu : Program.UnionFree p) {d : FDatabase}
    (h : execM p = some d) : d.NoUnions :=
  execProgramM_noUnions hu empty_noUnions h

/-- **An `execM` target of an encoded program asserts no equation**, so its `Cong` is the
identity (`Cong.eq_of_eqsRefl`) and `Database.Out` reads its key up to equality.

This is `sameClassF_iff`'s second hypothesis, discharged: `difftest correspond`'s `tgt-eqs`
column reports 0 on every case, and this is why. -/
theorem execM_encode_eqsRefl {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : tgt.EqsRefl := by
  intro p hp
  rw [(execM_noUnions (encode_unionFree P) h).eqs] at hp
  exact absurd hp (by simp)


/-! #### The invariant, as a property of the term list

`Database.Out` is not monotone along a run — a round adds terms and *deletes* rows, and the
displaced row's entry term is what survives (`mergeOneOriented_confined`) — so an invariant a
per-command induction can carry has to be stated on `terms`. With the target's `Cong` the
identity, that costs nothing: the two clauses say exactly that every term of the two shapes
the encoding writes is justified, and `Database.Out` at such a term is the same statement
back. -/

/-- **`Database.ViewsSound` and `Database.EdgesSound`, as one condition on the term list.**
A view entry term and a `@UF` entry term are the only two shapes either clause reads. -/
def FDatabase.SoundTerms (d : FDatabase) (src : Database) : Prop :=
  (∀ f cs e pf, Term.app (viewName f) (cs ++ [e, pf]) ∈ d.terms → EntrySound src f cs e) ∧
  (∀ t p pf, Term.app ufName [t, p, pf] ∈ d.terms → Cong src t p)

/-- **The term-list form is enough**, where the target asserts nothing: `Database.Out` reads
the key up to a congruence that is the identity there (`CongList.eq_of_eqsRefl`), so the row
it answers with is the entry term itself. `execM_encode_eqsRefl` is the hypothesis, at an
`execM` target. -/
theorem viewsSound_of_soundTerms {src : Database} {d : FDatabase} (hr : d.EqsRefl)
    (h : d.SoundTerms src) :
    d.toDatabase.ViewsSound src ∧ d.toDatabase.EdgesSound src := by
  refine ⟨fun f cs e pf ho => ?_, fun t p pf ho => ?_⟩
  · obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : cs = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    exact h.1 f cs e pf (by rw [FDatabase.toDatabase_terms] at hmem; exact hmem)
  · obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : [t] = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    refine h.2 t p pf ?_
    rw [FDatabase.toDatabase_terms] at hmem
    exact hmem

/-- **And it is no stronger**, where the target is subterm-closed: a key column of an entry
term is a term the state holds, which is the reflexivity `Database.out_self` wants. So the
residue below is the two clauses and not a strengthening of them. -/
theorem soundTerms_of_viewsSound {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (hv : d.toDatabase.ViewsSound src) (he : d.toDatabase.EdgesSound src) : d.SoundTerms src := by
  have hout : ∀ (f : FnName) (as vs : List Term), Term.app f (as ++ vs) ∈ d.terms →
      d.toDatabase.Out f as vs := by
    intro f as vs hmem
    refine Database.out_self (by rw [FDatabase.toDatabase_terms]; exact hmem) (fun a ha => ?_)
    rw [FDatabase.toDatabase_terms]
    exact hsc _ hmem a ((Term.mem_subtermList (Term.app f (as ++ vs))).mpr
      (Term.arg_subterms (List.mem_append_left _ ha) (Term.self_mem_subterms a)))
  exact ⟨fun f cs e pf hmem => hv f cs e pf (hout _ _ _ hmem),
    fun t p pf hmem => he t p pf (hout ufName [t] [p, pf] hmem)⟩

/-! ##### The three writers of `terms`

`FDatabase.addTerm`, `FDatabase.addRow` — which is an `addTerm` and an index write — and
`FDatabase.union`, which is what a round's accumulator folds with. Every other component
update leaves the list alone, so the induction below owes one obligation per `addTerm` the
run performs and nothing else. `addTerm` records every *subterm*, which is why the obligation
is stated over `Term.subtermList` and not at the term alone. -/

/-- `EntrySound` moves along a source that grows: `Cong` and `CongList` are monotone in `eqs`,
and `Database.terms` is read out of them. What transports a clause proved at a command's
pre-state onto the state the whole source run finishes at. -/
theorem EntrySound.mono {src src' : Database} (h : src.eqs ⊆ src'.eqs) {f : FnName}
    {cs : List Term} {e : Term} (hs : EntrySound src f cs e) : EntrySound src' f cs e :=
  let ⟨as, ham, hal, hae⟩ := hs
  ⟨as, Cong.mono ⟨h⟩ ham, hal.mono ⟨h⟩, Cong.mono ⟨h⟩ hae⟩

@[inherit_doc EntrySound.mono]
theorem FDatabase.SoundTerms.mono_src {src src' : Database} {d : FDatabase}
    (h : src.eqs ⊆ src'.eqs) (hs : d.SoundTerms src) : d.SoundTerms src' :=
  ⟨fun f cs e pf hm => (hs.1 f cs e pf hm).mono h,
    fun t p pf hm => Cong.mono ⟨h⟩ (hs.2 t p pf hm)⟩

/-- **One `addTerm`**, which is the only writer of `terms` there is. The two obligations are
about the term's *subterms*, since that is what the list records. -/
theorem FDatabase.SoundTerms.addTerm {src : Database} {d : FDatabase} {t : Term}
    (h : d.SoundTerms src)
    (hv : ∀ f cs e pf, Term.app (viewName f) (cs ++ [e, pf]) ∈ t.subtermList →
      EntrySound src f cs e)
    (hu : ∀ x p pf, Term.app ufName [x, p, pf] ∈ t.subtermList → Cong src x p) :
    (d.addTerm t).SoundTerms src := by
  constructor
  · intro f cs e pf hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact hv f cs e pf hm'
    · exact h.1 f cs e pf hm'
  · intro x p pf hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact hu x p pf hm'
    · exact h.2 x p pf hm'

/-- **One `set`.** The entry term is the whole of what the denotation sees; the index row is
not a term. -/
theorem FDatabase.SoundTerms.addRow {src : Database} {d : FDatabase} {g : FnName}
    {as vs : List Term} (h : d.SoundTerms src)
    (hv : ∀ f cs e pf,
      Term.app (viewName f) (cs ++ [e, pf]) ∈ (Term.app g (as ++ vs)).subtermList →
      EntrySound src f cs e)
    (hu : ∀ x p pf, Term.app ufName [x, p, pf] ∈ (Term.app g (as ++ vs)).subtermList →
      Cong src x p) :
    (d.addRow g as vs).SoundTerms src := h.addTerm hv hu

/-- **One firing, unioned into the accumulator.** -/
theorem FDatabase.SoundTerms.union {src : Database} {d₁ d₂ : FDatabase}
    (h₁ : d₁.SoundTerms src) (h₂ : d₂.SoundTerms src) : (d₁.union d₂).SoundTerms src := by
  constructor
  · intro f cs e pf hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact h₁.1 f cs e pf hm'
    · exact h₂.1 f cs e pf hm'
  · intro x p pf hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact h₁.2 x p pf hm'
    · exact h₂.2 x p pf hm'

/-- The base case: the initial state holds no term. -/
theorem FDatabase.empty_soundTerms {src : Database} : FDatabase.empty.SoundTerms src :=
  ⟨fun _ _ _ _ hm => absurd hm (by simp [FDatabase.empty]),
    fun _ _ _ hm => absurd hm (by simp [FDatabase.empty])⟩

/-! ##### The obligations collapse to the written term

`addTerm` records every **subterm**, so `FDatabase.SoundTerms.addTerm` asks for a
justification at every view- and `@UF`-shaped subterm of what a writer wrote — for every id
and every proof node the encoding mints, and not only for the entry. It does not have to be
paid twice. A recorded subterm the state **already holds** is discharged by
`FDatabase.SoundTerms` itself, and the shells the encoding mints around terms the state holds
— a proof node, an id — are of neither shape. So the obligation is at the written term and
nowhere else, which is what the two lemmas below say and the two after them supply the
hypothesis of. -/

/-- **The two shapes `FDatabase.SoundTerms` reads.** A recorded subterm of neither shape costs
the invariant nothing, however deep. -/
def Term.EntryShaped (t : Term) : Prop :=
  (∃ f cs e pf, t = Term.app (viewName f) (cs ++ [e, pf])) ∨
    (∃ x p pf, t = Term.app ufName [x, p, pf])

/-- **One `addTerm`, with its recorded subterms discharged by the invariant.** The two
obligations are at `t` alone; `hsub` is what pays for the rest, and
`FDatabase.subterms_of_columns` and `not_entryShaped_of_ne` are the two ways it is paid. -/
theorem FDatabase.SoundTerms.addTerm_top {src : Database} {d : FDatabase} {t : Term}
    (h : d.SoundTerms src)
    (hsub : ∀ s ∈ t.subtermList, s ≠ t → s.EntryShaped → s ∈ d.terms)
    (hv : ∀ f cs e pf, t = Term.app (viewName f) (cs ++ [e, pf]) → EntrySound src f cs e)
    (hu : ∀ x p pf, t = Term.app ufName [x, p, pf] → Cong src x p) :
    (d.addTerm t).SoundTerms src := by
  refine h.addTerm (fun f cs e pf hm => ?_) (fun x p pf hm => ?_)
  · by_cases he : Term.app (viewName f) (cs ++ [e, pf]) = t
    · exact hv f cs e pf he.symm
    · exact h.1 f cs e pf (hsub _ hm he (Or.inl ⟨f, cs, e, pf, rfl⟩))
  · by_cases he : Term.app ufName [x, p, pf] = t
    · exact hu x p pf he.symm
    · exact h.2 x p pf (hsub _ hm he (Or.inr ⟨x, p, pf, rfl⟩))

/-- **One `set`**, at the entry term it records. -/
theorem FDatabase.SoundTerms.addRow_top {src : Database} {d : FDatabase} {g : FnName}
    {as vs : List Term} (h : d.SoundTerms src)
    (hsub : ∀ s ∈ (Term.app g (as ++ vs)).subtermList, s ≠ Term.app g (as ++ vs) →
      s.EntryShaped → s ∈ d.terms)
    (hv : ∀ f cs e pf, Term.app g (as ++ vs) = Term.app (viewName f) (cs ++ [e, pf]) →
      EntrySound src f cs e)
    (hu : ∀ x p pf, Term.app g (as ++ vs) = Term.app ufName [x, p, pf] → Cong src x p) :
    (d.addRow g as vs).SoundTerms src := h.addTerm_top hsub hv hu

/-- **Every proper subterm of an entry term is held**, where the state is subterm-closed and
holds the columns. This is `addTerm_top`'s hypothesis at every writer whose columns are terms
the state already has, which is every `set` the encoding emits over ids the state built. -/
theorem FDatabase.subterms_of_columns {d : FDatabase} (hsc : d.SubtermClosed) {g : FnName}
    {cols : List Term} (hcol : ∀ c ∈ cols, c ∈ d.terms) :
    ∀ s ∈ (Term.app g cols).subtermList, s ≠ Term.app g cols → s ∈ d.terms := by
  intro s hs hne
  rw [Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact absurd rfl hne
  · obtain ⟨a, ha, hsa⟩ := (Term.mem_subtermListL cols).mp hs
    exact hsc a (hcol a ha) s ((Term.mem_subtermList a).mpr hsa)

/-- **A shell of neither shape.** The freshly minted terms a writer wraps around held ones —
a proof node, a skolem id — are applications of a name that is no view and not `@UF`, so
`addTerm_top`'s `hsub` is vacuous at them. -/
theorem not_entryShaped_of_ne {g : FnName} (hv : ∀ f, g ≠ viewName f) (hu : g ≠ ufName)
    {as : List Term} : ¬ (Term.app g as).EntryShaped := by
  rintro (⟨f, cs, e, pf, h⟩ | ⟨x, p, pf, h⟩)
  · exact hv f (Term.app.inj h).1
  · exact hu (Term.app.inj h).1

/-- **A shell of the wrong width.** Both shapes carry at least two value columns, so an
application of arity below two is of neither. `@Fiat` and `@Sym` are the two the encoding
mints. -/
theorem not_entryShaped_of_length {g : FnName} {as : List Term} (h : as.length < 2) :
    ¬ (Term.app g as).EntryShaped := by
  rintro (⟨f, cs, e, pf, hq⟩ | ⟨x, p, pf, hq⟩) <;>
    · have := congrArg List.length (Term.app.inj hq).2
      simp at this
      omega

/-- `@Trans` is neither shape: it is no view (`viewName_ne_transName`), it is not `@UF`, and
its width would make the key empty either way. -/
theorem not_entryShaped_trans {a b : Term} : ¬ (Term.app transName [a, b]).EntryShaped :=
  not_entryShaped_of_ne (fun _ h => viewName_ne_transName h.symm) (by decide)

/-- `@Sym` is neither shape, by width. -/
theorem not_entryShaped_sym {a : Term} : ¬ (Term.app symName [a]).EntryShaped :=
  not_entryShaped_of_length (by simp)

/-- `@Fiat` is neither shape, by width. -/
theorem not_entryShaped_fiat : ¬ (Term.app fiatName []).EntryShaped :=
  not_entryShaped_of_length (by simp)

/-! ##### What a `:merge` body can be, at an encoded target

`FDatabase.mergeRound` reads `d.sig.mergeOf` at a colliding row's function and runs whatever
body it finds, so "what a merge firing writes" is an open family until the signature is
pinned. At an encoded target it is not open: `encode` declares exactly two kinds of merge
function — `@UF` and the views — and gives them the **same** body and the same result
expressions. That is the sig-shape invariant the enumeration of `FDatabase.mergeRound`'s
writers needs, and it survives the whole run for one reason: `encodeCmds` emits no
declaration at all, so nothing after the prelude moves the signature. -/

/-- **Only `@UF` and the views carry a `:merge` body, and both carry `mergeBody`.** A
`.noMerge` function — the term relations — and a constructor are excluded by the hypothesis
rather than by a disjunct.

The two **widths** come with it, because a merge firing's writes are read at them: both
declarations have `outArity 2`, an e-class column and its proof, and `@UF` is unary.

So does the **identity width**, `identityVals = some 1`, which is what decides whether a
collision runs the body at all: `FDatabase.noConflict` compares that many value columns, and
at one column it compares exactly the e-class columns. Without it the shape would admit
`identityVals = some 0`, where every collision skips the body and `mergeOneOriented` drops the
displaced row leaving no `@UF` edge behind — which is precisely the case
`mergeOneOriented_survivorUF` has to exclude. -/
def Signature.MergeShape (sig : Signature) : Prop :=
  ∀ f dc, sig f = some dc → ∀ body res, dc.merge = some (.merge body res) →
    (f = ufName ∨ ∃ g, f = viewName g) ∧ body = mergeBody ∧ res = mergeResult ∧
      dc.outArity = 2 ∧ (f = ufName → dc.arity = 1) ∧ dc.identityVals = some 1

theorem Signature.mergeShape_empty : Signature.MergeShape (fun _ => none) := by
  intro f dc h
  exact absurd h (by simp)

/-- One declaration, which is the only thing that moves a signature. -/
theorem Signature.MergeShape.update {sig : Signature} (h : sig.MergeShape) {f : FnName}
    {dc : FnDecl}
    (hdc : ∀ body res, dc.merge = some (.merge body res) →
      (f = ufName ∨ ∃ g, f = viewName g) ∧ body = mergeBody ∧ res = mergeResult ∧
        dc.outArity = 2 ∧ (f = ufName → dc.arity = 1) ∧ dc.identityVals = some 1) :
    Signature.MergeShape (Function.update sig f (some dc)) := by
  intro g dcg hg
  rw [Function.update_apply] at hg
  by_cases hfg : g = f
  · subst hfg
    obtain rfl : dcg = dc := by simpa [eq_comm] using hg
    exact hdc
  · rw [if_neg hfg] at hg
    exact h g dcg hg

/-- A command that cannot break the shape: anything but a declaration, or a declaration whose
own `:merge` fits. -/
def Cmd.MergeShapeOk : Cmd → Prop
  | .decl f dc => ∀ body res, dc.merge = some (.merge body res) →
      (f = ufName ∨ ∃ g, f = viewName g) ∧ body = mergeBody ∧ res = mergeResult ∧
        dc.outArity = 2 ∧ (f = ufName → dc.arity = 1) ∧ dc.identityVals = some 1
  | _ => True

/-- One command: only a declaration moves the signature, and a legal one keeps the shape. -/
theorem FDatabase.execCmdM_mergeShape {d d' : FDatabase} {c : Cmd} (hc : c.MergeShapeOk)
    (h : d.sig.MergeShape) (hs : d.execCmdM c = some d') : d'.sig.MergeShape := by
  rw [FDatabase.execCmdM_sig hs]
  cases c with
  | decl f dc => exact h.update hc
  | _ => exact h

@[inherit_doc FDatabase.execCmdM_mergeShape]
theorem FDatabase.execProgramM_mergeShape {p : Program} (hp : ∀ c ∈ p, c.MergeShapeOk) :
    ∀ {d D : FDatabase}, d.sig.MergeShape → d.execProgramM p = some D → D.sig.MergeShape := by
  induction p with
  | nil =>
    intro d D h hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hrun
    exact hrun ▸ h
  | cons c cs ih =>
    intro d D h hrun
    rw [FDatabase.execProgramM] at hrun
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hrun
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
      (FDatabase.execCmdM_mergeShape (hp c List.mem_cons_self) h h₁) h₂

/-! ###### The two halves of the encoded program

The prelude is where every declaration is, and `encodeCmds` is where none is. -/

theorem mergeShapeOk_ruleProofDecls : ∀ (rs : List Rule) (i : Nat),
    ∀ c ∈ ruleProofDecls rs i, c.MergeShapeOk
  | [], _ => by simp [ruleProofDecls]
  | r :: rs, i => by
      intro c hc
      rw [ruleProofDecls, List.mem_cons] at hc
      rcases hc with rfl | hc
      · intro body res hb
        exact absurd hb (by simp [proofDecl])
      · exact mergeShapeOk_ruleProofDecls rs (i + 1) c hc

/-- **The prelude's declarations, enumerated.** The proof vocabulary and the skolem
constructors have no `:merge`; a term relation has `.noMerge`; `@UF` and the views have
`mergeBody`, which is what the two disjuncts record. -/
theorem mergeShapeOk_encodePrelude (P : Program) : ∀ c ∈ encodePrelude P, c.MergeShapeOk := by
  intro c hc
  rw [encodePrelude] at hc
  rcases List.mem_append.mp hc with h | h
  · rcases List.mem_append.mp h with h₁ | h₁
    · rw [proofDecls] at h₁
      rcases List.mem_append.mp h₁ with h₂ | h₂
      · rcases List.mem_append.mp h₂ with h₃ | h₃
        · have h₄ : c = Cmd.decl fiatName (proofDecl 0) ∨ c = Cmd.decl symName (proofDecl 1) ∨
              c = Cmd.decl transName (proofDecl 2) := by simpa using h₃
          rcases h₄ with rfl | rfl | rfl <;>
            exact fun body res hb => absurd hb (by simp [proofDecl])
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h₃
          exact fun body res hb => absurd hb (by simp [proofDecl])
      · exact mergeShapeOk_ruleProofDecls _ _ c h₂
    · rcases List.mem_cons.mp h₁ with rfl | h₂
      · intro body res hb
        obtain ⟨rfl, rfl⟩ : mergeBody = body ∧ mergeResult = res := by
          simpa [ufDecl] using hb
        exact ⟨Or.inl rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩
      · obtain ⟨fk, -, h₃⟩ := List.mem_flatMap.mp h₂
        have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
        rcases h₄ with rfl | rfl | rfl
        · exact fun body res hb => absurd hb (by simp [skolemDecl])
        · intro body res hb
          obtain ⟨rfl, rfl⟩ : mergeBody = body ∧ mergeResult = res := by
            simpa [viewDecl] using hb
          exact ⟨Or.inr ⟨fk.1, rfl⟩, rfl, rfl, rfl, fun hu => absurd hu viewName_ne_ufName, rfl⟩
        · exact fun body res hb => absurd hb (by simp [termDecl])
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
    trivial

/-- **`encodeCmd` emits no declaration**, which is why the shape is fixed once the prelude has
run. -/
theorem mergeShapeOk_encodeCmd (c : Cmd) (n i : Nat) :
    ∀ c' ∈ (encodeCmd c n i).1, c'.MergeShapeOk := by
  intro c' hc'
  cases c with
  | action a =>
      have h : c' ∈ (encodeAction fiatE a n).1.map Cmd.action ++ [Cmd.saturate rebuildRuleset] :=
        hc'
      rcases List.mem_append.mp h with h₁ | h₁
      · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h₁
        trivial
      · obtain rfl : c' = Cmd.saturate rebuildRuleset := by simpa using h₁
        trivial
  | rule r =>
      have h : c' ∈ [Cmd.rule (encodeRule i r n).1] := hc'
      obtain rfl : c' = Cmd.rule (encodeRule i r n).1 := by simpa using h
      trivial
  | run R =>
      have h : c' ∈ [Cmd.run R, Cmd.saturate rebuildRuleset] := hc'
      have h2 : c' = Cmd.run R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
      rcases h2 with rfl | rfl <;> trivial
  | saturate R =>
      have h : c' ∈ [Cmd.saturate R, Cmd.saturate rebuildRuleset] := hc'
      have h2 : c' = Cmd.saturate R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
      rcases h2 with rfl | rfl <;> trivial
  | decl f dc =>
      have h : c' ∈ ([] : Program) := hc'
      simp at h

@[inherit_doc mergeShapeOk_encodeCmd]
theorem mergeShapeOk_encodeCmds : ∀ (p : Program) (n i : Nat),
    ∀ c ∈ (encodeCmds p n i).1, c.MergeShapeOk
  | [], _, _ => by simp [encodeCmds]
  | c :: cs, n, i => by
      intro c' hc'
      have hsplit : (encodeCmds (c :: cs) n i).1
          = (encodeCmd c n i).1
            ++ (encodeCmds cs (encodeCmd c n i).2.1 (encodeCmd c n i).2.2).1 := rfl
      rw [hsplit] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact mergeShapeOk_encodeCmd c n i c' h
      · exact mergeShapeOk_encodeCmds cs _ _ c' h

/-- **The sig-shape invariant at the state `execM` returned.** -/
theorem execM_encode_mergeShape {P : Program} {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.sig.MergeShape := by
  rw [execM, encode] at htgt
  refine FDatabase.execProgramM_mergeShape (p := encodePrelude P ++ (encodeCmds P 0 0).1)
    (fun c hc => ?_) ?_ htgt
  · rcases List.mem_append.mp hc with h | h
    · exact mergeShapeOk_encodePrelude P c h
    · exact mergeShapeOk_encodeCmds P 0 0 c h
  · exact Signature.mergeShape_empty

/-! ##### And what a collision compares

`mergeOneOriented` fires on rows whose keys are **congruent**, read through the pre-pass
`closureF`. At an encoded target `Cong` is the identity (`execM_encode_eqsRefl`), so
congruent keys are equal keys and the two entry terms a firing combines are entries at one
key — which is exactly `cong_of_entrySound_collide`'s hypothesis. -/

/-- **The closure of a state that asserts nothing is the diagonal.** -/
theorem diag_closureF {d : FDatabase} (hr : d.EqsRefl) {p : Term × Term}
    (hp : p ∈ d.closureF) : p.1 = p.2 :=
  Cong.eq_of_eqsRefl hr.toDatabase (FDatabase.mem_closureF_iff.mp (by
    rw [show (p.1, p.2) = p from rfl]; exact hp))

/-- **Congruent key tuples are equal, against a diagonal closure.** Stated at the closure and
not at a state, because `FDatabase.mergeRound` compares against the closure of its
**pre-pass** state while the accumulator has moved on. -/
theorem eq_of_congrKeys {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2) :
    ∀ {as bs : List Term}, FDatabase.congrKeys cl as bs = true → as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    have hlen := (Bool.and_eq_true_iff.mp h).1
    have h0 : (0 : Nat) = bs.length := by simpa using hlen
    exact (List.eq_nil_of_length_eq_zero h0.symm).symm
  | cons a as ih =>
    intro bs h
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp h
    match bs with
    | [] => simp at hlen
    | b :: bs' =>
      have hlen' : (as.length == bs'.length) = true := by simpa using hlen
      have hall' := List.all_eq_true.mp hall
      have hab : (a, b) ∈ cl := by
        have hq := hall' (a, b) (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
        simpa using hq
      have hrest : FDatabase.congrKeys cl as bs' = true :=
        Bool.and_eq_true_iff.mpr ⟨hlen', List.all_eq_true.mpr (fun q hq =>
          hall' q (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq))⟩
      have heq : a = b := hcl (a, b) hab
      rw [heq, ih hrest]


/-! ##### What a merge firing writes

`FDatabase.mergeRound` is a rebuild and then a fold of `FDatabase.mergeOneWith` over row
pairs, and only one of those touches `terms`: `FDatabase.rebuild` re-keys rows, the
`noConflict` branch drops one, and neither writes the list. What is left is
`FDatabase.mergeOneOriented`'s other branch, which writes exactly twice — the `@UF` edge
`mergeBody` `set`s between the two colliding rows' e-class columns, and the surviving entry
`mergeResult` computes. With `Signature.MergeShape` pinning the body, both are enumerated
below and then discharged against the two rows the firing combined. -/

/-- A non-primitive application, inverted: the value is the application of the head to the
operands' values. -/
theorem Expr.eval_app_inv {sig : Signature} {σ : Env} {f : FnName} {args : List Expr}
    {t : Term} (hp : Prim.ofName f = none) (h : (Expr.app f args).eval sig σ = some t) :
    ∃ ts, Expr.evalList sig args σ = some ts ∧ t = .app f ts := by
  rw [Expr.eval, hp] at h
  by_cases hc : sig.IsCtor f
  · rw [if_pos hc] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨ts, hts, rfl⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- **`(if (ordering-gt _ _) ea eb)` answers with one of its two branches**, whichever way the
tie-break went. The four selectors `mergeBody` and `mergeResult` are built from are all of
this shape, and which branch each takes is not what the invariant reads — only that the
answer is one of the two columns it was given. -/
theorem eval_ifGt_inv {sig : Signature} {σ : Env} {e₁ e₂ ea eb : Expr} {t : Term}
    (h : (ifE (gtE e₁ e₂) ea eb).eval sig σ = some t) :
    ea.eval sig σ = some t ∨ eb.eval sig σ = some t := by
  rw [ifE, Expr.eval, show Prim.ofName "if" = some Prim.ifThenElse from rfl] at h
  obtain ⟨ts, hts, happ⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.evalList] at hts
  obtain ⟨c, -, hts⟩ := Option.bind_eq_some_iff.mp hts
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hts
  obtain ⟨ta, tb, ha, hb, rfl⟩ := Expr.evalList_pair hus
  match c with
  | .app _ _ => exact absurd happ (by simp [Prim.apply])
  | .lit (.int _) => exact absurd happ (by simp [Prim.apply])
  | .lit (.bool b) =>
    rw [Prim.apply, Option.some.injEq] at happ
    cases b with
    | true => exact Or.inl (by rw [ha, ← happ]; simp)
    | false => exact Or.inr (by rw [hb, ← happ]; simp)

/-- The environment a two-column collision runs the body in. -/
theorem mergeEnv_pair (o0 o1 n0 n1 : Term) :
    mergeEnv [o0, o1] [n0, n1]
      = [("old0", o0), ("new0", n0), ("old1", o1), ("new1", n1)] := rfl

@[inherit_doc mergeEnv_pair]
theorem eval_mergeEnv_old0 {sig : Signature} {o0 o1 n0 n1 : Term} :
    (Expr.var "old0").eval sig (mergeEnv [o0, o1] [n0, n1]) = some o0 := by
  rw [Expr.eval, mergeEnv_pair]; simp [Env.lookup]

@[inherit_doc mergeEnv_pair]
theorem eval_mergeEnv_new0 {sig : Signature} {o0 o1 n0 n1 : Term} :
    (Expr.var "new0").eval sig (mergeEnv [o0, o1] [n0, n1]) = some n0 := by
  rw [Expr.eval, mergeEnv_pair]; simp [Env.lookup]

@[inherit_doc mergeEnv_pair]
theorem eval_mergeEnv_old1 {sig : Signature} {o0 o1 n0 n1 : Term} :
    (Expr.var "old1").eval sig (mergeEnv [o0, o1] [n0, n1]) = some o1 := by
  rw [Expr.eval, mergeEnv_pair]; simp [Env.lookup]

@[inherit_doc mergeEnv_pair]
theorem eval_mergeEnv_new1 {sig : Signature} {o0 o1 n0 n1 : Term} :
    (Expr.var "new1").eval sig (mergeEnv [o0, o1] [n0, n1]) = some n1 := by
  rw [Expr.eval, mergeEnv_pair]; simp [Env.lookup]

/-- Each of the four selectors answers with one of the two columns it chose between. -/
theorem mergeSelector_cases {sig : Signature} {o0 o1 n0 n1 t : Term} :
    (minE (.var "old0") (.var "new0")).eval sig (mergeEnv [o0, o1] [n0, n1]) = some t →
      t = o0 ∨ t = n0 := by
  intro h
  rcases eval_ifGt_inv h with h' | h'
  · exact Or.inr (Option.some.inj (h'.symm.trans eval_mergeEnv_new0))
  · exact Or.inl (Option.some.inj (h'.symm.trans eval_mergeEnv_old0))

@[inherit_doc mergeSelector_cases]
theorem mergeSelectorMax_cases {sig : Signature} {o0 o1 n0 n1 t : Term} :
    (maxE (.var "old0") (.var "new0")).eval sig (mergeEnv [o0, o1] [n0, n1]) = some t →
      t = o0 ∨ t = n0 := by
  intro h
  rcases eval_ifGt_inv h with h' | h'
  · exact Or.inl (Option.some.inj (h'.symm.trans eval_mergeEnv_old0))
  · exact Or.inr (Option.some.inj (h'.symm.trans eval_mergeEnv_new0))

@[inherit_doc mergeSelector_cases]
theorem mergeProof_cases {sig : Signature} {o0 o1 n0 n1 t : Term} {e₁ e₂ : Expr}
    (h : (ifE (gtE e₁ e₂) (.var "old1") (.var "new1")).eval sig
        (mergeEnv [o0, o1] [n0, n1]) = some t) : t = o1 ∨ t = n1 := by
  rcases eval_ifGt_inv h with h' | h'
  · exact Or.inl (Option.some.inj (h'.symm.trans eval_mergeEnv_old1))
  · exact Or.inr (Option.some.inj (h'.symm.trans eval_mergeEnv_new1))

/-- **`mergeBody`, run and inverted.** One `set` of a `@UF` edge whose key and value are the
two rows' e-class columns and whose proof column is `@Trans (@Sym _) _` over their proof
columns. Which of the two goes where is the tie-break's business and not the invariant's. -/
theorem execActions_mergeBody_inv {m m' : FDatabase} {o0 o1 n0 n1 : Term}
    (henv : m.env = mergeEnv [o0, o1] [n0, n1])
    (h : execActions m mergeBody = some m') :
    ∃ mx mn a b : Term, (mx = o0 ∨ mx = n0) ∧ (mn = o0 ∨ mn = n0) ∧
      (a = o1 ∨ a = n1) ∧ (b = o1 ∨ b = n1) ∧
      m' = m.addRow ufName [mx] [mn, .app transName [.app symName [a], b]] := by
  rw [mergeBody, execActions] at h
  obtain ⟨m₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  rw [execActions, Option.some.injEq] at h₂
  subst h₂
  obtain ⟨as, vs, has, hvs, rfl⟩ := execAction_set h₁
  rw [henv] at has hvs
  obtain ⟨mx, hmx, rfl⟩ := Expr.evalList_singleton has
  obtain ⟨mn, pf, hmn, hpf, rfl⟩ := Expr.evalList_pair hvs
  obtain ⟨ts, hts, rfl⟩ := Expr.eval_app_inv (f := transName) (by decide) hpf
  obtain ⟨sy, lo, hsy, hlo, rfl⟩ := Expr.evalList_pair hts
  obtain ⟨us, hus, rfl⟩ := Expr.eval_app_inv (f := symName) (by decide) hsy
  obtain ⟨hi, hhi, rfl⟩ := Expr.evalList_singleton hus
  exact ⟨mx, mn, hi, lo, mergeSelectorMax_cases hmx, mergeSelector_cases hmn,
    mergeProof_cases hhi, mergeProof_cases hlo, rfl⟩

/-- **`mergeResult`, run and inverted.** The surviving row's value tuple is one of the two
e-class columns and one of the two proof columns. -/
theorem evalList_mergeResult_inv {sig : Signature} {o0 o1 n0 n1 : Term} {vs : List Term}
    (h : Expr.evalList sig mergeResult (mergeEnv [o0, o1] [n0, n1]) = some vs) :
    ∃ mn lo, (mn = o0 ∨ mn = n0) ∧ (lo = o1 ∨ lo = n1) ∧ vs = [mn, lo] := by
  obtain ⟨mn, lo, hmn, hlo, rfl⟩ := Expr.evalList_pair h
  exact ⟨mn, lo, mergeSelector_cases hmn, mergeProof_cases hlo, rfl⟩


/-! ###### The state facts a firing reads

Three, each named: the two rows are **entry terms** (`FDatabase.IndexOk.entry`, read at a
diagonal state), their columns are terms the state holds (subterm closure), and their widths
are the declaration's (`FDatabase.IndexOk.width`). -/

/-- `FDatabase.SoundTerms` reads `terms` and nothing else. -/
theorem FDatabase.SoundTerms.mono_terms {src : Database} {d e : FDatabase}
    (ht : ∀ t ∈ e.terms, t ∈ d.terms) (h : d.SoundTerms src) : e.SoundTerms src :=
  ⟨fun f cs x pf hm => h.1 f cs x pf (ht _ hm), fun x p pf hm => h.2 x p pf (ht _ hm)⟩

/-- A term the list held it still holds. -/
theorem FDatabase.mem_addTerm_of_mem {d : FDatabase} {t s : Term} (hs : s ∈ d.terms) :
    s ∈ (d.addTerm t).terms := by
  simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
  exact Or.inr hs

/-- Subterm closure survives an `addTerm`: what the list records is closed under subterms
already. -/
theorem FDatabase.SubtermClosed.addTerm {d : FDatabase} (h : d.SubtermClosed) (t : Term) :
    (d.addTerm t).SubtermClosed := by
  intro u hu s hs
  simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append] at hu ⊢
  rcases hu with hu | hu
  · exact Or.inl ((Term.mem_subtermList t).mpr
      (((Term.mem_subtermList u).mp hs).trans ((Term.mem_subtermList t).mp hu)))
  · exact Or.inr (h u hu s hs)

@[inherit_doc FDatabase.SubtermClosed.addTerm]
theorem FDatabase.SubtermClosed.addRow {d : FDatabase} (h : d.SubtermClosed) (g : FnName)
    (as vs : List Term) : (FDatabase.addRow g as vs d).SubtermClosed :=
  h.addTerm (.app g (as ++ vs))

/-- A column of a term the list holds is a term the list holds. -/
theorem FDatabase.mem_terms_of_column {d : FDatabase} (hsc : d.SubtermClosed) {g : FnName}
    {cols : List Term} (hmem : Term.app g cols ∈ d.terms) {c : Term} (hc : c ∈ cols) :
    c ∈ d.terms :=
  hsc _ hmem c ((Term.mem_subtermList _).mpr
    (Term.arg_subterms hc (Term.self_mem_subterms c)))

/-- **A row is an entry term**, where the state asserts nothing: `FDatabase.IndexOk.entry`
reads the key up to a congruence that is the identity there. This is the direction soundness
needs, and the one `cxTgt_not_indexCurrent` does *not* refute — its converse
`FDatabase.IndexCurrent` is what that refutes, which is why this residue and
`execM_viewJoined` are separate holes. -/
theorem mem_terms_of_indexOk {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {r : Row} (hm : r ∈ d.rows) (hmg : d.sig.mergeOf r.fn ≠ none) :
    Term.app r.fn (r.args ++ r.out) ∈ d.terms := by
  obtain ⟨bs, hcl, hmem⟩ := hidx.entry r hm hmg
  obtain rfl : r.args = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
  rw [FDatabase.toDatabase_terms] at hmem
  exact hmem

/-- `FDatabase.SoundTerms.addTerm_top`'s hypothesis, one column at a time. -/
theorem entryShaped_mem_of_columns {d : FDatabase} {g : FnName} {cols : List Term}
    (hcol : ∀ c ∈ cols, ∀ s ∈ c.subtermList, s.EntryShaped → s ∈ d.terms) :
    ∀ s ∈ (Term.app g cols).subtermList, s ≠ Term.app g cols →
      s.EntryShaped → s ∈ d.terms := by
  intro s hs hne hshaped
  rw [Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact absurd rfl hne
  · obtain ⟨c, hc, hsub⟩ := (Term.mem_subtermListL _).mp hs
    exact hcol c hc s ((Term.mem_subtermList c).mpr hsub) hshaped

/-- A column the state already holds. -/
theorem entryShaped_mem_of_held {d : FDatabase} (hsc : d.SubtermClosed) {c : Term}
    (hc : c ∈ d.terms) : ∀ s ∈ c.subtermList, s.EntryShaped → s ∈ d.terms :=
  fun s hs _ => hsc c hc s hs

/-- **The proof node a merge body mints.** `@Trans (@Sym a) b` is of neither shape and neither
is its `@Sym`, so everything the clause has to answer for under it is a subterm of `a` or of
`b` — and those are the two colliding rows' proof columns, which the state holds. This is the
whole of what "no proof term is view- or `@UF`-shaped" costs at this writer. -/
theorem entryShaped_mem_of_transSym {d : FDatabase} (hsc : d.SubtermClosed) {a b : Term}
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) :
    ∀ s ∈ (Term.app transName [Term.app symName [a], b]).subtermList,
      s.EntryShaped → s ∈ d.terms := by
  intro s hs hshaped
  rw [Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact absurd hshaped not_entryShaped_trans
  · obtain ⟨c, hc, hsub⟩ := (Term.mem_subtermListL _).mp hs
    have hc2 : c = Term.app symName [a] ∨ c = b := by simpa using hc
    have hsl : s ∈ c.subtermList := (Term.mem_subtermList c).mpr hsub
    rcases hc2 with rfl | rfl
    · rw [Term.subtermList, List.mem_cons] at hsl
      rcases hsl with rfl | hsl
      · exact absurd hshaped not_entryShaped_sym
      · obtain ⟨z, hz, hsub2⟩ := (Term.mem_subtermListL _).mp hsl
        obtain rfl : z = a := by simpa using hz
        exact hsc z ha s ((Term.mem_subtermList z).mpr hsub2)
    · exact hsc c hb s hsl

/-- **The `@UF` edge a merge body writes, against the invariant.** Its key and value are the
two colliding rows' e-class columns and its proof column is the minted `@Trans (@Sym _) _`, so
the only obligation is the edge itself. -/
theorem soundTerms_addRow_uf {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (h : d.SoundTerms src) {mx mn a b : Term}
    (hmx : mx ∈ d.terms) (hmn : mn ∈ d.terms) (ha : a ∈ d.terms) (hb : b ∈ d.terms)
    (hcong : Cong src mx mn) :
    (FDatabase.addRow ufName [mx] [mn, .app transName [.app symName [a], b]] d).SoundTerms
      src := by
  refine h.addRow_top (entryShaped_mem_of_columns (fun c hc => ?_)) (fun f cs x q hq => ?_)
    (fun x p q hq => ?_)
  · have hc2 : c = mx ∨ c = mn ∨ c = Term.app transName [Term.app symName [a], b] := by
      simpa using hc
    rcases hc2 with rfl | rfl | rfl
    · exact entryShaped_mem_of_held hsc hmx
    · exact entryShaped_mem_of_held hsc hmn
    · exact entryShaped_mem_of_transSym hsc ha hb
  · exact absurd (Term.app.inj hq).1 (fun hz => viewName_ne_ufName hz.symm)
  · obtain ⟨-, hcols⟩ := Term.app.inj hq
    have h3 : [mx, mn, Term.app transName [Term.app symName [a], b]] = [x, p, q] := hcols
    obtain rfl : mx = x := (List.cons.inj h3).1
    obtain rfl : mn = p := (List.cons.inj (List.cons.inj h3).2).1
    exact hcong

/-- **One merge firing preserves the invariant, and asks nothing beyond the state.**

Two writes and no others: the `@UF` edge `mergeBody` `set`s between the two colliding rows'
e-class columns, and the entry `mergeResult` leaves at the resident row's key. Both are
justified against the **two rows the firing combined**, which `mem_terms_of_indexOk` reads
back as entry terms and `FDatabase.SoundTerms` then justifies — `cong_of_entrySound_collide`
for the edge and `EntrySound.select` for the survivor at a view, the `edges` clause twice over
at `@UF`. Which column each selector picked is not part of it: `mergeSelector_cases` says every
selector answers with one of the two it chose between, and both are justified.

The state facts are `FDatabase.IndexOk`'s two clauses, subterm closure and `EqsRefl`; the
body's shape is `Signature.MergeShape`; and `hcl` is the pass's closure being the diagonal,
which at an encoded target `execM_encode_eqsRefl` supplies. `cl` is a parameter and not
`d.closureF` because `FDatabase.mergeRound` compares against the closure of its **pre-pass**
state while the accumulator has moved on. -/
theorem mergeOneOriented_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : d.SoundTerms src)
    (hfire : d.mergeOneOriented cl r₁ r₂ = some e) : e.SoundTerms src := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
      obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
      obtain ⟨hname, rfl, rfl, hout2, huf1, -⟩ := hshape r₁.fn dc hdc body res hmergedc
      split at hfire
      next hg =>
        obtain ⟨⟨⟨hfn, hkeys⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
            FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
        have hmg1 : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
        have hmg2 : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg1
        have hE1 := mem_terms_of_indexOk hr hidx hmem₁ hmg1
        have hE2 := mem_terms_of_indexOk hr hidx hmem₂ hmg2
        have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hkeys
        obtain ⟨hk1, hw1⟩ := hidx.width r₁ hmem₁ dc hdc hmg1
        obtain ⟨-, hw2⟩ := hidx.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg2
        rw [hout2] at hw1 hw2
        obtain ⟨n0, n1, hr1out⟩ := List.length_eq_two.mp hw1
        obtain ⟨o0, o1, hr2out⟩ := List.length_eq_two.mp hw2
        have hcol₁ : ∀ c ∈ r₁.args ++ r₁.out, c ∈ d.terms :=
          fun c hc => FDatabase.mem_terms_of_column hsc hE1 hc
        have hcol₂ : ∀ c ∈ r₂.args ++ r₂.out, c ∈ d.terms :=
          fun c hc => FDatabase.mem_terms_of_column hsc hE2 hc
        have hn0 : n0 ∈ d.terms := hcol₁ n0 (by rw [hr1out]; simp)
        have hn1 : n1 ∈ d.terms := hcol₁ n1 (by rw [hr1out]; simp)
        have ho0 : o0 ∈ d.terms := hcol₂ o0 (by rw [hr2out]; simp)
        have ho1 : o1 ∈ d.terms := hcol₂ o1 (by rw [hr2out]; simp)
        have hE1' : Term.app r₁.fn (r₁.args ++ [n0, n1]) ∈ d.terms := by
          rw [← hr1out]; exact hE1
        have hE2' : Term.app r₂.fn (r₂.args ++ [o0, o1]) ∈ d.terms := by
          rw [← hr2out]; exact hE2
        -- the two writes, justified against the two rows the firing combined
        have hobl : Cong src o0 n0 ∧ ∀ v, (v = o0 ∨ v = n0) → ∀ lo,
            (∀ f cs x pf, Term.app r₂.fn (r₂.args ++ [v, lo])
                = Term.app (viewName f) (cs ++ [x, pf]) → EntrySound src f cs x) ∧
              (∀ x p pf, Term.app r₂.fn (r₂.args ++ [v, lo])
                = Term.app ufName [x, p, pf] → Cong src x p) := by
          have hfn2 : r₂.fn = r₁.fn := hfn.symm
          rcases hname with hn | ⟨g, hn⟩
          · -- the union-find table: the two rows are two parents of one key
            obtain ⟨x0, hx0⟩ : ∃ x0, r₁.args = [x0] := by
              rw [huf1 hn] at hk1; exact List.length_eq_one_iff.mp hk1
            have hu1 : Cong src x0 n0 := by
              refine h.2 x0 n0 n1 ?_
              have := hE1'
              rw [hn, hx0] at this
              exact this
            have hu2 : Cong src x0 o0 := by
              refine h.2 x0 o0 o1 ?_
              have := hE2'
              rw [hfn2, hn, ← hargs, hx0] at this
              exact this
            refine ⟨hu2.symm.trans hu1, fun v hv0 lo => ⟨fun f cs x pf hq => ?_, ?_⟩⟩
            · exact absurd ((Term.app.inj hq).1.symm.trans (hfn2.trans hn))
                (fun hz => viewName_ne_ufName hz)
            · intro x p pf hq
              obtain ⟨-, hcols⟩ := Term.app.inj hq
              rw [← hargs, hx0] at hcols
              have h3 : [x0, v, lo] = [x, p, pf] := hcols
              obtain rfl : x0 = x := (List.cons.inj h3).1
              obtain rfl : v = p := (List.cons.inj (List.cons.inj h3).2).1
              rcases hv0 with rfl | rfl
              · exact hu2
              · exact hu1
          · -- a view: the two rows are two e-classes at one key
            have hv1 : EntrySound src g r₂.args n0 := by
              refine h.1 g r₂.args n0 n1 ?_
              rw [← hargs, ← hn]; exact hE1'
            have hv2 : EntrySound src g r₂.args o0 := by
              refine h.1 g r₂.args o0 o1 ?_
              rw [← hn, ← hfn2]; exact hE2'
            refine ⟨cong_of_entrySound_collide hv2 hv1, fun v hv0 lo => ⟨?_, fun x p pf hq => ?_⟩⟩
            · intro f cs x pf hq
              obtain ⟨hfname, hcols⟩ := Term.app.inj hq
              obtain rfl : f = g :=
                (viewName_inj ((hfn2.trans hn).symm.trans hfname)).symm
              obtain ⟨rfl, hlast⟩ := List.append_inj' hcols rfl
              obtain rfl : v = x := (List.cons.inj hlast).1
              exact EntrySound.select hv2 hv1 hv0
            · exact absurd ((Term.app.inj hq).1.symm.trans (hfn2.trans hn)).symm
                viewName_ne_ufName
        obtain ⟨hcong, hsurv⟩ := hobl
        split at hfire
        next =>
          rw [Option.some.injEq] at hfire
          exact h.mono_terms (fun t ht => by rw [← hfire] at ht; exact ht)
        next =>
          obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
          obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hfire
          have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
              = mergeEnv [o0, o1] [n0, n1] := by rw [hr1out, hr2out]
          obtain ⟨mx, mn, a, b, hmx, hmn, ha, hb, rfl⟩ := execActions_mergeBody_inv henv hm
          have hmxm : mx ∈ d.terms := by rcases hmx with rfl | rfl <;> assumption
          have hmnm : mn ∈ d.terms := by rcases hmn with rfl | rfl <;> assumption
          have ham : a ∈ d.terms := by rcases ha with rfl | rfl <;> assumption
          have hbm : b ∈ d.terms := by rcases hb with rfl | rfl <;> assumption
          have hcongmm : Cong src mx mn := by
            rcases hmx with rfl | rfl <;> rcases hmn with rfl | rfl
            · exact hcong.trans hcong.symm
            · exact hcong
            · exact hcong.symm
            · exact hcong.symm.trans hcong
          have hstep₁ := soundTerms_addRow_uf
            (d := ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase)) hsc h
            hmxm hmnm ham hbm hcongmm
          have hsc₁ := (hsc : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).SubtermClosed
            ).addRow ufName [mx] [mn, Term.app transName [Term.app symName [a], b]]
          obtain ⟨v, lo, hv0, hlo0, rfl⟩ :=
            evalList_mergeResult_inv (o0 := o0) (o1 := o1) (n0 := n0) (n1 := n1)
              (by rw [show (FDatabase.addRow ufName [mx]
                    [mn, Term.app transName [Term.app symName [a], b]]
                    { d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
                  = mergeEnv [o0, o1] [n0, n1] from henv] at hvs; exact hvs)
          obtain ⟨hvv, huu⟩ := hsurv v hv0 lo
          refine FDatabase.SoundTerms.mono_terms (fun t ht => ht)
            (hstep₁.addTerm_top (entryShaped_mem_of_columns (fun c hc => ?_)) hvv huu)
          rcases List.mem_append.mp hc with hc' | hc'
          · exact entryShaped_mem_of_held hsc₁
              (FDatabase.mem_addTerm_of_mem (hcol₂ c (List.mem_append_left _ hc')))
          · have hc2 : c = v ∨ c = lo := by simpa using hc'
            refine entryShaped_mem_of_held hsc₁ (FDatabase.mem_addTerm_of_mem ?_)
            rcases hc2 with rfl | rfl
            · rcases hv0 with rfl | rfl <;> assumption
            · rcases hlo0 with rfl | rfl <;> assumption
      next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)


/-! ###### The one row a firing deletes, and the edge that replaces it

`FDatabase.mergeOneOriented` is the only writer in the interpreter that **removes** a row, so
it is the only one that can break "every merge-function entry term has a current row at a
congruent key whose e-class column is `@UF`-reachable from the entry's" — the claim
`execM_rebuildClosed` is left waiting on, and the one `cxTgt_currentUF` is a compiled instance
of.

**It does not break it, and not by accident: it repairs it in the same step.** The two
selectors are complementary at *one* comparison — `mergeResult` keeps `ordering-min old0 new0`
and `mergeBody` writes `@UF (ordering-max old0 new0) ↦ (ordering-min old0 new0, …)`, both
under `Term.blt new0 old0` — so the surviving row's e-class column is whichever of the two
collided columns the tie-break calls smaller, and the other one is handed an `@UF` edge to it
in the very state the firing returns. `Database.UFReach` is then reflexivity on one side and a
single step on the other, whichever way the tie-break went. `mergeBody_result_paired` is that
complementarity, and it is why no `Term.blt` survives into `mergeOneOriented_survivorUF`.

The skip branch is the same statement degenerately: `identityVals = some 1` puts the e-class
column inside `FDatabase.noConflict`'s comparison, so a collision runs no body exactly when the
two e-class columns are **equal**, and the row that stays carries the column the dropped row
carried. That clause of `Signature.MergeShape` is what rules out the one shape that would break
this — a width of zero would skip every collision and drop rows with no edge at all. -/

/-- `ordering-max old0 new0`, evaluated. -/
theorem eval_mergeEnv_maxE {sig : Signature} {o0 o1 n0 n1 : Term} :
    (maxE (.var "old0") (.var "new0")).eval sig (mergeEnv [o0, o1] [n0, n1])
      = some (if Term.blt n0 o0 then o0 else n0) := by
  rw [maxE]
  exact eval_ifGt eval_mergeEnv_old0 eval_mergeEnv_new0 eval_mergeEnv_old0 eval_mergeEnv_new0

/-- `ordering-min old0 new0`, evaluated — the complement of `eval_mergeEnv_maxE` at the same
comparison, which is the whole of why the two writes fit together. -/
theorem eval_mergeEnv_minE {sig : Signature} {o0 o1 n0 n1 : Term} :
    (minE (.var "old0") (.var "new0")).eval sig (mergeEnv [o0, o1] [n0, n1])
      = some (if Term.blt n0 o0 then n0 else o0) := by
  rw [minE]
  exact eval_ifGt eval_mergeEnv_old0 eval_mergeEnv_new0 eval_mergeEnv_new0 eval_mergeEnv_old0

/-- **`mergeBody`, run and computed.** `execActions_mergeBody_inv` says each column is one of
the two it chose between; this says *which*, which is what a reachability claim needs. -/
theorem execActions_mergeBody_eq {m m' : FDatabase} {o0 o1 n0 n1 : Term}
    (henv : m.env = mergeEnv [o0, o1] [n0, n1])
    (h : execActions m mergeBody = some m') :
    ∃ pf, m' = FDatabase.addRow ufName [if Term.blt n0 o0 then o0 else n0]
      [if Term.blt n0 o0 then n0 else o0, pf] m := by
  rw [mergeBody, execActions] at h
  obtain ⟨m₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  rw [execActions, Option.some.injEq] at h₂
  subst h₂
  obtain ⟨as, vs, has, hvs, rfl⟩ := execAction_set h₁
  rw [henv] at has hvs
  obtain ⟨mx, hmx, rfl⟩ := Expr.evalList_singleton has
  obtain ⟨mn, pf, hmn, -, rfl⟩ := Expr.evalList_pair hvs
  obtain rfl : mx = (if Term.blt n0 o0 then o0 else n0) :=
    Option.some.inj (hmx.symm.trans eval_mergeEnv_maxE)
  obtain rfl : mn = (if Term.blt n0 o0 then n0 else o0) :=
    Option.some.inj (hmn.symm.trans eval_mergeEnv_minE)
  exact ⟨pf, rfl⟩

/-- **`mergeResult`, run and computed.** The survivor's e-class column is the *same*
expression the edge points at, so no second comparison enters. -/
theorem evalList_mergeResult_eq {sig : Signature} {o0 o1 n0 n1 : Term} {vs : List Term}
    (h : Expr.evalList sig mergeResult (mergeEnv [o0, o1] [n0, n1]) = some vs) :
    ∃ lo, vs = [if Term.blt n0 o0 then n0 else o0, lo] := by
  rw [mergeResult] at h
  obtain ⟨mn, lo, hmn, -, rfl⟩ := Expr.evalList_pair h
  exact ⟨lo, by rw [Option.some.inj (hmn.symm.trans eval_mergeEnv_minE)]⟩

/-- **The two writes of one firing, paired.** The edge runs from one of the two colliding
e-class columns to the other, and the row that survives carries the *edge's own target*. Which
way round is the tie-break's business; that the two agree is not, and it is the whole content
of this lemma. -/
theorem mergeBody_result_paired {m m' : FDatabase} {o0 o1 n0 n1 : Term} {vs : List Term}
    (henv : m.env = mergeEnv [o0, o1] [n0, n1])
    (hbody : execActions m mergeBody = some m')
    (hres : Expr.evalList m'.sig mergeResult m'.env = some vs) :
    ∃ mx mn pf lo, ((mx = o0 ∧ mn = n0) ∨ (mx = n0 ∧ mn = o0)) ∧ vs = [mn, lo] ∧
      m' = FDatabase.addRow ufName [mx] [mn, pf] m := by
  obtain ⟨pf, rfl⟩ := execActions_mergeBody_eq henv hbody
  rw [FDatabase.addRow_env, henv] at hres
  obtain ⟨lo, rfl⟩ := evalList_mergeResult_eq hres
  by_cases hb : Term.blt n0 o0
  · exact ⟨o0, n0, pf, lo, Or.inl ⟨rfl, rfl⟩, by simp [hb], by simp [hb]⟩
  · exact ⟨n0, o0, pf, lo, Or.inr ⟨rfl, rfl⟩, by simp [hb], by simp [hb]⟩

/-- A row the firing leaves alone is a row of the state its `set` returns. -/
theorem mem_addRow_rows {d : FDatabase} {f : FnName} {as vs : List Term} {r : Row}
    (h : r ∈ d.rows) : r ∈ (FDatabase.addRow f as vs d).rows := by
  simp only [FDatabase.addRow, List.mem_dedup, List.mem_cons, FDatabase.mem_addTerm_rows]
  exact Or.inr (Or.inr h)

/-- **The edge a `set` writes is an `@UF` step at the state it returns.** `addRow` records the
entry term and every subterm of it, so the key column is a term the state holds and
`Database.out_self` reads the edge back. -/
theorem ufStep_addRow {d : FDatabase} {mx mn pf : Term} :
    (FDatabase.addRow ufName [mx] [mn, pf] d).toDatabase.UFStep mx mn := by
  have hsub : ∀ s ∈ (Term.app ufName [mx, mn, pf]).subtermList,
      s ∈ (FDatabase.addRow ufName [mx] [mn, pf] d).toDatabase.terms := by
    intro s hs
    rw [FDatabase.toDatabase_terms]
    exact FDatabase.mem_addTerm_terms.mpr (Or.inl hs)
  refine ⟨pf, Database.out_self (hsub _ ?_) (fun a ha => ?_)⟩
  · rw [Term.subtermList]; exact List.mem_cons_self
  · obtain rfl : a = mx := by simpa using ha
    refine hsub _ ?_
    rw [Term.subtermList]
    exact List.mem_cons_of_mem _ ((Term.mem_subtermListL _).mpr
      ⟨a, List.mem_cons_self, Term.self_mem_subterms a⟩)

/-- **`Database.UFStep` only grows with the term and equation lists**, which is what lets an
edge written at one point of a firing be read at the state the firing ends in. -/
theorem Database.UFStep.mono {d e : FDatabase} (ht : ∀ t ∈ d.terms, t ∈ e.terms)
    (he : ∀ p ∈ d.eqs, p ∈ e.eqs) {a b : Term} (h : d.toDatabase.UFStep a b) :
    e.toDatabase.UFStep a b := by
  obtain ⟨pf, bs, hcl, hmem⟩ := h
  refine ⟨pf, bs, hcl.mono ⟨fun p hp => ?_⟩, ?_⟩
  · rcases FDatabase.mem_toDatabase_eqs.mp hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
    · exact FDatabase.mem_toDatabase_eqs.mpr (Or.inl ⟨h₁, ht _ h₂⟩)
    · exact FDatabase.mem_toDatabase_eqs.mpr (Or.inr ⟨he _ h₁, ht _ h₂, ht _ h₃⟩)
  · rw [FDatabase.toDatabase_terms] at hmem ⊢
    exact ht _ hmem

/-- The edge, read at a state the firing's later writes reach: `addTerm` grows `terms` and no
component of a firing touches `eqs`. -/
theorem ufStep_of_addRow_mono {M E : FDatabase} {mx mn pf : Term}
    (ht : ∀ t ∈ (FDatabase.addRow ufName [mx] [mn, pf] M).terms, t ∈ E.terms)
    (he : ∀ p ∈ (FDatabase.addRow ufName [mx] [mn, pf] M).eqs, p ∈ E.eqs) :
    E.toDatabase.UFStep mx mn :=
  Database.UFStep.mono ht he ufStep_addRow

/-- **One merge firing keeps the entry it displaced `@UF`-reachable from a row it leaves.**

The claim checked at the one writer that can break it: whichever of the two colliding rows the
firing removes, the row it leaves at `r₂`'s key carries an e-class column that
`Database.UFReach` reaches from **both** of the colliding e-class columns, in the state the
firing itself returns. Reflexivity on the survivor's own side and one edge on the other — the
edge `mergeBody` wrote, `ordering-max` to `ordering-min`, in that same step.

`hne` is `FDatabase.mergeRound`'s own guard: the pass skips a row against itself, and without
it the deletion would take the survivor with it.

**This is the merge case of `execM_rebuildClosed`'s residue, and it is discharged.** It is not
the residue: what is left is the transport of this fact along a whole pass and across the rule
phases between passes, which is run-wide and is not a statement about one firing. -/
theorem mergeOneOriented_survivorUF {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2)
    (hne : r₁ ≠ r₂) (hfire : d.mergeOneOriented cl r₁ r₂ = some e) :
    ∃ n0 n1 o0 o1 v lo : Term, r₁.out = [n0, n1] ∧ r₂.out = [o0, o1] ∧ r₁.args = r₂.args ∧
      r₁.fn = r₂.fn ∧ (⟨r₂.fn, r₂.args, [v, lo]⟩ : Row) ∈ e.rows ∧
      e.toDatabase.UFReach n0 v ∧ e.toDatabase.UFReach o0 v := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨-, rfl, rfl, hout2, -, hid⟩ := hshape r₁.fn dc hdc body res hmergedc
    split at hfire
    next hg =>
      obtain ⟨⟨⟨hfn, hkeys⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hmg1 : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
      have hmg2 : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg1
      have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hkeys
      obtain ⟨-, hw1⟩ := hidx.width r₁ hmem₁ dc hdc hmg1
      obtain ⟨-, hw2⟩ := hidx.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg2
      rw [hout2] at hw1 hw2
      obtain ⟨n0, n1, hr1out⟩ := List.length_eq_two.mp hw1
      obtain ⟨o0, o1, hr2out⟩ := List.length_eq_two.mp hw2
      have hr₂ : (⟨r₂.fn, r₂.args, [o0, o1]⟩ : Row) = r₂ := by rw [← hr2out]
      have hwidth : (d.sig r₁.fn).bind (·.unchangedWidth mergeBody) = some 1 := by
        simp [hdc, FnDecl.unchangedWidth, hid]
      split at hfire
      next hskip =>
        rw [hwidth] at hskip
        have hn0o0 : n0 = o0 := by
          simp only [FDatabase.noConflict, hr1out, hr2out, List.take_succ_cons, List.take_zero,
            beq_iff_eq, List.cons.injEq, and_true] at hskip
          exact hskip
        rw [Option.some.injEq] at hfire
        subst hfire
        exact ⟨n0, n1, o0, o1, o0, o1, hr1out, hr2out, hargs, hfn,
          by rw [hr₂]; exact List.mem_filter.mpr ⟨hmem₂, by simpa using Ne.symm hne⟩,
          by rw [hn0o0]; exact .refl, .refl⟩
      next =>
        obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp hfire
        have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
            = mergeEnv [o0, o1] [n0, n1] := by rw [hr1out, hr2out]
        obtain ⟨mx, mn, pf, lo, hswap, rfl, rfl⟩ := mergeBody_result_paired henv hm hvs
        have hedge : e.toDatabase.UFStep mx mn := by
          refine ufStep_of_addRow_mono (M := { d with env := mergeEnv r₂.out r₁.out })
            (pf := pf) ?_ ?_
          · rw [← he]; exact fun t ht => FDatabase.mem_addTerm_of_mem ht
          · rw [← he]; exact fun p hp => hp
        have hrow : (⟨r₂.fn, r₂.args, [mn, lo]⟩ : Row) ∈ e.rows := by
          rw [← he]
          exact List.mem_map.mpr ⟨r₂, List.mem_filter.mpr
            ⟨FDatabase.mem_addTerm_rows.mpr (Or.inr (mem_addRow_rows hmem₂)),
              by simpa using Ne.symm hne⟩, by simp⟩
        refine ⟨n0, n1, o0, o1, mn, lo, hr1out, hr2out, hargs, hfn, hrow, ?_, ?_⟩
        · rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact .refl
          · exact hedge.toReach
        · rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hedge.toReach
          · exact .refl
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

/-- **The same, at whichever orientation `FDatabase.mergeOneWith` chose.** The conclusion is
symmetric in the two rows — both e-class columns reach the survivor's — so the orientation the
rebuild's `swapForCanon` picks costs nothing, and the surviving row can be named at `r₁`'s own
key because a firing's two keys are equal against a diagonal closure. -/
theorem mergeOneWith_survivorUF {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2)
    (hne : r₁ ≠ r₂) (hm : d.mergeOneWith cl r₁ r₂ = some e) :
    ∃ n0 n1 o0 o1 v lo : Term, r₁.out = [n0, n1] ∧ r₂.out = [o0, o1] ∧ r₁.args = r₂.args ∧
      r₁.fn = r₂.fn ∧ (⟨r₁.fn, r₁.args, [v, lo]⟩ : Row) ∈ e.rows ∧
      e.toDatabase.UFReach n0 v ∧ e.toDatabase.UFReach o0 v := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · obtain ⟨o0, o1, n0, n1, v, lo, hr2out, hr1out, hargs, hfn, hrow, ho, hn⟩ :=
      mergeOneOriented_survivorUF hshape hidx hcl (Ne.symm hne) (he ▸ hm)
    exact ⟨n0, n1, o0, o1, v, lo, hr1out, hr2out, hargs.symm, hfn.symm, hrow, hn, ho⟩
  · obtain ⟨n0, n1, o0, o1, v, lo, hr1out, hr2out, hargs, hfn, hrow, hn, ho⟩ :=
      mergeOneOriented_survivorUF hshape hidx hcl hne (he ▸ hm)
    exact ⟨n0, n1, o0, o1, v, lo, hr1out, hr2out, hargs, hfn, by rw [hfn, hargs]; exact hrow,
      hn, ho⟩


/-! ###### The pass, and the phase

`FDatabase.mergeRound_induction` is the rebuild and the two folds, factored; the invariant it
carries here is the one `mergeOneOriented_soundTerms` reads, plus `sig = d.sig` so that the two
*signature* hypotheses — which are statements about the pre-pass signature — apply at every
accumulator. `FDatabase.Inv.mergeRound_of_legalMerges` is what re-establishes
`FDatabase.IndexOk` at each step and `Signature.MergesLegal` is what it costs;
`Proofs/Counterexamples.lean`'s `cexSig_not_mergesLegal` is that hypothesis being load-bearing
rather than decorative. -/

/-- A state that asserts nothing asserts nothing non-reflexive. -/
theorem FDatabase.NoUnions.eqsRefl {d : FDatabase} (h : d.NoUnions) : d.EqsRefl := by
  intro p hp
  rw [h.eqs] at hp
  exact absurd hp (by simp)

/-- **One merge firing, at whichever orientation `mergeOneWith` chose.** -/
theorem mergeOneWith_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : d.SoundTerms src)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.SoundTerms src := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_soundTerms hshape hr hsc hidx hcl h (he ▸ hm)

/-- **A merge pass preserves the invariant.** The rebuild writes `rows` only, so it costs
nothing; every firing is `mergeOneWith_soundTerms`. -/
theorem mergeRound_soundTerms {src : Database} {d : FDatabase}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hn : d.NoUnions) (h : d.SoundTerms src) :
    d.mergeRound.SoundTerms src := by
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      d.mergeRound.SoundTerms src := by
    refine FDatabase.mergeRound_induction
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ x.SoundTerms src)
      ⟨hinv, rfl, hn, h⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        h.mono_terms (fun t ht => ht)⟩ ?_
    intro x y r₁ r₂ hx hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_soundTerms (by rw [hx.2.1]; exact hshape) hx.2.2.1.eqsRefl
      (FDatabase.SubtermClosed.of_wf hx.1.wf) hx.1.index hdiag hx.2.2.2 hy
  exact key.2.2.2

/-- **The whole merge phase preserves the invariant**, which is what `FDatabase.execCmdM` runs
after every top-level action and at the end of every round. -/
theorem mergeSaturateF_soundTerms {src : Database} : ∀ (n : Nat) {d e : FDatabase},
    Signature.MergeShape d.sig → Signature.MergesLegal d.sig → d.Inv → d.NoUnions →
    d.SoundTerms src → FDatabase.mergeSaturateF n d = some e → e.SoundTerms src
  | 0, d, e, _, _, _, _, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · exact absurd hrun (by simp)
  | n + 1, d, e, hshape, hlegal, hinv, hn, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_soundTerms n (by rw [hsig]; exact hshape)
          (by rw [hsig]; exact hlegal) (FDatabase.Inv.mergeRound_of_legalMerges hinv hlegal)
          (mergeRound_noUnions hn) (mergeRound_soundTerms hshape hlegal hinv hn h) hrun

/-! ###### The union-find the rows record, and its roots

`Database.UFStep` reads an `@UF` **entry**, so it ranges over every edge the run ever wrote,
superseded ones included — which is what `cxStale_not_rebuildClosedStrong` turns on. The rows
are the live edges, and they are what the rebuild rules read: `FDatabase.UFRowEdge` is one of
them, and `FDatabase.UFRowEdge.toUFStep` is the one-way bridge, since a row is an entry
(`FDatabase.IndexOk.entry`) and an entry is not a row.

**This is the residue's third obligation, and its well-foundedness half is what is proved
here.** Two facts about the row relation, from two hypotheses about it:

* `FDatabase.UFRowsDescend` — every edge runs `ordering-max ↦ ordering-min`, so it strictly
  descends `Term.blt` — bounds a path by the `@UF` rows below its start, and `rows` is a
  **finite list**: `exists_ufRowRoot` is the path reaching a point with no outgoing row.
* `FDatabase.UFRowsForest` — at most one outgoing edge per key — makes that point *unique*:
  `ufRowRoot_unique`.

Together they are what the leader form of the clause could not reach and the landing-site form
does: two readers of one id displaced along different paths end at the **same** root, and a
root is where `Database.RebuildClosed`'s `Database.Lands` has to point. Both hypotheses are
statements about one state and neither is proved here — `FDatabase.UFRowsDescend` is a run-wide
induction over the three writers of an `@UF` row (a source `union`, `mergeBody`, and
`pathCompressRule`, which composes two descents), and `FDatabase.UFRowsForest` is the merge
fixpoint below at `@UF`'s own table, where the per-key count is not a measure because
`mergeBody`'s own write lands there. -/

namespace FDatabase

/-- Whether every key column of `r` is at or below `a` in `Term.blt`. -/
def rowKeyLe (a : Term) (r : Row) : Bool :=
  r.args.all fun k => Term.blt k a || k == a

/-- **One `@UF` row that moves**, read off `rows` rather than off `terms`. -/
def UFRowEdge (d : FDatabase) (a b : Term) : Prop :=
  (∃ pf, (⟨ufName, [a], [b, pf]⟩ : Row) ∈ d.rows) ∧ b ≠ a

/-- Reachability along them. -/
def UFRowReach (d : FDatabase) (a b : Term) : Prop :=
  Relation.ReflTransGen d.UFRowEdge a b

/-- A point with no outgoing row. -/
def UFRowRoot (d : FDatabase) (a : Term) : Prop := ∀ b, ¬ d.UFRowEdge a b

/-- Every edge descends. -/
def UFRowsDescend (d : FDatabase) : Prop :=
  ∀ a b, d.UFRowEdge a b → Term.blt b a = true

/-- Every key has at most one outgoing edge. -/
def UFRowsForest (d : FDatabase) : Prop :=
  ∀ a b c, d.UFRowEdge a b → d.UFRowEdge a c → b = c

theorem UFRowEdge.measure_lt {d : FDatabase} (hdes : d.UFRowsDescend) {a b : Term}
    (h : d.UFRowEdge a b) :
    (d.rows.filter (rowKeyLe b)).length < (d.rows.filter (rowKeyLe a)).length := by
  have hba : Term.blt b a = true := hdes a b h
  have hsub : List.Sublist (d.rows.filter (rowKeyLe b)) (d.rows.filter (rowKeyLe a)) := by
    refine List.monotone_filter_right _ (fun r hr => ?_)
    simp only [rowKeyLe, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hr ⊢
    intro k hk
    rcases hr k hk with hkb | rfl
    · exact Or.inl (Term.blt_trans k b a hkb hba)
    · exact Or.inl hba
  obtain ⟨pf, hmem⟩ := h.1
  have hin : (⟨ufName, [a], [b, pf]⟩ : Row) ∈ d.rows.filter (rowKeyLe a) :=
    List.mem_filter.mpr ⟨hmem, by simp [rowKeyLe]⟩
  have hout : (⟨ufName, [a], [b, pf]⟩ : Row) ∉ d.rows.filter (rowKeyLe b) := by
    intro hc
    have hk := (List.mem_filter.mp hc).2
    simp only [rowKeyLe, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.mem_singleton] at hk
    rcases hk a rfl with hab | hab
    · exact absurd hab (by rw [Term.blt_asymm b a hba]; simp)
    · exact h.2 hab.symm
  rcases Nat.lt_or_ge (d.rows.filter (rowKeyLe b)).length
      (d.rows.filter (rowKeyLe a)).length with hlt | hge
  · exact hlt
  · exact absurd (hsub.eq_of_length_le hge ▸ hin) hout

/-- **Every key reaches a root**: descent bounds a path by the `@UF` rows below its start. -/
theorem exists_ufRowRoot {d : FDatabase} (hdes : d.UFRowsDescend) (a : Term) :
    ∃ r, d.UFRowReach a r ∧ d.UFRowRoot r := by
  have key : ∀ n : Nat, ∀ a : Term, (d.rows.filter (rowKeyLe a)).length = n →
      ∃ r, d.UFRowReach a r ∧ d.UFRowRoot r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      by_cases hroot : d.UFRowRoot a
      · exact ⟨a, .refl, hroot⟩
      · obtain ⟨b, hb⟩ : ∃ b, d.UFRowEdge a b := by
          simpa [UFRowRoot, not_forall] using hroot
        obtain ⟨r, hr, hrr⟩ := ih _ (ha ▸ hb.measure_lt hdes) b rfl
        exact ⟨r, .head hb hr, hrr⟩
  exact key _ a rfl

/-- A root reaches nothing but itself. -/
theorem UFRowRoot.reach_eq {d : FDatabase} {a b : Term} (hr : d.UFRowRoot a)
    (h : d.UFRowReach a b) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) (hr _)

/-- **And the root is unique**, which is what makes two readers displaced along different
paths land on one point. -/
theorem ufRowRoot_unique {d : FDatabase} (hf : d.UFRowsForest) {a r s : Term}
    (hr : d.UFRowReach a r) (hrr : d.UFRowRoot r) (hs : d.UFRowReach a s)
    (hsr : d.UFRowRoot s) : r = s := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hrr.reach_eq hs).symm
  | head hstep _ ih =>
      rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨c, hc, hcs⟩
      · exact absurd hstep (hsr _)
      · obtain rfl : c = _ := hf _ _ _ hc hstep
        exact ih hcs

/-- **Descent along a whole path**, which is what says a path never returns. -/
theorem UFRowReach.le {d : FDatabase} (hdes : d.UFRowsDescend) {a b : Term}
    (h : d.UFRowReach a b) : b = a ∨ Term.blt b a = true := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hr hstep ih =>
      rcases ih with rfl | hlt
      · exact Or.inr (hdes _ _ hstep)
      · exact Or.inr (Term.blt_trans _ _ _ (hdes _ _ hstep) hlt)

/-- **A row edge is an entry edge**: `FDatabase.IndexOk.entry` reads the row back through
`Database.Out`, which is what `Database.UFStep` is stated over. -/
theorem UFRowEdge.toUFStep {d : FDatabase} (hidx : d.IndexOk)
    (hmg : d.sig.mergeOf ufName ≠ none) {a b : Term} (h : d.UFRowEdge a b) :
    d.toDatabase.UFStep a b := by
  obtain ⟨pf, hmem⟩ := h.1
  exact ⟨pf, hidx.entry ⟨ufName, [a], [b, pf]⟩ hmem hmg⟩

@[inherit_doc UFRowEdge.toUFStep]
theorem UFRowReach.toUFReach {d : FDatabase} (hidx : d.IndexOk)
    (hmg : d.sig.mergeOf ufName ≠ none) {a b : Term} (h : d.UFRowReach a b) :
    d.toDatabase.UFReach a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.toUFStep hidx hmg)

end FDatabase

/-! ###### The merge phase's own fixpoint

`FDatabase.mergeSaturateF` returns a **settled** state — `mergeSaturateF_settled` — and
`FDatabase.settled` compares the row list, so a pass that would change it is a pass the state
does not take. That is enough to read a *negative* fact off the fixpoint, and the fact is the
one `ufDecl`'s and `viewDecl`'s `identityVals := some 1` was put there for: at a fixpoint a
view key carries **at most one row** (`row_unique_of_settled`).

The measure is the row count at one key (`rowAt`), and the three things that make it one:

* `FDatabase.mergeOneOriented` deletes the arriving row whether or not the collision runs a
  body, and the row it overwrites keeps its own key — `mergeOneOriented_rows_shape` is that
  factored, and `countP_of_rows_shape` reads the count and the surviving rows off it;
* the only row `mergeBody` writes is an `@UF` row and the only rows `FDatabase.addTerm` writes
  are a constructor's, so no firing anywhere adds a row at a **view** key;
* at a diagonal closure the rebuild moves nothing (`rebuild_diag`), so the pass fires on the
  rows it started with, deduplicated.

`foldl_mark` is the shape of the argument: the pass reaches the colliding pair, and by the time
it does either the count has already dropped or the firing goes through and drops it.

**Why the claim is about a view key and not about `@UF`'s.** `mergeBody` writes at
`ordering-max` of the two colliding e-class columns, which for a *view* collision is an
arbitrary id — so the count at an `@UF` key can grow inside the very pass that shrinks a view
key's. Closing `FDatabase.UFRowsForest` this way needs a lexicographic measure instead: the
view count first, then a rank of the `@UF` key, which is where `FDatabase.UFRowsDescend` is
what makes the added row's key strictly smaller.

**And the body has to run.** `mergeBody` mints `@Trans (@Sym _) _`, so `Expr.eval` reads
`Signature.IsCtor` at `@Sym` and `@Trans`; a signature that does not declare them leaves every
collision standing, which is why `mergeOneWith_isSome_of_collide` carries those two hypotheses
rather than deriving them. The prelude declares both (`proofDecls`). -/

/-- A row of `f`'s table at the key tuple `as`: what a collision is compared at. -/
def rowAt (f : FnName) (as : List Term) (r : Row) : Bool := r.fn == f && r.args == as

/-- **Deleting one counted row strictly drops the count.** -/
theorem countP_filter_ne_lt {p : Row → Bool} {l : List Row} {a : Row}
    (ha : a ∈ l) (hp : p a = true) :
    (l.filter fun r => r ≠ a).countP p < l.countP p := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons x l ih =>
      have hle : ((l.filter fun r => r ≠ a).countP p) ≤ l.countP p :=
        List.filter_sublist.countP_le
      rcases eq_or_ne x a with rfl | hxa
      · rw [List.filter_cons_of_neg (by simp), List.countP_cons, if_pos hp]
        omega
      · rw [List.filter_cons_of_pos (by simpa using hxa), List.countP_cons, List.countP_cons]
        have hmem : a ∈ l := by
          rcases List.mem_cons.mp ha with rfl | h
          · exact absurd rfl hxa
          · exact h
        have := ih hmem
        omega

/-- **A map that moves no key changes no count**, which is what makes the overwrite a merge
firing performs invisible to a per-key count. -/
theorem countP_map_of_key {p : Row → Bool} {g : Row → Row} (hg : ∀ r, p (g r) = p r)
    (l : List Row) : (l.map g).countP p = l.countP p := by
  rw [List.countP_map]
  exact List.countP_congr fun r _ => by simpa using hg r

/-- `FDatabase.addTerm` writes only constructor rows, so it moves no merge function's key
count. -/
theorem countP_addTerm_le {d : FDatabase} {t : Term} {f : FnName} {as : List Term}
    (hmg : d.sig.mergeOf f ≠ none) :
    (d.addTerm t).rows.countP (rowAt f as) ≤ d.rows.countP (rowAt f as) := by
  have hsub : List.Sublist (d.addTerm t).rows (Term.ctorRowList d.sig t ++ d.rows) :=
    List.dedup_sublist _
  have hle := hsub.countP_le (p := rowAt f as)
  rw [List.countP_append] at hle
  have hzero : (Term.ctorRowList d.sig t).countP (rowAt f as) = 0 := by
    rw [List.countP_eq_zero]
    intro r hr hrow
    simp only [rowAt, Bool.and_eq_true, beq_iff_eq] at hrow
    exact hmg (hrow.1 ▸ (FDatabase.mem_ctorRowList hr).2.1)
  omega

/-- And `FDatabase.addRow` moves only its own function's. -/
theorem countP_addRow_le {d : FDatabase} {g : FnName} {bs vs : List Term} {f : FnName}
    {as : List Term} (hmg : d.sig.mergeOf f ≠ none) (hgf : g ≠ f) :
    (FDatabase.addRow g bs vs d).rows.countP (rowAt f as) ≤ d.rows.countP (rowAt f as) := by
  set t : Term := .app g (bs ++ vs) with ht
  have hsub : List.Sublist (FDatabase.addRow g bs vs d).rows
      ((⟨g, bs, vs⟩ : Row) :: (d.addTerm t).rows) := List.dedup_sublist _
  have hle := hsub.countP_le (p := rowAt f as)
  rw [List.countP_cons, if_neg (by simp [rowAt, hgf])] at hle
  have := countP_addTerm_le (d := d) (t := t) (f := f) (as := as) hmg
  omega

/-- **`mergeBody` writes an `@UF` row and nothing else**, so a view function's key count comes
out of the body untouched. -/
theorem countP_mergeBody_le {m m' : FDatabase} {o0 o1 n0 n1 : Term} {f : FnName}
    {as : List Term} (henv : m.env = mergeEnv [o0, o1] [n0, n1])
    (h : execActions m mergeBody = some m') (hmg : m.sig.mergeOf f ≠ none) (hfne : f ≠ ufName) :
    m'.rows.countP (rowAt f as) ≤ m.rows.countP (rowAt f as) := by
  obtain ⟨mx, mn, a, b, -, -, -, -, rfl⟩ := execActions_mergeBody_inv henv h
  exact countP_addRow_le hmg (Ne.symm hfne)

/-- **What one merge firing does to the row list**, factored so that the per-key counts and
the rows it leaves alone come out of one unfolding: the two colliding rows sit at one key,
the row list it rewrites holds every row the pass had, and the rewrite drops `r₁` and moves
no key. -/
theorem mergeOneOriented_rows_shape {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2)
    (hfire : d.mergeOneOriented cl r₁ r₂ = some e) :
    r₁ ∈ d.rows ∧ r₂ ∈ d.rows ∧ r₁.fn = r₂.fn ∧ r₁.args = r₂.args ∧
      ∃ (mid : List Row) (g : Row → Row),
        e.rows = (mid.filter fun r => r ≠ r₁).map g ∧
        (∀ r, (g r).fn = r.fn ∧ (g r).args = r.args) ∧
        (∀ r, r ≠ r₂ → g r = r) ∧
        (∀ r ∈ d.rows, r ∈ mid) ∧
        (∀ (f : FnName) (as : List Term), d.sig.mergeOf f ≠ none → f ≠ ufName →
          mid.countP (rowAt f as) ≤ d.rows.countP (rowAt f as)) := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨-, rfl, rfl, hout2, -, hid⟩ := hshape r₁.fn dc hdc body res hmergedc
    split at hfire
    next hg =>
      obtain ⟨⟨⟨hfn, hkeys⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hkeys
      refine ⟨hmem₁, hmem₂, hfn, hargs, ?_⟩
      split at hfire
      next =>
        rw [Option.some.injEq] at hfire
        subst hfire
        exact ⟨d.rows, id, by simp, fun r => ⟨rfl, rfl⟩, fun r _ => rfl, fun r hr => hr,
          fun f as _ _ => Nat.le_refl _⟩
      next =>
        obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp hfire
        have hmg1 : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
        have hmg2 : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg1
        obtain ⟨-, hw1⟩ := hidx.width r₁ hmem₁ dc hdc hmg1
        obtain ⟨-, hw2⟩ := hidx.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg2
        rw [hout2] at hw1 hw2
        obtain ⟨n0, n1, hr1out⟩ := List.length_eq_two.mp hw1
        obtain ⟨o0, o1, hr2out⟩ := List.length_eq_two.mp hw2
        have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
            = mergeEnv [o0, o1] [n0, n1] := by rw [hr1out, hr2out]
        obtain ⟨mx, mn, aa, bb, -, -, -, -, hmeq⟩ := execActions_mergeBody_inv henv hm
        have hsig : m.sig = d.sig := by rw [hmeq]; rfl
        have hmrows : ∀ r ∈ d.rows, r ∈ m.rows := by
          intro r hr
          rw [hmeq]
          exact mem_addRow_rows hr
        refine ⟨(m.addTerm (.app r₂.fn (r₂.args ++ vs))).rows,
          fun r => if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r, by rw [← he], ?_, ?_, ?_, ?_⟩
        · intro r
          by_cases hr : r = r₂
          · subst hr; simp
          · simp [hr]
        · intro r hr; simp [hr]
        · intro r hr
          exact FDatabase.mem_addTerm_rows.mpr (Or.inr (hmrows r hr))
        · intro f as hmgf hfnef
          refine le_trans (countP_addTerm_le (by rw [hsig]; exact hmgf)) ?_
          rw [hmeq]
          exact countP_addRow_le hmgf (Ne.symm hfnef)
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

/-- The three consequences of `mergeOneOriented_rows_shape`, read off the factored shape. -/
private theorem countP_of_rows_shape {d e : FDatabase} {s₁ s₂ : Row} {f : FnName}
    {as : List Term} {mid : List Row} {g : Row → Row}
    (hkey : s₁.fn = s₂.fn) (hkarg : s₁.args = s₂.args)
    (he : e.rows = (mid.filter fun r => r ≠ s₁).map g)
    (hgk : ∀ r, (g r).fn = r.fn ∧ (g r).args = r.args)
    (hgid : ∀ r, r ≠ s₂ → g r = r)
    (hs₁ : s₁ ∈ mid) (hmid : ∀ r ∈ d.rows, r ∈ mid)
    (hcnt : mid.countP (rowAt f as) ≤ d.rows.countP (rowAt f as)) :
    e.rows.countP (rowAt f as) ≤ d.rows.countP (rowAt f as) ∧
      (rowAt f as s₁ = true → e.rows.countP (rowAt f as) < d.rows.countP (rowAt f as)) ∧
      (rowAt f as s₁ = false → ∀ r ∈ d.rows, rowAt f as r = true → r ∈ e.rows) := by
  have hmap : ∀ r, rowAt f as (g r) = rowAt f as r := by
    intro r; simp [rowAt, (hgk r).1, (hgk r).2]
  have hrw : e.rows.countP (rowAt f as) = (mid.filter fun r => r ≠ s₁).countP (rowAt f as) := by
    rw [he]; exact countP_map_of_key hmap _
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (hrw ▸ List.filter_sublist.countP_le) hcnt
  · intro hp
    exact lt_of_lt_of_le (hrw ▸ countP_filter_ne_lt hs₁ hp) hcnt
  · intro hp r hr hpr
    have hne₁ : r ≠ s₁ := fun h => by rw [h, hp] at hpr; exact absurd hpr (by simp)
    have hne₂ : r ≠ s₂ := fun h => by
      rw [h, show rowAt f as s₂ = rowAt f as s₁ by simp [rowAt, hkey, hkarg], hp] at hpr
      exact absurd hpr (by simp)
    rw [he, ← hgid r hne₂]
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hmid r hr, by simpa using hne₁⟩)

/-- `hi_pf`, evaluated. -/
theorem eval_mergeEnv_hiPfE {sig : Signature} {o0 o1 n0 n1 : Term} :
    hiPfE.eval sig (mergeEnv [o0, o1] [n0, n1])
      = some (if Term.blt n0 o0 then o1 else n1) := by
  rw [hiPfE]
  exact eval_ifGt eval_mergeEnv_old0 eval_mergeEnv_new0 eval_mergeEnv_old1 eval_mergeEnv_new1

/-- `lo_pf`, evaluated. -/
theorem eval_mergeEnv_loPfE {sig : Signature} {o0 o1 n0 n1 : Term} :
    loPfE.eval sig (mergeEnv [o0, o1] [n0, n1])
      = some (if Term.blt o0 n0 then o1 else n1) := by
  rw [loPfE]
  exact eval_ifGt eval_mergeEnv_new0 eval_mergeEnv_old0 eval_mergeEnv_old1 eval_mergeEnv_new1

/-- **The proof node `mergeBody` mints, evaluated.** This is the one place the body reads the
signature: `@Sym` and `@Trans` have to be declared, and a signature that does not declare them
leaves every collision standing. -/
theorem eval_mergeEnv_mergePf {sig : Signature} {o0 o1 n0 n1 : Term}
    (hsy : sig.IsCtor symName) (htr : sig.IsCtor transName) :
    (transE (symE hiPfE) loPfE).eval sig (mergeEnv [o0, o1] [n0, n1])
      = some (.app transName [.app symName [if Term.blt n0 o0 then o1 else n1],
          if Term.blt o0 n0 then o1 else n1]) := by
  rw [transE, Expr.eval_app_ctor (by decide) htr, symE]
  simp only [Expr.evalList, Expr.eval_app_ctor (by decide) hsy, eval_mergeEnv_hiPfE,
    eval_mergeEnv_loPfE, Option.map_some, Option.bind_some]

/-- **`mergeBody` runs.** -/
theorem execActions_mergeBody_isSome {m : FDatabase} {o0 o1 n0 n1 : Term}
    (henv : m.env = mergeEnv [o0, o1] [n0, n1]) (hsy : m.sig.IsCtor symName)
    (htr : m.sig.IsCtor transName) : (execActions m mergeBody).isSome = true := by
  rw [mergeBody, execActions, execAction, henv]
  simp only [Expr.evalList, eval_mergeEnv_maxE, eval_mergeEnv_minE,
    eval_mergeEnv_mergePf hsy htr, Option.map_some, Option.bind_some, execActions]
  rfl

/-- **And so does `mergeResult`.** -/
theorem evalList_mergeResult_isSome {sig : Signature} {o0 o1 n0 n1 : Term} :
    (Expr.evalList sig mergeResult (mergeEnv [o0, o1] [n0, n1])).isSome = true := by
  rw [mergeResult]
  simp only [Expr.evalList, eval_mergeEnv_minE, eval_mergeEnv_loPfE, Option.map_some,
    Option.bind_some]
  rfl

/-- A property every step preserves is a property of the fold. -/
theorem foldl_pres {α β : Type _} {f : β → α → β} {P : β → Prop}
    (h : ∀ b y, P b → P (f b y)) : ∀ (l : List α) (b : β), P b → P (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons y l ih => intro b hb; exact ih _ (h b y hb)

/-- **A fold with one marked element.** `P` is carried up to the mark, the mark turns it into
`Q`, and `Q` is carried the rest of the way — which is what says a pass that reaches one
particular colliding pair has done something by the time it ends. -/
theorem foldl_mark {α β : Type _} {f : β → α → β} {P Q : β → Prop} {a : α}
    (hP : ∀ b y, P b → P (f b y)) (hQ : ∀ b y, Q b → Q (f b y))
    (hPQ : ∀ b, P b → Q (f b a)) :
    ∀ {l : List α}, a ∈ l → ∀ (b : β), P b → Q (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro ha; exact absurd ha (by simp)
  | cons y l ih =>
      intro ha b hb
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact foldl_pres hQ l _ (hPQ b hb)
      · exact ih ha' _ (hP b y hb)

/-- **One merge firing, at a per-key count**, at whichever orientation `mergeOneWith` chose:
the count never grows, it strictly drops if the firing is at that key, and a firing at any
other key leaves that key's rows exactly where they were. -/
theorem mergeOneWith_countP {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    {f : FnName} {as : List Term}
    (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2)
    (hmg : d.sig.mergeOf f ≠ none) (hfne : f ≠ ufName)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) :
    e.rows.countP (rowAt f as) ≤ d.rows.countP (rowAt f as) ∧
      (rowAt f as r₁ = true → e.rows.countP (rowAt f as) < d.rows.countP (rowAt f as)) ∧
      (rowAt f as r₁ = false → ∀ r ∈ d.rows, rowAt f as r = true → r ∈ e.rows) := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · obtain ⟨hm₂, -, hfn, hargs, mid, g, heq, hgk, hgid, hmid, hcnt⟩ :=
      mergeOneOriented_rows_shape hshape hidx hcl (he ▸ hm)
    have hsame : rowAt f as r₂ = rowAt f as r₁ := by simp [rowAt, hfn, hargs]
    obtain ⟨h1, h2, h3⟩ := countP_of_rows_shape (d := d) hfn hargs heq hgk hgid
      (hmid r₂ hm₂) hmid (hcnt f as hmg hfne)
    exact ⟨h1, fun hp => h2 (hsame.trans hp), fun hp => h3 (hsame.trans hp)⟩
  · obtain ⟨hm₁, -, hfn, hargs, mid, g, heq, hgk, hgid, hmid, hcnt⟩ :=
      mergeOneOriented_rows_shape hshape hidx hcl (he ▸ hm)
    exact countP_of_rows_shape (d := d) hfn hargs heq hgk hgid (hmid r₁ hm₁) hmid
      (hcnt f as hmg hfne)

/-- A pair of a list zipped with itself is diagonal. -/
private theorem mem_zip_self {α : Type _} : ∀ {xs : List α} {q : α × α},
    q ∈ xs.zip xs → q.1 = q.2 ∧ q.1 ∈ xs
  | [], _, h => by simp at h
  | x :: xs, q, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨rfl, List.mem_cons_self⟩
      · exact ⟨(mem_zip_self h).1, List.mem_cons_of_mem _ (mem_zip_self h).2⟩

/-- A key tuple is congruent to itself as soon as the closure records its columns. -/
theorem congrKeys_self {cl : Finset (Term × Term)} {as : List Term}
    (h : ∀ a ∈ as, (a, a) ∈ cl) : FDatabase.congrKeys cl as as = true := by
  simp only [FDatabase.congrKeys, FDatabase.congrTuple, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, decide_eq_true_eq]
  intro q hq
  obtain ⟨heq, hmem⟩ := mem_zip_self hq
  rw [show q = (q.1, q.1) from Prod.ext rfl heq.symm]
  exact h q.1 hmem

/-- **A collision at one key fires.** `swapForCanon` declines to orient a pair at equal keys,
so the pair reaches `mergeOneOriented` in the order it was given; the collision that runs no
body drops the arriving row outright, and the one that runs `mergeBody` runs it because the
signature declares `@Sym` and `@Trans` — a signature that did not would leave the collision
standing. -/
theorem mergeOneWith_isSome_of_collide {cl : Finset (Term × Term)} {d : FDatabase} {r₁ r₂ : Row}
    {dc : FnDecl} (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk)
    (hsy : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName)
    (hdecl : d.sig r₁.fn = some dc) (hdc : dc.merge = some (.merge mergeBody mergeResult))
    (hm₁ : r₁ ∈ d.rows) (hm₂ : r₂ ∈ d.rows) (hfn : r₁.fn = r₂.fn) (hargs : r₁.args = r₂.args)
    (hkeys : FDatabase.congrKeys cl r₁.args r₂.args = true) :
    (d.mergeOneWith cl r₁ r₂).isSome = true := by
  obtain ⟨-, -, -, hoa, -, hiv⟩ := hshape r₁.fn dc hdecl mergeBody mergeResult hdc
  have hmg : d.sig.mergeOf r₁.fn = some (.merge mergeBody mergeResult) := by
    rw [Signature.mergeOf, hdecl, Option.bind_some, hdc]
  have hmg2 : d.sig.mergeOf r₂.fn = some (.merge mergeBody mergeResult) := by
    rw [← hfn]; exact hmg
  have hswap : FDatabase.swapForCanon cl d r₁ r₂ = false := by
    rw [FDatabase.swapForCanon, hmg]
    simp [hargs]
  obtain ⟨-, hw1⟩ := hidx.width r₁ hm₁ dc hdecl (by rw [hmg]; simp)
  obtain ⟨-, hw2⟩ := hidx.width r₂ hm₂ dc (by rw [← hfn]; exact hdecl) (by rw [hmg2]; simp)
  rw [hoa] at hw1 hw2
  obtain ⟨n0, n1, hr1out⟩ := List.length_eq_two.mp hw1
  obtain ⟨o0, o1, hr2out⟩ := List.length_eq_two.mp hw2
  have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
      = mergeEnv [o0, o1] [n0, n1] := by rw [hr1out, hr2out]
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp
    (execActions_mergeBody_isSome (m := { d with env := mergeEnv r₂.out r₁.out }) henv hsy htr)
  obtain ⟨mx, mn, aa, bb, -, -, -, -, hmeq⟩ := execActions_mergeBody_inv henv hm
  have hmenv : m.env = mergeEnv [o0, o1] [n0, n1] := by
    rw [hmeq, FDatabase.addRow_env]; exact henv
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp
    (evalList_mergeResult_isSome (sig := m.sig) (o0 := o0) (o1 := o1) (n0 := n0) (n1 := n1))
  have hguard : (decide (r₁.fn = r₂.fn) && FDatabase.congrKeys cl r₁.args r₂.args
      && d.rows.contains r₁ && d.rows.contains r₂) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
    exact ⟨⟨⟨hfn, hkeys⟩, hm₁⟩, hm₂⟩
  rw [FDatabase.mergeOneWith]
  rw [if_neg (by simp [hswap] : ¬ FDatabase.swapForCanon cl d r₁ r₂ = true)]
  rw [FDatabase.mergeOneOriented]
  simp only [hmg]
  rw [if_pos hguard]
  split
  · simp
  · have hvs' : Expr.evalList m.sig mergeResult m.env = some vs := by rw [hmenv]; exact hvs
    rw [hm, Option.bind_some, hvs']
    simp

namespace FDatabase

/-- **`FDatabase.mergeSaturateF` returns a state a further pass leaves alone**, which is the
branch condition it returned from. -/
theorem mergeSaturateF_settled : ∀ (n : Nat) {d e : FDatabase},
    FDatabase.mergeSaturateF n d = some e → e.settled = true
  | 0, d, e, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · next hs => rw [Option.some.injEq] at h; exact h ▸ hs
      · exact absurd h (by simp)
  | n + 1, d, e, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · next hs => rw [Option.some.injEq] at h; exact h ▸ hs
      · exact mergeSaturateF_settled n h

/-- The row list a settled state's next pass leaves. -/
theorem settled_rows {d : FDatabase} (h : d.settled = true) :
    d.mergeRound.rows = d.rows := by
  simp only [FDatabase.settled, FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- **A diagonal closure canonicalises nothing.** -/
theorem canonOf_diag {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2)
    (ts : List Term) (t : Term) : canonOf cl ts t = t := by
  rcases canonOf_spec (cl := cl) (ts := ts) (t := t) with h | ⟨-, h | h⟩
  · exact h
  · exact h
  · exact (hcl _ h).symm

@[inherit_doc canonOf_diag]
theorem canonKeyOf_diag {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2)
    (ts as : List Term) : canonKeyOf cl ts as = as := by
  rw [canonKeyOf, List.map_congr_left (g := id) fun a _ => canonOf_diag hcl ts a, List.map_id]

theorem rebuildRow_diag {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2)
    {d : FDatabase} (r : Row) : d.rebuildRow cl r = r := by
  rw [rebuildRow]
  split
  · rw [canonKeyOf_diag hcl]
  · rfl

theorem rebuild_diag {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2)
    {d : FDatabase} : (rebuild cl d).rows = d.rows.dedup := by
  have hmap : (d.rows.map fun r => (d.rebuildRow cl r, r)) = d.rows.map fun r => (r, r) :=
    List.map_congr_left fun r _ => by rw [rebuildRow_diag hcl]
  change (((d.rows.map fun r => (d.rebuildRow cl r, r)).filter fun p => p.1 != p.2).map Prod.fst
      ++ ((d.rows.map fun r => (d.rebuildRow cl r, r)).filter fun p => p.1 == p.2).map
        Prod.fst).dedup = d.rows.dedup
  rw [hmap]
  have h1 : ((d.rows.map fun r => (r, r)).filter fun p => p.1 != p.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
    simp
  have h2 : ((d.rows.map fun r => (r, r)).filter fun p => p.1 == p.2)
      = d.rows.map fun r => (r, r) := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
    simp
  rw [h1, h2, List.map_nil, List.nil_append,
    show ((d.rows.map fun r => (r, r)).map Prod.fst) = d.rows from by
      rw [List.map_map]; exact List.map_id _]

/-- The invariant a pass carries up to the marked collision: the count has not grown, and
either it has already dropped or both rows are still there. -/
private def MarkPre (d : FDatabase) (f : FnName) (as : List Term) (r₁ r₂ : Row)
    (x : FDatabase) : Prop :=
  x.Inv ∧ x.sig = d.sig ∧ x.rows.countP (rowAt f as) ≤ d.rows.countP (rowAt f as) ∧
    (x.rows.countP (rowAt f as) < d.rows.countP (rowAt f as) ∨ (r₁ ∈ x.rows ∧ r₂ ∈ x.rows))

/-- And the one it carries after it: the count has dropped. -/
private def MarkPost (d : FDatabase) (f : FnName) (as : List Term) (x : FDatabase) : Prop :=
  x.Inv ∧ x.sig = d.sig ∧ x.rows.countP (rowAt f as) < d.rows.countP (rowAt f as)

/-- **A merge pass drops a view key's row count when that key carries two rows.**

The pass reaches the pair, and by the time it does either the count has already dropped or
the firing goes through (`mergeOneWith_isSome_of_collide`) and deletes the arriving row.
Every other firing leaves this key alone: the row a firing deletes and the row it overwrites
share its own key, and the only row `mergeBody` adds is an `@UF` row — which is why the claim
is about a **view** key and not about `@UF`'s own table. -/
theorem mergeRound_countP_lt {d : FDatabase} {f : FnName} {as : List Term} {r₁ r₂ : Row}
    {dc : FnDecl}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hcl : ∀ p ∈ d.closureF, p.1 = p.2)
    (hsy : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName)
    (hdecl : d.sig f = some dc) (hdc : dc.merge = some (.merge mergeBody mergeResult))
    (hfne : f ≠ ufName) (hrefl : ∀ a ∈ as, (a, a) ∈ d.closureF)
    (hm₁ : r₁ ∈ d.rows) (hm₂ : r₂ ∈ d.rows)
    (hk₁ : rowAt f as r₁ = true) (hk₂ : rowAt f as r₂ = true) (hne : r₁ ≠ r₂) :
    d.mergeRound.rows.countP (rowAt f as) < d.rows.countP (rowAt f as) := by
  obtain ⟨hfn₁, ha₁⟩ : r₁.fn = f ∧ r₁.args = as := by
    simpa only [rowAt, Bool.and_eq_true, beq_iff_eq] using hk₁
  obtain ⟨hfn₂, ha₂⟩ : r₂.fn = f ∧ r₂.args = as := by
    simpa only [rowAt, Bool.and_eq_true, beq_iff_eq] using hk₂
  have hmg : d.sig.mergeOf f = some (.merge mergeBody mergeResult) := by
    rw [Signature.mergeOf, hdecl, Option.bind_some, hdc]
  have hmgf : d.sig.mergeOf f ≠ none := by rw [hmg]; simp
  have hhas : d.hasMergeRow = true := by
    rw [FDatabase.hasMergeRow, List.any_eq_true]
    exact ⟨r₁, hm₁, by rw [hfn₁, hmg]⟩
  have hkeys : FDatabase.congrKeys d.closureF r₁.args r₂.args = true := by
    rw [ha₁, ha₂]; exact congrKeys_self hrefl
  have hlrows : (FDatabase.rebuild d.closureF d).rows = d.rows.dedup := rebuild_diag hcl
  have hround : d.mergeRound = (FDatabase.rebuild d.closureF d).rows.foldl
      (fun acc s₁ => (FDatabase.rebuild d.closureF d).rows.foldl
        (fun acc' s₂ => if s₁ == s₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' s₁ s₂ with
            | some acc'' => acc''
            | none => acc') acc) (FDatabase.rebuild d.closureF d) := by
    rw [FDatabase.mergeRound]
    simp only [hhas, Bool.not_true, Bool.false_eq_true, if_false]
    rfl
  -- One firing, at each of the two invariants.
  have hstepQ : ∀ (x y : FDatabase) (s₁ s₂ : Row), MarkPost d f as x →
      FDatabase.mergeOneWith d.closureF x s₁ s₂ = some y → MarkPost d f as y := by
    intro x y s₁ s₂ hx hy
    obtain ⟨hle, -, -⟩ := mergeOneWith_countP (as := as) (by rw [hx.2.1]; exact hshape)
      hx.1.index hcl (by rw [hx.2.1]; exact hmgf) hfne hy
    exact ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1, lt_of_le_of_lt hle hx.2.2⟩
  have hstepP : ∀ (x y : FDatabase) (s₁ s₂ : Row), MarkPre d f as r₁ r₂ x →
      FDatabase.mergeOneWith d.closureF x s₁ s₂ = some y → MarkPre d f as r₁ r₂ y := by
    intro x y s₁ s₂ hx hy
    obtain ⟨hle, hlt, hpres⟩ := mergeOneWith_countP (as := as) (by rw [hx.2.1]; exact hshape)
      hx.1.index hcl (by rw [hx.2.1]; exact hmgf) hfne hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1, hle.trans hx.2.2.1, ?_⟩
    rcases hx.2.2.2 with h | ⟨hr₁, hr₂⟩
    · exact Or.inl (lt_of_le_of_lt hle h)
    · by_cases hs : rowAt f as s₁ = true
      · exact Or.inl (lt_of_lt_of_le (hlt hs) hx.2.2.1)
      · exact Or.inr ⟨hpres (by simpa using hs) r₁ hr₁ hk₁, hpres (by simpa using hs) r₂ hr₂ hk₂⟩
  -- The two invariants survive one inner step, and so a whole inner fold.
  have hQstep : ∀ (s₁ : Row) (b : FDatabase) (y : Row), MarkPost d f as b →
      MarkPost d f as (if s₁ == y then b
        else match FDatabase.mergeOneWith d.closureF b s₁ y with
          | some acc'' => acc'' | none => b) := by
    intro s₁ b y hb
    by_cases hbe : s₁ == y
    · simpa [hbe] using hb
    · rw [if_neg (by simpa using hbe)]
      cases hz : FDatabase.mergeOneWith d.closureF b s₁ y with
      | none => simpa [hz] using hb
      | some z => simpa [hz] using hstepQ b z s₁ y hb hz
  have hPstep : ∀ (s₁ : Row) (b : FDatabase) (y : Row), MarkPre d f as r₁ r₂ b →
      MarkPre d f as r₁ r₂ (if s₁ == y then b
        else match FDatabase.mergeOneWith d.closureF b s₁ y with
          | some acc'' => acc'' | none => b) := by
    intro s₁ b y hb
    by_cases hbe : s₁ == y
    · simpa [hbe] using hb
    · rw [if_neg (by simpa using hbe)]
      cases hz : FDatabase.mergeOneWith d.closureF b s₁ y with
      | none => simpa [hz] using hb
      | some z => simpa [hz] using hstepP b z s₁ y hb hz
  -- The marked pair: the collision fires, so the count drops.
  have hmark : ∀ b : FDatabase, MarkPre d f as r₁ r₂ b →
      MarkPost d f as (if r₁ == r₂ then b
        else match FDatabase.mergeOneWith d.closureF b r₁ r₂ with
          | some acc'' => acc'' | none => b) := by
    intro b hb
    rw [if_neg (by simpa using hne)]
    rcases hb.2.2.2 with h | ⟨hr₁, hr₂⟩
    · have hpost : MarkPost d f as b := ⟨hb.1, hb.2.1, h⟩
      cases hz : FDatabase.mergeOneWith d.closureF b r₁ r₂ with
      | none => simpa [hz] using hpost
      | some z => simpa [hz] using hstepQ b z r₁ r₂ hpost hz
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp
        (mergeOneWith_isSome_of_collide (by rw [hb.2.1]; exact hshape) hb.1.index
          (by rw [hb.2.1]; exact hsy) (by rw [hb.2.1]; exact htr)
          (by rw [hb.2.1, hfn₁]; exact hdecl) hdc hr₁ hr₂ (by rw [hfn₁, hfn₂])
          (by rw [ha₁, ha₂]) (by rw [ha₁, ha₂]; exact congrKeys_self hrefl))
      obtain ⟨-, hlt, -⟩ := mergeOneWith_countP (as := as) (by rw [hb.2.1]; exact hshape)
        hb.1.index hcl (by rw [hb.2.1]; exact hmgf) hfne hz
      have hzp : MarkPost d f as z :=
        ⟨FDatabase.mergeOneWith_inv hb.1 (by rw [hb.2.1]; exact hlegal) hz,
          ((FDatabase.mergeOneWith_confined hz).2.2.1).trans hb.2.1,
          lt_of_lt_of_le (hlt hk₁) hb.2.2.1⟩
      simpa [hz] using hzp
  -- The two folds, marked.
  have hinit : MarkPre d f as r₁ r₂ (FDatabase.rebuild d.closureF d) :=
    ⟨Inv.rebuild hinv closureSound_closureF, rfl,
      by rw [hlrows]; exact (List.dedup_sublist d.rows).countP_le,
      Or.inr ⟨by rw [hlrows]; exact List.mem_dedup.mpr hm₁,
        by rw [hlrows]; exact List.mem_dedup.mpr hm₂⟩⟩
  have hmem₁ : r₁ ∈ (FDatabase.rebuild d.closureF d).rows := by
    rw [hlrows]; exact List.mem_dedup.mpr hm₁
  have hmem₂ : r₂ ∈ (FDatabase.rebuild d.closureF d).rows := by
    rw [hlrows]; exact List.mem_dedup.mpr hm₂
  have hfinal : MarkPost d f as (d.mergeRound) := by
    rw [hround]
    refine foldl_mark (P := MarkPre d f as r₁ r₂) (Q := MarkPost d f as) ?_ ?_ ?_ hmem₁ _ hinit
    · intro b y hbb
      exact foldl_pres (P := MarkPre d f as r₁ r₂) (fun c z hc => hPstep y c z hc) _ _ hbb
    · intro b y hbb
      exact foldl_pres (P := MarkPost d f as) (fun c z hc => hQstep y c z hc) _ _ hbb
    · intro b hbb
      exact foldl_mark (P := MarkPre d f as r₁ r₂) (Q := MarkPost d f as)
        (fun c z hc => hPstep r₁ c z hc) (fun c z hc => hQstep r₁ c z hc)
        (fun c hc => hmark c hc) hmem₂ b hbb
  exact hfinal.2.2

/-- **At a merge fixpoint a view key carries at most one row.** `FDatabase.settled` is the
branch condition `FDatabase.mergeSaturateF` returns from and it compares the row list, so a
pass that would drop a count is a pass this state does not take.

This is the `identityVals = some 1` half of the rebuild residue's third obligation, at the
view tables: two entries at one key agree in **every** column, e-class and proof alike, since
`FDatabase.mergeOneOriented` drops the arriving row whether or not the collision runs a
body. -/
theorem row_unique_of_settled {d : FDatabase} {f : FnName} {as vs ws : List Term}
    {dc : FnDecl} (hset : d.settled = true)
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hcl : ∀ p ∈ d.closureF, p.1 = p.2)
    (hsy : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName)
    (hdecl : d.sig f = some dc) (hdc : dc.merge = some (.merge mergeBody mergeResult))
    (hfne : f ≠ ufName) (hrefl : ∀ a ∈ as, (a, a) ∈ d.closureF)
    (h₁ : (⟨f, as, vs⟩ : Row) ∈ d.rows) (h₂ : (⟨f, as, ws⟩ : Row) ∈ d.rows) : vs = ws := by
  by_contra hne
  have hrne : (⟨f, as, vs⟩ : Row) ≠ ⟨f, as, ws⟩ := by
    intro h; exact hne (by simpa using congrArg Row.out h)
  have hlt := mergeRound_countP_lt hshape hlegal hinv hcl hsy htr hdecl hdc hfne hrefl h₁ h₂
    (by simp [rowAt]) (by simp [rowAt]) hrne
  rw [settled_rows hset] at hlt
  omega

end FDatabase

/-! ###### The firing is real

`ENCODING.md`'s discipline: a lemma about a step nothing takes proves nothing. `cxPre` is the
state three `set`s leave — a view entry, the `union`'s `@UF` edge, and the entry the e-class
rebuild rule re-keyed onto `(A)` — and its two `@BView` rows collide at the one (empty) key.
That collision is the firing `mergeOneOriented_soundTerms` is about, `cxTgt` is what the pass
around it produced, and the `@UF` edge below is what the body wrote. -/

/-- The re-keyed row: `@BView() ↦ ((A), @Trans @Fiat @Fiat)`, the arriving one. -/
def cxViewRowA : Row := ⟨viewName "B", [], [cxA, cxTransFiat]⟩

/-- The resident row: `@BView() ↦ ((B), @Fiat)`. -/
def cxViewRowB : Row := ⟨viewName "B", [], [cxB, cxFiat]⟩

/-- The edge `mergeBody` writes between the two rows' e-class columns, with the proof node it
mints: `@Trans (@Sym @Fiat) (@Trans @Fiat @Fiat)`, exactly the shape
`execActions_mergeBody_inv` reads back. -/
def cxUFmerged : Term :=
  .app ufName [cxB, cxA,
    .app transName [.app symName [cxFiat], cxTransFiat]]

set_option maxRecDepth 100000 in
/-- **The collision fires, and it writes.** Three terms more than `cxPre` had, and the edge is
one of them — so `mergeOneOriented_soundTerms`'s conclusion is about a state strictly larger
than its hypothesis's, and its `hedge` obligation is asked at an entry the state did not
hold. -/
theorem cxPre_mergeOneOriented_writes :
    (cxPre.mergeOneOriented cxPre.closureF cxViewRowA cxViewRowB).isSome = true ∧
      ((cxPre.mergeOneOriented cxPre.closureF cxViewRowA cxViewRowB).getD
        FDatabase.empty).terms.contains cxUFmerged = true ∧
      cxPre.terms.contains cxUFmerged = false := by decide

set_option maxRecDepth 100000 in
/-- And the three decidable hypotheses hold there. -/
theorem cxPre_eqsRefl : cxPre.EqsRefl := (FDatabase.eqsReflB_iff cxPre).mp (by decide)

set_option maxRecDepth 100000 in
@[inherit_doc cxPre_eqsRefl]
theorem cxPre_subtermClosed : cxPre.SubtermClosed :=
  (FDatabase.subtermClosedB_iff cxPre).mp (by decide)

@[inherit_doc cxPre_eqsRefl]
theorem cxPre_diag_closureF : ∀ p ∈ cxPre.closureF, p.1 = p.2 :=
  fun _ hp => diag_closureF cxPre_eqsRefl hp

/-! #### Both clauses at the state the forward half's two clauses fail at

`ncTgt_not_readsSelf` and `ncTgt_not_viewsProduct` are the two over-strong forward clauses
refuted at `ncTgt`, the state the encoded `ncProgram` reaches. The completeness half's
invariant **survives** there, at positive arity and at a real `@UF` edge: the source rule
fired over the non-leader member `(B)` and the encoded rule did not, and under-firing is
exactly what soundness is indifferent to. -/

/-- Membership in the source's term list, as membership in its denotation. -/
private theorem ncSrc_memD {t : Term} (h : t ∈ ncSrc.terms) : t ∈ ncSrc.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact h

/-- `(A)` is in the source's term list. -/
private theorem ncSrc_memL_A : ncA ∈ ncSrc.terms := by rw [ncSrc_terms_eq]; simp

/-- `(B)` is in the source's term list. -/
private theorem ncSrc_memL_B : ncB ∈ ncSrc.terms := by rw [ncSrc_terms_eq]; simp

/-- `(F (A))` is in the source's term list. -/
private theorem ncSrc_memL_FA : ncFA ∈ ncSrc.terms := by rw [ncSrc_terms_eq]; simp

/-- `(A)` is a source term, so it is congruent to itself. -/
private theorem ncSrc_mem_A : ncA ∈ ncSrc.toDatabase.terms := ncSrc_memD ncSrc_memL_A

/-- `(B)` is a source term. -/
private theorem ncSrc_mem_B : ncB ∈ ncSrc.toDatabase.terms := ncSrc_memD ncSrc_memL_B

/-- `(F (A))` is a source term. -/
private theorem ncSrc_mem_FA : ncFA ∈ ncSrc.toDatabase.terms := ncSrc_memD ncSrc_memL_FA

/-- The `union`'s own equation, symmetrised: the edge `ncTgt` holds runs from `(B)` to `(A)`
and the source asserts the pair the other way round. -/
private theorem ncSrc_cong_B_A : Cong ncSrc.toDatabase ncB ncA :=
  (Cong.assert (FDatabase.mem_toDatabase_eqs.mpr
    (Or.inr ⟨by rw [ncSrc_eqs]; simp [ncA, ncB], ncSrc_memL_A, ncSrc_memL_B⟩))).symm

/-- **`Database.ViewsSound` holds at `ncTgt`.** Four view entries over three constructors:
`@AView` and `@FView` are reflexive, and `(B)`'s key carries two e-class columns — its own
build's `(B)` and the leader's `(A)`, which the rebuild's e-class rule wrote — so the second
is `EntrySound` at the `union`'s own equation and not at a reflexive `Cong`. `@FView` is keyed
at `((A))`, which is the positive-arity case. -/
theorem ncTgt_viewsSound : ncTgt.toDatabase.ViewsSound ncSrc.toDatabase := by
  intro f cs e pf ho
  rcases ncTgt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hE⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨[], ncSrc_mem_A, .nil, ncSrc_mem_A⟩
  · rcases hE with rfl | rfl
    · exact ⟨[], ncSrc_mem_B, .nil, ncSrc_cong_B_A⟩
    · exact ⟨[], ncSrc_mem_B, .nil, ncSrc_mem_B⟩
  · exact ⟨[ncA], ncSrc_mem_FA, CongList.refl (by
      intro a ha
      obtain rfl : a = ncA := by simpa using ha
      exact ncSrc_mem_A), ncSrc_mem_FA⟩

/-- **And `Database.EdgesSound` holds at `ncTgt`, with an edge to discharge it at.**
`ncTgt_out_uf` is the edge — `@UF((B)) ↦ ((A), …)`, written by the source `union` and settled
against by `mergeBody` — so the clause is not carried here by its vacuous case, which is the
trap `satTarget_edgesSound` is. -/
theorem ncTgt_edgesSound : ncTgt.toDatabase.EdgesSound ncSrc.toDatabase := by
  intro t p pf ho
  obtain ⟨rfl, rfl⟩ := ncTgt_out_uf_cases ho
  exact ncSrc_cong_B_A

/-- **The term-list form at the same state**, through `soundTerms_of_viewsSound` and back
through `viewsSound_of_soundTerms`: the two forms agree at a state that holds four view
entries and two `@UF` edges, so the residue below is stated at neither more nor less than the
two clauses. -/
theorem ncTgt_soundTerms : ncTgt.SoundTerms ncSrc.toDatabase ∧
    ncTgt.toDatabase.ViewsSound ncSrc.toDatabase ∧
    ncTgt.toDatabase.EdgesSound ncSrc.toDatabase :=
  let hs := soundTerms_of_viewsSound ncTgt_subtermClosed ncTgt_viewsSound ncTgt_edgesSound
  ⟨hs, viewsSound_of_soundTerms ncTgt_eqsRefl hs⟩

/-- **The completeness half's whole conclusion, at `ncTgt`.** `sameClass_cong_of_state` run at
the state the two forward clauses fail at, over the pair the source really does equate. -/
theorem ncTgt_sameClass_cong : Cong ncSrc.toDatabase ncFA ncFB :=
  sameClass_cong_of_state (ncProgram_programStep.wf Database.WF.empty) ncTgt_viewsSound
    ncSrc_mem_FA (ncSrc_memD ncSrc_mem_FB) ncTgt_sameClass_FA_FB

/-! #### The source's own firing, reached

`hfired`'s cheap part, proved: a firing of the round's **pre**-state writes into the round's
**post**-state. `RunRules` is a `Database.sUnion` over the rule results, so one result's
equations are among the round's; `MergeClosure` only grows `eqs`, so the merge phase keeps
them; and `Cmd.saturate`'s extra rounds only grow it further. Stated over both firing commands,
since `encodeCmd` gives them the same block.

What these do **not** give is that the source's block evaluates at all. `RuleResults` asks
`evalLocalActions` for a `some`, and a stuck head is exactly the two refutations at the end of
this file — so `evalLocalActions … = some d` is a hypothesis *here*, and discharging it from
`EncodeDomain.noLitUnion` and `EncodeDomain.headsDeclared` is the section after next. -/

/-- **The round's rule-firing half is contained in the round's post-state.** One `MergeClosure`
for a `.run`; for a `.saturate`, the first round's phase and then every round after it — or,
at zero rounds, `RunSaturated`'s own fixpoint. -/
theorem runRules_eqs_subset_of_cmdStep {R : RulesetName} {c : Cmd} {sd sd' : Database}
    (hc : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd') :
    (RunRules R sd).eqs ⊆ sd'.eqs := by
  rcases hc with rfl | rfl
  · obtain ⟨e, hreach, hcl⟩ := hstep
    have he : some (RunRules R sd) = some e := hreach
    obtain rfl : RunRules R sd = e := Option.some.inj he
    exact (MergeClosure.contained hcl).eqs
  · obtain ⟨hreach, hsat⟩ := cmdStep_saturate_iff.mp hstep
    rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨x, hstep₁, hrest⟩
    · rw [hsat.1]
    · exact ((MergeClosure.contained hstep₁).trans (RunReach.contained hrest)).eqs

/-- **Every equation one firing asserts is one the round's post-state asserts.** -/
theorem mem_eqs_of_ruleFired {R : RulesetName} {c : Cmd} {sd sd' d : Database} {r : Rule}
    (hc : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) {τ : Env}
    (hv : ValidQuerySubst sd r.query τ) (hd : evalLocalActions sd r.actions τ = some d)
    {p : Term × Term} (hp : p ∈ d.eqs) : p ∈ sd'.eqs := by
  refine runRules_eqs_subset_of_cmdStep hc hstep ?_
  rw [RunRules, Database.sUnion_eqs]
  exact Or.inr (Set.mem_biUnion (show d ∈ _ from ⟨r, hr, hrs, τ, hv, hd⟩) hp)

/-- **And every term one firing builds is one the round's post-state holds.** This is the shape
`entrySound_headBuild_post` asks `hfired` for, with `src` the round's pre-state and `src'` its
post-state — the two `FDatabase.SoundTerms.mono_src` cannot bridge, since the term is in
neither `sd.terms` nor a clause about it. -/
theorem mem_terms_of_ruleFired {R : RulesetName} {c : Cmd} {sd sd' d : Database} {r : Rule}
    (hc : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) {τ : Env}
    (hv : ValidQuerySubst sd r.query τ) (hd : evalLocalActions sd r.actions τ = some d)
    {t : Term} (ht : t ∈ d.terms) : t ∈ sd'.terms := by
  refine Database.mem_terms_of_eqs (runRules_eqs_subset_of_cmdStep hc hstep) ?_
  rw [RunRules, Database.sUnion_terms]
  exact Or.inr (Set.mem_biUnion (show d ∈ _ from ⟨r, hr, hrs, τ, hv, hd⟩) ht)

/-! #### The block evaluates, and the two domain clauses that buy it

`hfired`'s third part. `RuleResults` asks `evalLocalActions` for a `some`, and `Expr.eval` has
exactly three failure modes on a constructor-fragment head — an undeclared name, a `union`
whose operand's *value* is a literal, and an unbound variable. `EncodeDomain.headsDeclared`
answers the first, `EncodeDomain.noLitUnion` the second, and the third is not a domain clause
and does not need to be: `encodeBuild` keeps a source variable as itself and the encoded query
binds no name the source query does not, so a head variable neither the query nor a global
binds sticks the **encoded** head too and that firing writes on neither side
(`Rule.HeadScoped`).

The second clause is a disjunction and both arms are carried here. The union-free arm is
syntactic. The literal-free arm is *not* — `Spec/Scope.lean`'s `Action.Evaluable` asks a
`union` operand to be an application, which is the strongest condition readable off the
expression alone, and a lit-free program's **variable** operand fails it: a query binds a
variable to a term the source holds, and that term is not a literal for a reason about the
**state**. So the arm is carried as a source-run invariant, `Database.NoLits`, and
`Database.LitFree` is its data clause.
-/

/-! ##### Literal-free terms and states -/

/-- No literal occurs in `t`. -/
def Term.LitFree (t : Term) : Prop := ∀ s ∈ t.subterms, ¬ s.isLit

theorem Term.not_litFree_lit {l : Lit} : ¬ Term.LitFree (.lit l) := by
  intro h
  exact h _ (Term.self_mem_subterms _) rfl

theorem Term.litFree_app {f : FnName} {args : List Term} :
    Term.LitFree (.app f args) ↔ ∀ a ∈ args, Term.LitFree a := by
  simp only [Term.LitFree, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop, forall_eq_or_imp]
  constructor
  · rintro ⟨-, h⟩ a ha s hs
    exact h s ⟨a, ha, hs⟩
  · rintro h
    refine ⟨by simp [Term.isLit], ?_⟩
    rintro s ⟨a, ha, hs⟩
    exact h a ha s hs

/-- No term the state holds is a literal. -/
def Database.LitFree (db : Database) : Prop := ∀ t ∈ db.terms, ¬ t.isLit

theorem Database.LitFree.term {db : Database} (hw : db.WF) (h : db.LitFree) {t : Term}
    (ht : t ∈ db.terms) : Term.LitFree t :=
  fun s hs => h s (hw.subtermClosed t ht hs)

theorem Database.empty_litFree : Database.empty.LitFree := by
  intro t ht; exact absurd ht (by simp)

/-! ##### Evaluation of a literal-free expression builds a literal-free term -/

mutual

/-- **A literal-free expression evaluates to a literal-free term**, in an environment whose
bindings are literal-free. `Prim.ofName f = none` is what keeps the primitive branch out:
`ordering-gt` returns a fresh `bool` literal from operands that hold none, so the clause is
about the applied names and not only about the syntax. -/
theorem Expr.eval_litFree {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (e : Expr) {t : Term}, e.litFreeB = true → (∀ f ∈ e.fns, Prim.ofName f = none) →
      e.eval sig σ = some t → Term.LitFree t
  | .lit _, _, hl, _, _ => by simp [Expr.litFreeB] at hl
  | .var v, t, _, _, he => hσ v t he
  | .app f args, t, hl, hf, he => by
      rw [Expr.eval_app_ctor (hf f (by simp [Expr.fns])) ?_] at he
      · obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
        refine Term.litFree_app.mpr ?_
        exact Expr.evalList_litFree hσ args (by simpa [Action.litFreeB, Expr.litFreeB] using hl)
          (fun g hg => hf g (by simp [Expr.fns, hg])) hts
      · by_contra hc
        rw [Expr.eval_app_not_ctor (hf f (by simp [Expr.fns])) hc] at he
        exact absurd he (by simp)

@[inherit_doc Expr.eval_litFree]
theorem Expr.evalList_litFree {sig : Signature} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (es : List Expr) {ts : List Term}, Expr.litFreeListB es = true →
      (∀ f ∈ Expr.fnsList es, Prim.ofName f = none) →
      Expr.evalList sig es σ = some ts → ∀ t ∈ ts, Term.LitFree t
  | [], _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hl, hf, he => by
      rw [Expr.litFreeListB, Bool.and_eq_true] at hl
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_litFree hσ e hl.1 (fun g hg => hf g (by simp [hg])) hu
      · exact Expr.evalList_litFree hσ es hl.2 (fun g hg => hf g (by simp [hg])) hus t ht'

end

/-! ##### The primitive condition, at the applied names -/

/-- `Program.EncodeDomain.noPrim` reads `Program.ctors` and evaluation reads `Expr.fns`. -/
theorem noPrim_fns {e : Expr} (hp : ∀ fk ∈ e.ctors, Prim.ofName fk.1 = none) :
    ∀ f ∈ e.fns, Prim.ofName f = none := fun f hf =>
  let ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hf
  hp (f, k) hk

@[inherit_doc noPrim_fns]
theorem noPrim_fnsList {es : List Expr}
    (hp : ∀ fk ∈ Expr.ctorsList es, Prim.ofName fk.1 = none) :
    ∀ f ∈ Expr.fnsList es, Prim.ofName f = none := fun f hf =>
  let ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hf
  hp (f, k) hk

/-! ##### One action keeps the state literal-free -/

theorem Database.LitFree.lookup {db : Database} (hw : db.WF) (h : db.LitFree) :
    ∀ v t, Env.lookup v db.env = some t → Term.LitFree t := fun v t hv =>
  h.term hw (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

/-- **A literal-free action keeps the state literal-free.** Every writer is an `addTerm` or
an `addEq` of a value `Expr.eval_litFree` covers. -/
theorem evalAction_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {a : Action} (hl : a.litFreeB = true) (hp : ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none)
    (hv : evalAction db a = some db') : db'.LitFree := by
  have hlk := h.lookup hw
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ | ⟨v, e, t, rfl, he, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, ha, hb, rfl⟩
  · have ht : Term.LitFree t :=
      Expr.eval_litFree hlk e hl (noPrim_fns hp) he
    intro s hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact ht s hs'
  · have ht : Term.LitFree t :=
      Expr.eval_litFree hlk e hl (noPrim_fns hp) he
    intro s hs
    rw [Database.terms_setEnv, Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact ht s hs'
  · rw [Action.litFreeB, Bool.and_eq_true] at hl
    have hp₁ : ∀ fk ∈ e₁.ctors, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (by rw [Action.ctors]; exact List.mem_append_left _ hk)
    have hp₂ : ∀ fk ∈ e₂.ctors, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (by rw [Action.ctors]; exact List.mem_append_right _ hk)
    have ht₁ : Term.LitFree t₁ := Expr.eval_litFree hlk e₁ hl.1 (noPrim_fns hp₁) he₁
    have ht₂ : Term.LitFree t₂ := Expr.eval_litFree hlk e₂ hl.2 (noPrim_fns hp₂) he₂
    intro s hs
    rw [Database.addEq_terms] at hs
    rcases hs with hs' | hs'
    · rcases hs' with hs'' | hs''
      · exact h s hs''
      · exact ht₁ s hs''
    · exact ht₂ s hs'
  · rw [Action.litFreeB, Bool.and_eq_true] at hl
    have hp₁ : ∀ fk ∈ Expr.ctorsList args, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (List.mem_cons_of_mem _ (List.mem_append_left _ hk))
    have hp₂ : ∀ fk ∈ Expr.ctorsList out, Prim.ofName fk.1 = none :=
      fun fk hk => hp fk (List.mem_cons_of_mem _ (List.mem_append_right _ hk))
    have hall : ∀ u ∈ as ++ vs, Term.LitFree u := by
      intro u hu
      rcases List.mem_append.mp hu with hu' | hu'
      · exact Expr.evalList_litFree hlk args hl.1 (noPrim_fnsList hp₁) ha u hu'
      · exact Expr.evalList_litFree hlk out hl.2 (noPrim_fnsList hp₂) hb u hu'
    intro s hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact h s hs'
    · exact Term.litFree_app.mpr hall s hs'

/-- What one action must be for `evalAction` to keep the state literal-free: no literal in
the expressions it evaluates, and no applied name a primitive — `ordering-gt` returns a
`bool` literal from operands that hold none. -/
def Action.NoLits (a : Action) : Prop :=
  a.litFreeB = true ∧ ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none

/-- `Action.NoLits` at every action a command runs. Vacuous at a run, a saturation and a
declaration, which evaluate nothing. -/
def Cmd.NoLits : Cmd → Prop
  | .action a => a.NoLits
  | .rule r => ∀ a ∈ r.actions, a.NoLits
  | _ => True

theorem evalActions_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits)
    (hv : evalActions db as = some db') : db'.LitFree := by
  induction as generalizing db with
  | nil =>
      rw [evalActions_nil, Option.some_inj] at hv
      exact hv ▸ h
  | cons a as ih =>
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨d, hd, hrest⟩ := hv
      have ha := hl a List.mem_cons_self
      refine ih (evalAction_wf hw hd) (evalAction_litFree hw h ha.1 ha.2 hd) ?_ hrest
      exact fun b hb => hl b (List.mem_cons_of_mem _ hb)

theorem evalLocalActions_litFree {db db' : Database} (hw : db.WF) (h : db.LitFree)
    {as : List Action} (hl : ∀ a ∈ as, a.NoLits) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hv : evalLocalActions db as σ = some db') :
    db'.LitFree := by
  obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some hv
  have hlf : ({ db with env := db.env ++ σ } : Database).LitFree := by
    intro t ht; exact h t (Database.terms_setEnv ▸ ht)
  intro t ht
  rw [Database.terms_setEnvRules] at ht
  exact evalActions_litFree (hw.appendEnv hσ) hlf hl hd t ht

/-- **The source-side invariant `noLitUnion`'s second arm is carried as**: no term the state
holds is a literal, and every rule it holds has a literal-free head. The second clause is what
the rule-firing case needs — a firing evaluates a head the *state* carries, not one the
command names. -/
structure Database.NoLits (db : Database) : Prop where
  /-- No term the state holds is a literal, so no variable is bound to one. -/
  terms : db.LitFree
  /-- Every rule the state holds has a literal-free head. -/
  heads : ∀ r ∈ db.rules, ∀ a ∈ r.actions, a.NoLits

theorem Database.empty_noLits : Database.empty.NoLits where
  terms := Database.empty_litFree
  heads := by intro r hr; exact absurd hr (by simp [Database.empty])

/-- **A round keeps it.** `RunRules` is a `Database.sUnion` over the firings, each of which is
an `evalLocalActions` of a head the state carries. -/
theorem Database.NoLits.runRules {R : RulesetName} {db : Database} (hw : db.WF)
    (h : db.NoLits) : (RunRules R db).NoLits := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [RunRules, Database.sUnion_terms] at ht
    rcases ht with ht' | ht'
    · exact h.terms t ht'
    · obtain ⟨d, hd, ht''⟩ := Set.mem_iUnion₂.mp ht'
      obtain ⟨r, hr, -, σ, hq, hfire⟩ := hd
      exact evalLocalActions_litFree hw h.terms (h.heads r hr) hq.mem_terms hfire t ht''
  · rw [RunRules, Database.sUnion_rules]; exact h.heads

/-! ##### One command and one run keep it -/

theorem cmdStep_noLits {db db' : Database} (hc : db.CtorState) (h : db.NoLits)
    {c : Cmd} (hn : c.NoLits) (hdecl : c.CtorDecl) (hstep : CmdStep db c db') :
    db'.NoLits := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  cases c with
  | action a =>
      have hv : evalAction db a = some d := hreach
      obtain rfl : db' = d :=
        hcl.eq_of_allConstructors (by rw [evalAction_sig hv]; exact hc.sig)
      exact ⟨evalAction_litFree hc.wf h.terms hn.1 hn.2 hv,
        by rw [evalAction_rules hv]; exact h.heads⟩
  | rule r =>
      have hv : some { db with rules := insert r db.rules } = some d := hreach
      obtain rfl : d = { db with rules := insert r db.rules } := (Option.some.inj hv).symm
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      refine ⟨fun t ht => h.terms t (Database.terms_setRules ▸ ht), ?_⟩
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact hn
      · exact h.heads r' hr''
  | run R =>
      have hv : some (RunRules R db) = some d := hreach
      obtain rfl : d = RunRules R db := (Option.some.inj hv).symm
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      exact h.runRules hc.wf
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp ⟨d, hreach, hcl⟩
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.NoLits) ?_ hsat.1 ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      exact ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩,
        hx.2.runRules hx.1.wf⟩
  | decl f dc =>
      have hv : some { db with sig := Function.update db.sig f (some dc) } = some d := hreach
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } :=
        (Option.some.inj hv).symm
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      exact ⟨fun t ht => h.terms t (Database.terms_setSig ▸ ht), h.heads⟩

/-- **`Database.NoLits` at every state a run reaches.** Applied to a *prefix* of the source
program it is the invariant at the state a firing command starts from, which is where the
head's own `union` check is spent. -/
theorem programStep_noLits {db db' : Database} (hc : db.CtorState) (h : db.NoLits)
    {p : Program} (hn : ∀ c ∈ p, c.NoLits) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.NoLits := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      exact ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_noLits hc h (hn c List.mem_cons_self) (hdecl c List.mem_cons_self) hstep)
        (fun c' hc' => hn c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-! ##### The block evaluates

`Spec/Scope.lean`'s `Action.Evaluable` asks a `union` operand to be an **application**, which
is the strongest condition readable off the expression alone and which a lit-free program's
*variable* operand fails: a query binds a variable to a term the source holds, and that term
is not a literal for a reason about the **state**. So the block lemma is restated with that
clause replaced by the two arms of `Program.EncodeDomain.noLitUnion`, which is exactly what
`evalAction`'s own check spends. -/

/-- `Action.Evaluable` with the `union` operands' `Expr.IsApp` dropped: every expression the
action evaluates builds, and nothing is asked about literals. -/
def Action.Builds : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => e₁.Evaluable sig ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

@[simp] def Actions.Builds : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Builds sig ∧ Actions.Builds as sig

/-- **The `union` check, as the block needs it**: either the block asserts no equation, or
the state holds no literal and the block evaluates none. The two arms of
`Program.EncodeDomain.noLitUnion`, and both survive one action — which is what lets the fold
carry the disjunction rather than one arm at a time. -/
def Actions.UnionRunnable (as : List Action) (db : Database) : Prop :=
  Actions.UnionFree as ∨ (db.LitFree ∧ ∀ a ∈ as, a.NoLits)

/-- **One action does not get stuck.** `evalAction_isSome_of_scoped` with the `union` clause
weakened to `Actions.UnionRunnable`. -/
theorem evalAction_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {a : Action} {as : List Action} (hsc : a.Scoped Γ) (hb : a.Builds db.sig)
    (hr : Actions.UnionRunnable (a :: as) db) :
    ∃ db', evalAction db a = some db' ∧ (a.bind Γ).Models db'.env := by
  cases a with
  | expr e =>
      obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm hsc.2 hb
      exact ⟨db.addTerm t, by simp [evalAction, ht], hm⟩
  | letBind v e =>
      obtain ⟨t, ht⟩ := Expr.eval_isSome_of_scoped hm hsc hb
      refine ⟨{ db.addTerm t with env := (v, t) :: db.env }, by simp [evalAction, ht], ?_⟩
      intro w
      simp only [Action.bind, List.mem_cons, Env.dom_cons]
      exact or_congr_right (hm w)
  | union e₁ e₂ =>
      obtain ⟨t₁, ht₁⟩ := Expr.eval_isSome_of_scoped hm hsc.1 hb.1
      obtain ⟨t₂, ht₂⟩ := Expr.eval_isSome_of_scoped hm hsc.2 hb.2
      rcases hr with huf | ⟨hlf, hnl⟩
      · exact absurd huf.1 id
      · obtain ⟨hl, hp⟩ := hnl _ List.mem_cons_self
        rw [Action.litFreeB, Bool.and_eq_true] at hl
        have hp₁ : ∀ fk ∈ e₁.ctors, Prim.ofName fk.1 = none :=
          fun fk hk => hp fk (List.mem_append_left _ hk)
        have hp₂ : ∀ fk ∈ e₂.ctors, Prim.ofName fk.1 = none :=
          fun fk hk => hp fk (List.mem_append_right _ hk)
        have hlk := hlf.lookup hw
        have hn₁ : ¬ t₁.isLit :=
          Expr.eval_litFree hlk e₁ hl.1 (noPrim_fns hp₁) ht₁ t₁ (Term.self_mem_subterms t₁)
        have hn₂ : ¬ t₂.isLit :=
          Expr.eval_litFree hlk e₂ hl.2 (noPrim_fns hp₂) ht₂ t₂ (Term.self_mem_subterms t₂)
        exact ⟨db.addEq t₁ t₂, by simp [evalAction, ht₁, ht₂, hn₁, hn₂], hm⟩
  | set f args out =>
      obtain ⟨cs, hcs⟩ := Expr.evalList_isSome args
        (fun v hv => by
          obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
          exact (hm v).mp (hsc.1 e hmem v hve))
        (fun g hg => by
          obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
          exact hb.1 e hmem g hge)
      obtain ⟨vs, hvs⟩ := Expr.evalList_isSome out
        (fun v hv => by
          obtain ⟨e, hmem, hve⟩ := Expr.mem_varsList hv
          exact (hm v).mp (hsc.2 e hmem v hve))
        (fun g hg => by
          obtain ⟨e, hmem, hge⟩ := Expr.mem_fnsList hg
          exact hb.2 e hmem g hge)
      refine ⟨db.addTerm (.app f (cs ++ vs)), by simp [evalAction, hcs, hvs], ?_⟩
      simpa [Action.bind] using hm

/-- **The block does not get stuck.** The fold, with `Actions.UnionRunnable` as the
invariant: the union-free arm shrinks with the list, and the literal-free arm is carried by
`evalAction_litFree`. -/
theorem evalActions_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {as : List Action} (hsc : Actions.Scoped as Γ)
    (hb : Actions.Builds as db.sig) (hr : Actions.UnionRunnable as db) :
    ∃ db', evalActions db as = some db' ∧ (Actions.bind as Γ).Models db'.env := by
  induction as generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons a as ih =>
      obtain ⟨db₁, h₁, hm₁⟩ := evalAction_isSome_of_builds hm hw hsc.1 hb.1 hr
      have hsig : db₁.sig = db.sig := evalAction_sig h₁
      have hr₁ : Actions.UnionRunnable as db₁ := by
        rcases hr with huf | ⟨hlf, hnl⟩
        · exact Or.inl huf.2
        · obtain ⟨hl, hp⟩ := hnl a List.mem_cons_self
          exact Or.inr ⟨evalAction_litFree hw hlf hl hp h₁,
            fun b hb' => hnl b (List.mem_cons_of_mem _ hb')⟩
      obtain ⟨db₂, h₂, hm₂⟩ :=
        ih hm₁ (evalAction_wf hw h₁) hsc.2 (by rw [hsig]; exact hb.2) hr₁
      exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-- **A rule head does not get stuck**, at the substitution its query delivered.
`Spec/Scope.lean`'s `evalLocalActions_isSome_of_scoped` with the `union` clause weakened. -/
theorem evalLocalActions_isSome_of_builds {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    (hw : db.WF) {r : Rule} (hsc : Actions.Scoped r.actions (Query.bind r.query Γ))
    (hb : Actions.Builds r.actions db.sig)
    (hr : Actions.UnionRunnable r.actions db) {σ : Env}
    (hq : ValidQuerySubst db r.query σ) :
    ∃ d, evalActions { db with env := db.env ++ σ } r.actions = some d ∧
      evalLocalActions db r.actions σ = some { d with env := db.env, rules := db.rules } := by
  obtain ⟨d, hd, -⟩ := evalActions_isSome_of_builds
    (db := { db with env := db.env ++ σ }) (Query.bind_models hm hq)
    (hw.appendEnv hq.mem_terms) hsc hb
    (by rcases hr with huf | ⟨hlf, hnl⟩
        · exact Or.inl huf
        · exact Or.inr ⟨fun t ht => hlf t (Database.terms_setEnv ▸ ht), hnl⟩)
  exact ⟨d, hd, by simp [evalLocalActions, hd]⟩

/-! ##### Where in the block an action ran

`hfired` is stated at the block's *initial* environment `src.env ++ τ`, and an action after a
`letBind` in the same block runs at an extended one. So the block lemma has to say which
environment each action saw, and it is the initial one extended by a prefix whose domain is
the `let`s the block performed before it. -/

/-- The variable a `let` binds; nothing for any other action. -/
def Action.letVars : Action → List Var
  | .letBind v _ => [v]
  | _ => []

/-- The variables a block's `let`s bind, which is what an action's environment can carry
beyond the block's own. -/
def Actions.letVars (as : List Action) : List Var := as.flatMap Action.letVars

/-- **Only a `let` extends the environment**, and it extends it by its own binder. -/
theorem evalAction_env_append {db db' : Database} {a : Action}
    (h : evalAction db a = some db') :
    ∃ δ, db'.env = δ ++ db.env ∧ ∀ v ∈ Env.dom δ, v ∈ a.letVars := by
  rcases evalAction_eq_some h with ⟨e, t, rfl, -, rfl⟩ | ⟨v, e, t, rfl, -, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, -, -, -, rfl⟩ | ⟨f, args, out, cs, vs, rfl, -, -, rfl⟩
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨[(v, t)], rfl, by simp [Action.letVars]⟩
  · exact ⟨[], rfl, by simp⟩
  · exact ⟨[], rfl, by simp⟩

/-- **Each action of a block ran at the block's own state, extended by the `let`s before
it**, and what it wrote is in the block's result. The environment clause is the one `hfired`
does not state; `Database.Contained` is what carries the write to the end of the block. -/
theorem exists_step_of_mem_evalActions : ∀ {as : List Action} {db d : Database},
    evalActions db as = some d → ∀ a ∈ as,
      ∃ δ e e', (∀ v ∈ Env.dom δ, v ∈ Actions.letVars as) ∧ e.sig = db.sig ∧
        e.env = δ ++ db.env ∧ evalAction e a = some e' ∧ Database.Contained e' d
  | [], _, _, _, a, ha => absurd ha (by simp)
  | b :: bs, db, d, hv, a, ha => by
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨db₁, h₁, hrest⟩ := hv
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨[], db, db₁, by simp, rfl, by simp, h₁, evalActions_contained hrest⟩
      · obtain ⟨δ, e, e', hdom, hsig, henv, hs, hcont⟩ :=
          exists_step_of_mem_evalActions hrest a ha'
        obtain ⟨δ₁, henv₁, hdom₁⟩ := evalAction_env_append h₁
        refine ⟨δ ++ δ₁, e, e', ?_, by rw [hsig, evalAction_sig h₁], ?_, hs, hcont⟩
        · intro v hvm
          rw [Env.dom_append, List.mem_append] at hvm
          rw [Actions.letVars, List.flatMap_cons, List.mem_append]
          rcases hvm with hv' | hv'
          · exact Or.inr (hdom v hv')
          · exact Or.inl (hdom₁ v hv')
        · rw [henv, henv₁, List.append_assoc]

/-! ##### `hfired`, discharged

The three parts of `hfired` composed: the block evaluates (`evalLocalActions_isSome_of_builds`,
out of the two domain clauses), each action ran at an environment the block's `let`s extended
(`exists_step_of_mem_evalActions`), and the write reaches the round's post-state
(`mem_terms_of_ruleFired`, `mem_eqs_of_ruleFired`). -/

/-- **The head's variables are bound where it runs**: the query's, the state's globals, or
the block's own `let`s. `Spec/Scope.lean`'s `Actions.Scoped` at the scope the state's
environment already is, so nothing has to model anything.

**It is a real condition, and the third shape of stuck head.** It was recorded here as
costing nothing — "a head variable neither the query nor a global binds sticks the *encoded*
head too" — and that is true wherever the encoded head **reads** the variable, which is every
position but one: `encodeBuild` emits no action at all for a *leaf*, so `.expr (.var v)`
stops the source block at an unbound `v` and the encoded block skips it and runs the rest of
the head. `bareProgram` is that, and `bare_build_invents_equality` is
`encode_corresponds_complete` failing at it under every *other* clause of the domain.
`EncodeDomain.headsScoped` — `Program.HeadsScoped`, on the program's text — is the clause
that excludes it, and `encodedHeadSound` is what it buys. -/
def Rule.HeadScoped (r : Rule) (db : Database) : Prop :=
  Actions.Scoped r.actions (Query.bind r.query (Env.dom db.env))

/-- `Expr.Scoped` in the scope. -/
theorem Expr.Scoped.mono {e : Expr} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : e.Scoped Γ) : e.Scoped Γ' := fun v hv => hsub v (h v hv)

@[inherit_doc Expr.Scoped.mono]
theorem Action.Scoped.mono {a : Action} {Γ Γ' : Scope} (hsub : ∀ v ∈ Γ, v ∈ Γ')
    (h : a.Scoped Γ) : a.Scoped Γ' := by
  cases a with
  | expr e => exact ⟨h.1, Expr.Scoped.mono hsub h.2⟩
  | letBind v e => exact Expr.Scoped.mono hsub h
  | union e₁ e₂ => exact ⟨Expr.Scoped.mono hsub h.1, Expr.Scoped.mono hsub h.2⟩
  | set f args out =>
      exact ⟨fun e he => Expr.Scoped.mono hsub (h.1 e he),
        fun e he => Expr.Scoped.mono hsub (h.2 e he)⟩

@[inherit_doc Expr.Scoped.mono]
theorem Actions.Scoped.mono : ∀ (as : List Action) {Γ Γ' : Scope}, (∀ v ∈ Γ, v ∈ Γ') →
    Actions.Scoped as Γ → Actions.Scoped as Γ' := by
  intro as
  induction as with
  | nil => intro _ _ _ _; trivial
  | cons a as ih =>
    intro Γ Γ' hsub h
    refine ⟨Action.Scoped.mono hsub h.1, ih ?_ h.2⟩
    cases a with
    | letBind v e =>
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub w hw')
    | expr e => exact hsub
    | union e₁ e₂ => exact hsub
    | set f args out => exact hsub

/-- And it gives `Rule.HeadScoped` at any state, since a state's globals only widen the
scope. -/
theorem Program.HeadsScoped.headScoped {P : Program} (h : P.HeadsScoped) {r : Rule}
    (hr : Cmd.rule r ∈ P) (sd : Database) : r.HeadScoped sd :=
  Actions.Scoped.mono r.actions
    (fun v hv => by rw [Query.bind]; exact List.mem_union_iff.mpr (Or.inr hv)) (h _ hr)


theorem Scope.Models.dom (σ : Env) : Scope.Models (Env.dom σ) σ := fun _ => Iff.rfl

/-- **A source rule of the round writes, and where.** The firing exists — which is what
`RuleResults` asks and what a stuck head denies — and each action of its head ran at the
environment `src.env ++ τ` extended by the `let`s before it, with its own writes reaching the
round's post-state. -/
theorem exists_headStep_of_ruleFired {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ) :
    ∀ a ∈ r.actions, ∃ δ e e', (∀ v ∈ Env.dom δ, v ∈ Actions.letVars r.actions) ∧
      e.sig = sd.sig ∧ e.env = δ ++ (sd.env ++ τ) ∧ evalAction e a = some e' ∧
      (∀ t ∈ e'.terms, t ∈ sd'.terms) ∧ (∀ p ∈ e'.eqs, p ∈ sd'.eqs) := by
  obtain ⟨d, hd, hlocal⟩ :=
    evalLocalActions_isSome_of_builds (Scope.Models.dom sd.env) hw hsc hb hun hq
  intro a ha
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, hcont⟩ := exists_step_of_mem_evalActions hd a ha
  refine ⟨δ, e, e', hdom, hsig, henv, hs, ?_, ?_⟩
  · intro t ht
    exact mem_terms_of_ruleFired hfire hstep hr hrs hq hlocal
      (Database.terms_setEnvRules ▸ hcont.terms ht)
  · intro p hp
    exact mem_eqs_of_ruleFired hfire hstep hr hrs hq hlocal (hcont.eqs hp)

/-- **`hfired` for `entrySound_headBuild`.** The head's own build, at the substitution the
correspondence returns: the term the source's head evaluation gives is a term the round's
post-state holds.

`hlet` is what the two states' shapes cost. `hfired` reads the head at the block's *initial*
environment, and an action after a `letBind` runs at an extended one; where the head mentions
none of the block's own binders the two environments agree on what the head reads
(`Expr.eval_agreeOn`) and the extension drops out. All seventy in-domain cases satisfy it
outright — no rule head there binds anything. -/
theorem mem_terms_of_headBuild {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {f : FnName} {args : List Expr} (ha : Action.expr (.app f args) ∈ r.actions)
    (hlet : ∀ v ∈ (Expr.app f args).vars, v ∉ Actions.letVars r.actions)
    {is : List Term}
    (hval : (Expr.app f args).eval sd.sig (sd.env ++ τ) = some (.app f is)) :
    Term.app f is ∈ sd'.terms := by
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, hterms, -⟩ :=
    exists_headStep_of_ruleFired hfire hstep hw hr hrs hsc hb hun hq _ ha
  have hagree : ∀ v ∈ (Expr.app f args).vars,
      Env.lookup v e.env = Env.lookup v (sd.env ++ τ) := by
    intro v hv
    rw [henv]
    exact Env.lookup_append_of_not_mem fun hc => hlet v hv (hdom v hc)
  have heval : (Expr.app f args).eval e.sig e.env = some (.app f is) := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _ hagree]; exact hval
  rcases evalAction_eq_some hs with ⟨g, t, hg, hev, rfl⟩ | ⟨v, g, t, hg, -, -⟩ |
      ⟨g₁, g₂, t₁, t₂, hg, -, -, -, -⟩ | ⟨g, cs, out, as, vs, hg, -, -, -⟩
  · obtain rfl : g = Expr.app f args := by injection hg with h; exact h.symm
    obtain rfl : t = Term.app f is := Option.some.inj (hev.symm.trans heval)
    exact hterms _ (Database.mem_addTerm _ _)
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)

/-- **`hfired` for `cong_headUnion`.** The head's own `union`, at the same substitution: the
pair the source's head asserted is a pair the round's post-state asserts. `hlet` is what it
is in `mem_terms_of_headBuild`. -/
theorem mem_eqs_of_headUnion {R : RulesetName} {c : Cmd} {sd sd' : Database}
    {r : Rule} (hfire : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') (hw : sd.WF)
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hsc : r.HeadScoped sd)
    (hb : Actions.Builds r.actions sd.sig) (hun : Actions.UnionRunnable r.actions sd)
    {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {e₁ e₂ : Expr} (ha : Action.union e₁ e₂ ∈ r.actions)
    (hlet : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∉ Actions.letVars r.actions)
    {t₁ t₂ : Term} (hv₁ : e₁.eval sd.sig (sd.env ++ τ) = some t₁)
    (hv₂ : e₂.eval sd.sig (sd.env ++ τ) = some t₂) : (t₁, t₂) ∈ sd'.eqs := by
  obtain ⟨δ, e, e', hdom, hsig, henv, hs, -, heqs⟩ :=
    exists_headStep_of_ruleFired hfire hstep hw hr hrs hsc hb hun hq _ ha
  have hagree : ∀ v ∈ e₁.vars ∪ e₂.vars,
      Env.lookup v e.env = Env.lookup v (sd.env ++ τ) := by
    intro v hv
    rw [henv]
    exact Env.lookup_append_of_not_mem fun hc => hlet v hv (hdom v hc)
  have he₁ : e₁.eval e.sig e.env = some t₁ := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _
      (fun v hv => hagree v (List.mem_union_iff.mpr (Or.inl hv)))]
    exact hv₁
  have he₂ : e₂.eval e.sig e.env = some t₂ := by
    rw [hsig, Expr.eval_agreeOn (sig := sd.sig) _
      (fun v hv => hagree v (List.mem_union_iff.mpr (Or.inr hv)))]
    exact hv₂
  rcases evalAction_eq_some hs with ⟨g, t, hg, -, -⟩ | ⟨v, g, t, hg, -, -⟩ |
      ⟨g₁, g₂, u₁, u₂, hg, hu₁, hu₂, -, rfl⟩ | ⟨g, cs, out, as, vs, hg, -, -, -⟩
  · exact absurd hg (by simp)
  · exact absurd hg (by simp)
  · obtain ⟨rfl, rfl⟩ : g₁ = e₁ ∧ g₂ = e₂ := by
      injection hg with h₁ h₂
      exact ⟨h₁.symm, h₂.symm⟩
    obtain rfl : u₁ = t₁ := Option.some.inj (hu₁.symm.trans he₁)
    obtain rfl : u₂ = t₂ := Option.some.inj (hu₂.symm.trans he₂)
    exact heqs _ (by rw [Database.addEq_eqs]; exact Set.mem_insert _ _)
  · exact absurd hg (by simp)

/-! ##### The two domain clauses, as the block's hypotheses

`EncodeDomain.headsDeclared` is `Actions.Declared` at the signature the source program's
prefix has installed, and the state a firing reads is later than that — `Cmd.sigBind` only
ever writes a `some`, so a name declared before the rule is declared at the firing
(`Proofs/Step.lean`'s `Signature.extends_sigBind` and `Actions.Declared.mono`).
`EncodeDomain.noPrim` and `ctorsOnly` then turn declaredness into `Signature.IsCtor`, which is
what `Expr.eval` needs. -/

/-- An expression's own `Expr.ctors` are among the list's. -/
theorem Expr.mem_ctorsList {es : List Expr} {e : Expr} (he : e ∈ es) {p : FnName × Nat}
    (hp : p ∈ e.ctors) : p ∈ Expr.ctorsList es := by
  induction es with
  | nil => simp at he
  | cons x xs ih =>
      rw [Expr.ctorsList]
      rcases List.mem_cons.mp he with rfl | he'
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (ih he')

/-- **A declared name that is no primitive is a constructor**, on a constructor-only
signature. This is the whole of what `headsDeclared` buys `Expr.eval`. -/
theorem Expr.Evaluable.of_declared {sig : Signature} (hac : sig.AllConstructors) {e : Expr}
    (hp : ∀ f ∈ e.fns, Prim.ofName f = none) (h : e.Declared sig) : e.Evaluable sig := by
  intro f hf
  refine ⟨hp f hf, ?_⟩
  obtain hd := (h f hf).resolve_left (by rw [hp f hf]; simp)
  obtain ⟨d, hdd⟩ := Option.ne_none_iff_exists'.mp hd
  refine Signature.isCtor_of_decl hdd ?_
  have hm := hac f
  rw [Signature.mergeOf, hdd, Option.bind_some] at hm
  exact hm

@[inherit_doc Expr.Evaluable.of_declared]
theorem Action.Builds.of_declared {sig : Signature} (hac : sig.AllConstructors) {a : Action}
    (hp : ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none) (h : a.Declared sig) :
    a.Builds sig := by
  cases a with
  | expr e => exact Expr.Evaluable.of_declared hac (noPrim_fns hp) h
  | letBind v e => exact Expr.Evaluable.of_declared hac (noPrim_fns hp) h
  | union e₁ e₂ =>
      exact ⟨Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_left _ hk)) h.1,
        Expr.Evaluable.of_declared hac
          (noPrim_fns fun fk hk => hp fk (List.mem_append_right _ hk)) h.2⟩
  | set f args out =>
      refine ⟨fun e he => Expr.Evaluable.of_declared hac (fun g hg => ?_) (h.2.1 e he),
        fun e he => Expr.Evaluable.of_declared hac (fun g hg => ?_) (h.2.2 e he)⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
        exact hp (g, k) (List.mem_cons_of_mem _
          (List.mem_append_left _ (Expr.mem_ctorsList he hk)))
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg
        exact hp (g, k) (List.mem_cons_of_mem _
          (List.mem_append_right _ (Expr.mem_ctorsList he hk)))

@[inherit_doc Expr.Evaluable.of_declared]
theorem Actions.Builds.of_declared {sig : Signature} (hac : sig.AllConstructors) :
    ∀ {as : List Action}, (∀ a ∈ as, ∀ fk ∈ a.ctors, Prim.ofName fk.1 = none) →
      Actions.Declared as sig → Actions.Builds as sig
  | [], _, _ => trivial
  | a :: _, hp, h =>
      ⟨Action.Builds.of_declared hac (hp a List.mem_cons_self) h.1,
        Actions.Builds.of_declared hac (fun b hb => hp b (List.mem_cons_of_mem _ hb)) h.2⟩

/-! ##### The two domain clauses, as state invariants

`headsDeclared` is threaded along `Cmd.sigBind` and a rule fires from `db.rules`, so what a
firing needs is not a fact about the program's text but the same fact carried on the state:
every rule the state holds has a head that builds at the state's own signature. -/

/-- What one source command must be for a rule it registers to have a runnable head:
`Spec/Scope.lean`'s `Actions.Declared` at the signature standing when the rule is read, and no
applied name a primitive. `EncodeDomain.headsDeclared` and `.noPrim` are exactly the two. -/
def Cmd.HeadRuns (c : Cmd) (sig : Signature) : Prop :=
  c.HeadsDeclared sig ∧ ∀ fk ∈ c.ctors, Prim.ofName fk.1 = none

/-- `Cmd.HeadRuns` along the program, as `Program.HeadsDeclared` is. -/
@[simp] def Program.HeadRuns : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.HeadRuns sig ∧ Program.HeadRuns cs (c.sigBind sig)

/-- **Every rule the state holds has a head that builds.** The invariant a firing spends:
`Actions.Builds` is what `evalLocalActions_isSome_of_builds` asks and it is asked at the
state's own signature, not at the program's. -/
def Database.HeadsBuild (db : Database) : Prop :=
  ∀ r ∈ db.rules, Actions.Builds r.actions db.sig

theorem Database.empty_headsBuild : Database.empty.HeadsBuild := by
  intro r hr; exact absurd hr (by simp [Database.empty])

/-- Evaluability survives a constructor declaration: `Signature.IsCtor.update` is the clause
`Cmd.CtorDecl` buys. -/
theorem Expr.Evaluable.update {sig : Signature} {f : FnName} {d : FnDecl}
    (hd : d.merge = none) {e : Expr} (h : e.Evaluable sig) :
    e.Evaluable (Function.update sig f (some d)) :=
  fun g hg => ⟨(h g hg).1, Signature.IsCtor.update hd (h g hg).2⟩

theorem Action.Builds.update {sig : Signature} {f : FnName} {d : FnDecl}
    (hd : d.merge = none) {a : Action} (h : a.Builds sig) :
    a.Builds (Function.update sig f (some d)) := by
  cases a with
  | expr e => exact Expr.Evaluable.update hd h
  | letBind v e => exact Expr.Evaluable.update hd h
  | union e₁ e₂ => exact ⟨Expr.Evaluable.update hd h.1, Expr.Evaluable.update hd h.2⟩
  | set g args out =>
      exact ⟨fun e he => Expr.Evaluable.update hd (h.1 e he),
        fun e he => Expr.Evaluable.update hd (h.2 e he)⟩

theorem Actions.Builds.update {sig : Signature} {f : FnName} {d : FnDecl} (hd : d.merge = none) :
    ∀ {as : List Action}, Actions.Builds as sig →
      Actions.Builds as (Function.update sig f (some d))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1.update hd, Actions.Builds.update hd h.2⟩

theorem cmdStep_headsBuild {db db' : Database} (hc : db.CtorState) (h : db.HeadsBuild)
    {c : Cmd} (hrun : c.HeadRuns db.sig) (hdecl : c.CtorDecl) (hstep : CmdStep db c db') :
    db'.HeadsBuild := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  cases c with
  | action a =>
      have hv : evalAction db a = some d := hreach
      obtain rfl : db' = d :=
        hcl.eq_of_allConstructors (by rw [evalAction_sig hv]; exact hc.sig)
      intro r hr
      rw [evalAction_sig hv]
      exact h r (by rw [← evalAction_rules hv]; exact hr)
  | rule r =>
      have hv : some { db with rules := insert r db.rules } = some d := hreach
      obtain rfl : d = { db with rules := insert r db.rules } := (Option.some.inj hv).symm
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact Actions.Builds.of_declared hc.sig
          (fun a ha fk hk => hrun.2 fk (by
            rw [Cmd.ctors]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)))
          hrun.1
      · exact h r' hr''
  | run R =>
      have hv : some (RunRules R db) = some d := hreach
      obtain rfl : d = RunRules R db := (Option.some.inj hv).symm
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      intro r hr
      rw [RunRules.sig]
      exact h r (by rw [RunRules, Database.sUnion_rules] at hr; exact hr)
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp ⟨d, hreach, hcl⟩
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.HeadsBuild) ?_ hsat.1
        ⟨hc, h⟩).2
      intro x y hx hxy
      obtain rfl : y = RunRules R x := hxy.eq_of_allConstructors hx.1.sig
      refine ⟨⟨RunRules.wf hx.1.wf, by rw [RunRules.sig]; exact hx.1.sig⟩, fun r hr => ?_⟩
      rw [RunRules.sig]
      exact hx.2 r (by rw [RunRules, Database.sUnion_rules] at hr; exact hr)
  | decl f dc =>
      have hv : some { db with sig := Function.update db.sig f (some dc) } = some d := hreach
      obtain rfl : d = { db with sig := Function.update db.sig f (some dc) } :=
        (Option.some.inj hv).symm
      obtain rfl : db' = { db with sig := Function.update db.sig f (some dc) } :=
        hcl.eq_of_allConstructors (hc.sig.sigBind hdecl)
      exact fun r hr => Actions.Builds.update hdecl (h r hr)

/-- **`Database.HeadsBuild` at every state a run reaches.** -/
theorem programStep_headsBuild {db db' : Database} (hc : db.CtorState) (h : db.HeadsBuild)
    {p : Program} (hrun : Program.HeadRuns p db.sig) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.HeadsBuild := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      refine ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_headsBuild hc h hrun.1 (hdecl c List.mem_cons_self) hstep) ?_
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
      rw [hstep.sig]; exact hrun.2

/-! ##### The invariants, from the domain -/

/-- **`Cmd.NoLits` from `noLitUnion`'s second arm and `noPrim`.** -/
theorem Cmd.NoLits.of_domain {P : Program} (hdom : P.EncodeDomain)
    (hlit : ∀ c ∈ P, c.litFreeB = true) {c : Cmd} (hc : c ∈ P) : c.NoLits := by
  cases c with
  | action a => exact ⟨hlit _ hc, fun fk hk => hdom.noPrim fk (mem_program_ctors hc hk)⟩
  | rule r =>
      intro a ha
      have hb := hlit _ hc
      rw [Cmd.litFreeB, List.all_eq_true] at hb
      refine ⟨hb a ha, fun fk hk => hdom.noPrim fk (mem_program_ctors hc ?_)⟩
      rw [Cmd.ctors]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)
  | run R => trivial
  | saturate R => trivial
  | decl f d => trivial

/-- **`Database.NoLits` at every state the source run reaches**, under `noLitUnion`'s second
arm. Applied to a *prefix* of the program it is the invariant at the state a firing command
starts from. -/
theorem noLits_of_programStep {P : Program} (hdom : P.EncodeDomain)
    (hlit : ∀ c ∈ P, c.litFreeB = true) {p : Program} (hp : ∀ c ∈ p, c ∈ P)
    {sd : Database} (hstep : ProgramStep Database.empty p sd) : sd.NoLits :=
  programStep_noLits Database.CtorState.empty Database.empty_noLits
    (fun c hc => Cmd.NoLits.of_domain hdom hlit (hp c hc))
    (fun c hc => hdom.ctorsOnly c (hp c hc)) hstep

/-- **`Program.HeadRuns` from `headsDeclared` and `noPrim`.** -/
theorem Program.HeadRuns.of_headsDeclared : ∀ {p : Program} {sig : Signature},
    Program.HeadsDeclared p sig → (∀ c ∈ p, ∀ fk ∈ c.ctors, Prim.ofName fk.1 = none) →
      Program.HeadRuns p sig
  | [], _, _, _ => trivial
  | _ :: _, _, h, hp =>
      ⟨⟨h.1, hp _ List.mem_cons_self⟩,
        Program.HeadRuns.of_headsDeclared h.2 fun c' hc' => hp c' (List.mem_cons_of_mem _ hc')⟩

/-- A prefix of a program whose heads run has heads that run. -/
theorem Program.HeadRuns.of_append : ∀ {p q : Program} {sig : Signature},
    Program.HeadRuns (p ++ q) sig → Program.HeadRuns p sig
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, Program.HeadRuns.of_append h.2⟩

/-- **`Database.HeadsBuild` at every state the source run reaches**, out of `headsDeclared`,
`noPrim` and `ctorsOnly`. -/
theorem headsBuild_of_programStep {P : Program} (hdom : P.EncodeDomain) {p q : Program}
    (hP : P = p ++ q) {sd : Database} (hstep : ProgramStep Database.empty p sd) :
    sd.HeadsBuild := by
  refine programStep_headsBuild Database.CtorState.empty Database.empty_headsBuild
    (Program.HeadRuns.of_append (q := q) ?_)
    (fun c hc => hdom.ctorsOnly c (by rw [hP]; exact List.mem_append_left _ hc)) hstep
  rw [← hP]
  exact Program.HeadRuns.of_headsDeclared hdom.headsDeclared
    fun c hc fk hk => hdom.noPrim fk (mem_program_ctors hc hk)

/-! ##### `hfired`, from the domain

Both shapes, with every hypothesis either the domain's or a fact about the firing. What is
**not** among them is the refuted one — that the key's application is a source term because
the target keyed on it. -/

/-- **`hfired` for `entrySound_headBuild`, from the domain.** -/
theorem mem_terms_of_headBuild_of_domain {P : Program} (hdom : P.EncodeDomain)
    {p q : Program} (hP : P = p ++ q) {sd : Database}
    (hpre : ProgramStep Database.empty p sd)
    {R : RulesetName} {c : Cmd} {sd' : Database} {r : Rule}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hmem : Cmd.rule r ∈ P)
    (hsc : r.HeadScoped sd) {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {f : FnName} {args : List Expr} (ha : Action.expr (.app f args) ∈ r.actions)
    (hlet : ∀ v ∈ (Expr.app f args).vars, v ∉ Actions.letVars r.actions)
    {is : List Term}
    (hval : (Expr.app f args).eval sd.sig (sd.env ++ τ) = some (.app f is)) :
    Term.app f is ∈ sd'.terms := by
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  refine mem_terms_of_headBuild hfire hstep hstate.wf hr hrs hsc
    (headsBuild_of_programStep hdom hP hpre r hr) ?_ hq ha hlet hval
  rcases hdom.noLitUnion with huf | hlit
  · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
  · exact Or.inr ⟨(noLits_of_programStep hdom hlit
      (fun c' hc' => by rw [hP]; exact List.mem_append_left _ hc') hpre).terms,
      Cmd.NoLits.of_domain hdom hlit hmem⟩

/-- **`hfired` for `cong_headUnion`, from the domain.** -/
theorem mem_eqs_of_headUnion_of_domain {P : Program} (hdom : P.EncodeDomain)
    {p q : Program} (hP : P = p ++ q) {sd : Database}
    (hpre : ProgramStep Database.empty p sd)
    {R : RulesetName} {c : Cmd} {sd' : Database} {r : Rule}
    (hfire : c = Cmd.run R ∨ c = Cmd.saturate R) (hstep : CmdStep sd c sd')
    (hr : r ∈ sd.rules) (hrs : r.ruleset = R) (hmem : Cmd.rule r ∈ P)
    (hsc : r.HeadScoped sd) {τ : Env} (hq : ValidQuerySubst sd r.query τ)
    {e₁ e₂ : Expr} (ha : Action.union e₁ e₂ ∈ r.actions)
    (hlet : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∉ Actions.letVars r.actions)
    {t₁ t₂ : Term} (hv₁ : e₁.eval sd.sig (sd.env ++ τ) = some t₁)
    (hv₂ : e₂.eval sd.sig (sd.env ++ τ) = some t₂) : (t₁, t₂) ∈ sd'.eqs := by
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  refine mem_eqs_of_headUnion hfire hstep hstate.wf hr hrs hsc
    (headsBuild_of_programStep hdom hP hpre r hr) ?_ hq ha hlet hv₁ hv₂
  rcases hdom.noLitUnion with huf | hlit
  · exact Or.inl ((Cmd.ruleUnionFreeB_iff r).mp (huf _ hmem))
  · exact Or.inr ⟨(noLits_of_programStep hdom hlit
      (fun c' hc' => by rw [hP]; exact List.mem_append_left _ hc') hpre).terms,
      Cmd.NoLits.of_domain hdom hlit hmem⟩


/-! ##### Both shapes, at firings that fire

`ENCODING.md`'s discipline. A `hfired` nothing satisfies would discharge
`entrySound_headBuild` and `cong_headUnion` for free, so each of the two is run at a source
state a program reaches, at a substitution the query really admits, and against a conclusion
the **pre**-state does not already hold.

The two witnesses are chosen to exercise the two arms of `noLitUnion` separately: `ncProgram`
has a union-free head and takes the first, `vuProgram` has a head that unions a **variable**
with an application and takes the second — the arm `Action.Evaluable`'s `Expr.IsApp` rejects
and the whole `Database.LitFree` invariant exists for.

`CmdStep` is a relation, so the round the witnesses step by is `RunRules` itself: no merge
phase fires on a constructor signature, and naming the post-state that way is what keeps the
kernel out of a rule-firing computation. -/

/-- `ncProgram` without its round. -/
def ncPrefix : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "B" { arity := 0, outArity := 1, merge := none },
   .decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "A" []])),
   .action (.expr (.app "B" [])),
   .action (.union (.app "A" []) (.app "B" [])),
   .rule ncRule]

/-- The state the round reads: `(F (A))`, `(A)`, `(B)`, the `union`'s equation, and `ncRule`.
It does **not** hold `(F (B))`. -/
def ncPre : FDatabase := (exec ncPrefix).getD FDatabase.empty

theorem ncPre_exec : exec ncPrefix = some ncPre := by
  obtain ⟨d, hd⟩ : ∃ d, exec ncPrefix = some d := Option.isSome_iff_exists.mp (by decide)
  rw [hd, ncPre, hd]
  rfl

theorem ncPrefix_programStep : ProgramStep Database.empty ncPrefix ncPre.toDatabase :=
  (exec_programStep
      (by intro c hc
          simp only [ncPrefix, List.mem_cons] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl])
      (Or.inr (by rw [ncPre_exec]; simp))).mp (by rw [ncPre_exec]; rfl)

theorem ncPre_rules : ncPre.rules = [ncRule] := rfl

theorem ncPre_mem_rule : ncRule ∈ ncPre.toDatabase.rules := by
  change ncRule ∈ ncPre.rules
  rw [ncPre_rules]
  exact List.mem_cons_self

theorem ncPre_env : ncPre.env = [] := by decide

/-- `?x` is the query's, so the head is scoped where it runs. -/
theorem ncRule_headScoped : ncRule.HeadScoped ncPre.toDatabase := by
  rw [Rule.HeadScoped]
  change Actions.Scoped ncRule.actions (Query.bind ncRule.query (Env.dom ncPre.env))
  rw [ncPre_env]
  simp [ncRule, Actions.Scoped, Action.Scoped, Expr.IsApp, Expr.Scoped, Expr.vars,
    Expr.varsList, Query.bind, Query.vars, Pattern.vars]

theorem ncPre_head_eval :
    (Expr.app "F" [.var "x"]).eval ncPre.toDatabase.sig
      (ncPre.toDatabase.env ++ [("x", ncB)]) = some ncFB := rfl

theorem ncPre_mem_B : ncB ∈ ncPre.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact (by decide : ncB ∈ ncPre.terms)

theorem ncPre_mem_FA : ncFA ∈ ncPre.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact (by decide : ncFA ∈ ncPre.terms)

/-- The `union`'s own equation at the round's pre-state. -/
theorem ncPre_cong_A_B : Cong ncPre.toDatabase ncA ncB :=
  Cong.assert (FDatabase.mem_toDatabase_eqs.mpr
    (Or.inr ⟨(by decide : (ncA, ncB) ∈ ncPre.eqs),
      (by decide : ncA ∈ ncPre.terms), (by decide : ncB ∈ ncPre.terms)⟩))

private theorem ncPre_contained_addFB :
    ncPre.toDatabase.Contained (ncPre.toDatabase.addTerm ncFB) :=
  ⟨fun p hp => by rw [Database.addTerm_eqs]; exact Or.inl hp⟩

/-- **The pattern matches at the non-leader member.** `(F (B))` is congruent to the held
`(F (A))` through the `union`, which is what `Matches` reads and what makes this firing the
one the encoded rule does not perform. -/
theorem ncPre_congOn_FA_FB : CongOn ncPre.toDatabase [ncFB] ncFA ncFB := by
  have hD : ncPre.toDatabase.withOperands [ncFB] = ncPre.toDatabase.addTerm ncFB := rfl
  rw [CongOn, hD]
  refine Cong.congr (f := "F") (as := [ncA]) (bs := [ncB]) ?_ ?_ ?_
  · exact Cong.mono ncPre_contained_addFB ncPre_mem_FA
  · exact Database.mem_addTerm ncFB ncPre.toDatabase
  · exact .cons (Cong.mono ncPre_contained_addFB ncPre_cong_A_B) .nil

theorem ncPre_validQuerySubst :
    ValidQuerySubst ncPre.toDatabase ncRule.query [("x", ncB)] := by
  refine ⟨[[("x", ncB)]], List.Forall₂.cons ⟨⟨?_, ?_⟩, ?_⟩ List.Forall₂.nil, .single _⟩
  · exact List.Perm.refl _
  · intro b hb
    obtain rfl : b = ("x", ncB) := by simpa using hb
    exact ncPre_mem_B
  · exact .expr ncPre_mem_FA ncPre_head_eval ncPre_congOn_FA_FB

theorem ncPre_cmdStep_run :
    CmdStep ncPre.toDatabase (.run "r") (RunRules "r" ncPre.toDatabase) :=
  ⟨_, rfl, .refl⟩

/-- **`hfired`'s build shape, discharged at a firing that really fires.** Every hypothesis of
`mem_terms_of_headBuild_of_domain` holds together at `ncProgram`'s own round, and the
conclusion is a term the round's **pre**-state does not hold — so the lemma is not carried
here by a state that already had the answer.

The substitution is `?x ↦ (B)`, the *non-leader* member of the class: this is the very firing
`Database.ReadsSelf` was refuted on (`ncTgt_not_readsSelf`), and soundness is indifferent to
the encoded rule not performing it. -/
theorem mem_terms_of_headBuild_witness :
    ncFB ∉ ncPre.toDatabase.terms ∧ ncFB ∈ (RunRules "r" ncPre.toDatabase).terms := by
  refine ⟨?_, ?_⟩
  · rw [FDatabase.toDatabase_terms]; exact (by decide : ncFB ∉ ncPre.terms)
  · exact mem_terms_of_headBuild_of_domain ncProgram_encodeDomain
      (show ncProgram = ncPrefix ++ [Cmd.run "r"] from rfl) ncPrefix_programStep
      (Or.inl rfl) ncPre_cmdStep_run ncPre_mem_rule rfl
      (by simp [ncProgram]) ncRule_headScoped ncPre_validQuerySubst
      (by simp [ncRule]) (by simp [ncRule, Actions.letVars, Action.letVars])
      ncPre_head_eval

/-! ##### And the arm the literal-free invariant is for

A rule head that unions a **variable** with an application. `Action.Evaluable` rejects it —
its `union` clause asks `Expr.IsApp` of both operands — and `noLitUnion`'s first arm does not
apply either, since the head does assert an equation. What runs it is the second arm, and
what makes `evalAction`'s own `t₁.isLit` check pass is `Database.LitFree` at the round's
pre-state: the variable is bound to a term the source holds, and the source holds no
literal. -/

/-- A head that unions its query variable with a constructor. -/
def vuRule : Rule where
  query := [.expr (.app "F" [.var "x"])]
  actions := [.union (.var "x") (.app "B" [])]
  ruleset := "r"

@[inherit_doc vuRule]
def vuProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "B" { arity := 0, outArity := 1, merge := none },
   .decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "A" []])),
   .action (.expr (.app "B" [])),
   .rule vuRule,
   .run "r"]

/-- `vuProgram` without its round. -/
def vuPrefix : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "B" { arity := 0, outArity := 1, merge := none },
   .decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "A" []])),
   .action (.expr (.app "B" [])),
   .rule vuRule]

private theorem vuRule_queryEncodable : (Cmd.rule vuRule).QueryEncodable := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain rfl : p = Pattern.expr (.app "F" [.var "x"]) := by simpa [vuRule] using hp
    refine ⟨?_, trivial⟩
    intro l
    simp
  · intro v hv
    obtain rfl : v = "x" := by
      simpa [vuRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList] using hv
    refine ⟨Pattern.expr (.app "F" [.var "x"]), by simp [vuRule], ?_⟩
    simp [Pattern.ArgVar, Expr.ArgVar]

theorem vuProgram_encodeDomain : vuProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc
    simp only [vuProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [vuProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact vuRule_queryEncodable
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inr (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

/-- **And the first arm really fails here**, so the witness below runs the second and not a
disjunction it satisfies twice over. -/
theorem vuProgram_not_ruleUnionFree : ¬ ∀ c ∈ vuProgram, c.ruleUnionFreeB = true := by decide

/-- The state `vuProgram`'s round reads. It asserts no equation between distinct terms. -/
def vuPre : FDatabase := (exec vuPrefix).getD FDatabase.empty

theorem vuPre_exec : exec vuPrefix = some vuPre := by
  obtain ⟨d, hd⟩ : ∃ d, exec vuPrefix = some d := Option.isSome_iff_exists.mp (by decide)
  rw [hd, vuPre, hd]
  rfl

theorem vuPrefix_programStep : ProgramStep Database.empty vuPrefix vuPre.toDatabase :=
  (exec_programStep
      (by intro c hc
          simp only [vuPrefix, List.mem_cons] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl])
      (Or.inr (by rw [vuPre_exec]; simp))).mp (by rw [vuPre_exec]; rfl)

theorem vuPre_rules : vuPre.rules = [vuRule] := rfl

theorem vuPre_mem_rule : vuRule ∈ vuPre.toDatabase.rules := by
  change vuRule ∈ vuPre.rules
  rw [vuPre_rules]
  exact List.mem_cons_self

theorem vuPre_env : vuPre.env = [] := by decide

theorem vuRule_headScoped : vuRule.HeadScoped vuPre.toDatabase := by
  rw [Rule.HeadScoped]
  change Actions.Scoped vuRule.actions (Query.bind vuRule.query (Env.dom vuPre.env))
  rw [vuPre_env]
  simp [vuRule, Actions.Scoped, Action.Scoped, Expr.Scoped, Expr.vars,
    Expr.varsList, Query.bind, Query.vars, Pattern.vars]

theorem vuPre_mem_A : ncA ∈ vuPre.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact (by decide : ncA ∈ vuPre.terms)

theorem vuPre_mem_FA : ncFA ∈ vuPre.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact (by decide : ncFA ∈ vuPre.terms)

theorem vuPre_query_eval :
    (Expr.app "F" [.var "x"]).eval vuPre.toDatabase.sig
      (vuPre.toDatabase.env ++ [("x", ncA)]) = some ncFA := rfl

/-- The operand that is a **variable**, evaluated: `(A)`, a term the source holds and — by
`Database.LitFree` — not a literal. -/
theorem vuPre_head_eval₁ :
    (Expr.var "x").eval vuPre.toDatabase.sig
      (vuPre.toDatabase.env ++ [("x", ncA)]) = some ncA := rfl

theorem vuPre_head_eval₂ :
    (Expr.app "B" []).eval vuPre.toDatabase.sig
      (vuPre.toDatabase.env ++ [("x", ncA)]) = some ncB := rfl

theorem vuPre_congOn_FA : CongOn vuPre.toDatabase [ncFA] ncFA ncFA := by
  have hD : vuPre.toDatabase.withOperands [ncFA] = vuPre.toDatabase.addTerm ncFA := rfl
  rw [CongOn, hD]
  exact Database.mem_addTerm ncFA vuPre.toDatabase

theorem vuPre_validQuerySubst :
    ValidQuerySubst vuPre.toDatabase vuRule.query [("x", ncA)] := by
  refine ⟨[[("x", ncA)]], List.Forall₂.cons ⟨⟨?_, ?_⟩, ?_⟩ List.Forall₂.nil, .single _⟩
  · exact List.Perm.refl _
  · intro b hb
    obtain rfl : b = ("x", ncA) := by simpa using hb
    exact vuPre_mem_A
  · exact .expr vuPre_mem_FA vuPre_query_eval vuPre_congOn_FA

theorem vuPre_cmdStep_run :
    CmdStep vuPre.toDatabase (.run "r") (RunRules "r" vuPre.toDatabase) :=
  ⟨_, rfl, .refl⟩

/-- **`hfired`'s `union` shape, discharged through `noLitUnion`'s second arm.** The pair the
head asserts is one the round's post-state asserts, and one the pre-state does not — so the
`Database.LitFree` invariant is doing work here rather than standing beside a state that had
already unioned the two. -/
theorem mem_eqs_of_headUnion_witness :
    (ncA, ncB) ∉ vuPre.toDatabase.eqs ∧
      (ncA, ncB) ∈ (RunRules "r" vuPre.toDatabase).eqs := by
  refine ⟨?_, ?_⟩
  · intro hc
    rcases FDatabase.mem_toDatabase_eqs.mp hc with ⟨he, -⟩ | ⟨hm, -⟩
    · exact absurd he (by simp [ncA, ncB])
    · exact absurd hm (by decide)
  · exact mem_eqs_of_headUnion_of_domain vuProgram_encodeDomain
      (show vuProgram = vuPrefix ++ [Cmd.run "r"] from rfl) vuPrefix_programStep
      (Or.inl rfl) vuPre_cmdStep_run vuPre_mem_rule rfl
      (by simp [vuProgram]) vuRule_headScoped vuPre_validQuerySubst
      (by simp [vuRule]) (by simp [vuRule, Actions.letVars, Action.letVars])
      vuPre_head_eval₁ vuPre_head_eval₂

/-! #### The rules an encoded target holds

The declaration invariant one level up. `Signature.MergeShape` had to be established at the
prelude and carried because `encodeCmds` emits no declaration; the same two-part shape works
for rules, because the two places a rule can come from are `encodePrelude`'s maintenance
families and `encodeCmd`'s `.rule` case, and no other command the encoding emits ever extends
`rules`. What it buys is the case split the rule-firing fold is: a firing is either an encoded
source rule's or a maintenance rule's, and there is no third kind. -/

/-- **Every rule an encoded program's state can hold.** Either the encoding of a source rule
of `P` — at whichever counters `encodeCmds` reached it with, which nothing below reads — or
one of `maintenanceRules P`. -/
def Rule.EncodedIn (P : Program) (r : Rule) : Prop :=
  (∃ (s : Rule) (i n : Nat), Cmd.rule s ∈ P ∧ r = (encodeRule i s n).1) ∨
    r ∈ maintenanceRules P

/-- The rule invariant, as a property of the state. -/
def FDatabase.RulesEncoded (d : FDatabase) (P : Program) : Prop :=
  ∀ r ∈ d.rules, r.EncodedIn P

/-- A command that cannot break it: anything but a `.rule`, whose rule has to be one. -/
def Cmd.RulesEncodedOk (P : Program) : Cmd → Prop
  | .rule r => r.EncodedIn P
  | _ => True

/-- **One command: only `Cmd.rule` extends `rules`.** Every other case is one of the three
`rules` field equations `Proofs/Merge.lean` already has. -/
theorem FDatabase.execCmdM_rulesEncoded {P : Program} {d d' : FDatabase} {c : Cmd}
    (hc : Cmd.RulesEncodedOk P c) (h : d.RulesEncoded P) (hs : d.execCmdM c = some d') :
    d'.RulesEncoded P := by
  cases c with
  | action a =>
      rw [FDatabase.execCmdM] at hs
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
      intro r hr
      rw [(FDatabase.mergeSaturateF_fields h₂).2.2, FDatabase.execAction_rules h₁] at hr
      exact h r hr
  | rule r =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs
      intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr''
      · exact hc
      · exact h r' hr''
  | run R =>
      rw [FDatabase.execCmdM] at hs
      intro r hr
      rw [(FDatabase.runRoundM_fields hs).2.2] at hr
      exact h r hr
  | saturate R =>
      rw [FDatabase.execCmdM] at hs
      intro r hr
      rw [(FDatabase.runSaturateM_fields runFuel hs).2.2] at hr
      exact h r hr
  | decl f dc =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs
      exact h

@[inherit_doc FDatabase.execCmdM_rulesEncoded]
theorem FDatabase.execProgramM_rulesEncoded {P : Program} {p : Program}
    (hp : ∀ c ∈ p, Cmd.RulesEncodedOk P c) :
    ∀ {d D : FDatabase}, d.RulesEncoded P → d.execProgramM p = some D → D.RulesEncoded P := by
  induction p with
  | nil =>
    intro d D h hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hrun
    exact hrun ▸ h
  | cons c cs ih =>
    intro d D h hrun
    rw [FDatabase.execProgramM] at hrun
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hrun
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
      (FDatabase.execCmdM_rulesEncoded (hp c List.mem_cons_self) h h₁) h₂

/-! ##### The two halves of the encoded program, again

`encodePrelude` is where every maintenance rule is; `encodeCmd`'s `.rule` case is where every
encoded source rule is; and every other command either declares, acts, runs or saturates. -/

/-- The per-rule proof constructors are declarations. -/
theorem rulesEncodedOk_ruleProofDecls (P : Program) : ∀ (rs : List Rule) (i : Nat),
    ∀ c ∈ ruleProofDecls rs i, Cmd.RulesEncodedOk P c
  | [], _ => by simp [ruleProofDecls]
  | r :: rs, i => by
      intro c hc
      rw [ruleProofDecls, List.mem_cons] at hc
      rcases hc with rfl | hc
      · trivial
      · exact rulesEncodedOk_ruleProofDecls P rs (i + 1) c hc

/-- **The prelude's rules, enumerated.** Everything before them declares, and the rules are
exactly `maintenanceRules P` mapped into commands. -/
theorem rulesEncodedOk_encodePrelude (P : Program) :
    ∀ c ∈ encodePrelude P, Cmd.RulesEncodedOk P c := by
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
      · exact rulesEncodedOk_ruleProofDecls P _ _ c h₂
    · rcases List.mem_cons.mp h₁ with rfl | h₂
      · trivial
      · obtain ⟨fk, -, h₃⟩ := List.mem_flatMap.mp h₂
        have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
        rcases h₄ with rfl | rfl | rfl <;> trivial
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact Or.inr hr

/-- **`encodeCmd` emits one rule and only for a source rule**, which is what makes the
invariant's first disjunct the *whole* of what a non-maintenance firing can be. -/
theorem rulesEncodedOk_encodeCmd {P : Program} {c : Cmd} (hc : c ∈ P) (n i : Nat) :
    ∀ c' ∈ (encodeCmd c n i).1, Cmd.RulesEncodedOk P c' := by
  intro c' hc'
  cases c with
  | action a =>
      have h : c' ∈ (encodeAction fiatE a n).1.map Cmd.action ++ [Cmd.saturate rebuildRuleset] :=
        hc'
      rcases List.mem_append.mp h with h₁ | h₁
      · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h₁
        trivial
      · obtain rfl : c' = Cmd.saturate rebuildRuleset := by simpa using h₁
        trivial
  | rule r =>
      have h : c' ∈ [Cmd.rule (encodeRule i r n).1] := hc'
      obtain rfl : c' = Cmd.rule (encodeRule i r n).1 := by simpa using h
      exact Or.inl ⟨r, i, n, hc, rfl⟩
  | run R =>
      have h : c' ∈ [Cmd.run R, Cmd.saturate rebuildRuleset] := hc'
      have h2 : c' = Cmd.run R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
      rcases h2 with rfl | rfl <;> trivial
  | saturate R =>
      have h : c' ∈ [Cmd.saturate R, Cmd.saturate rebuildRuleset] := hc'
      have h2 : c' = Cmd.saturate R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
      rcases h2 with rfl | rfl <;> trivial
  | decl f dc =>
      have h : c' ∈ ([] : Program) := hc'
      simp at h

@[inherit_doc rulesEncodedOk_encodeCmd]
theorem rulesEncodedOk_encodeCmds {P : Program} : ∀ (p : Program), (∀ c ∈ p, c ∈ P) →
    ∀ (n i : Nat), ∀ c' ∈ (encodeCmds p n i).1, Cmd.RulesEncodedOk P c'
  | [], _, _, _ => by simp [encodeCmds]
  | c :: cs, hp, n, i => by
      intro c' hc'
      have hsplit : (encodeCmds (c :: cs) n i).1
          = (encodeCmd c n i).1
            ++ (encodeCmds cs (encodeCmd c n i).2.1 (encodeCmd c n i).2.2).1 := rfl
      rw [hsplit] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact rulesEncodedOk_encodeCmd (hp c List.mem_cons_self) n i c' h
      · exact rulesEncodedOk_encodeCmds cs
          (fun x hx => hp x (List.mem_cons_of_mem c hx)) _ _ c' h

/-- **The rule invariant at the state `execM` returned.** The shape
`execM_encode_mergeShape` has for declarations. -/
theorem execM_encode_rules {P : Program} {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.RulesEncoded P := by
  rw [execM, encode] at htgt
  refine FDatabase.execProgramM_rulesEncoded
    (p := encodePrelude P ++ (encodeCmds P 0 0).1) (fun c hc => ?_) ?_ htgt
  · rcases List.mem_append.mp hc with h | h
    · exact rulesEncodedOk_encodePrelude P c h
    · exact rulesEncodedOk_encodeCmds P (fun _ hc' => hc') 0 0 c h
  · intro r hr
    exact absurd hr (by simp [FDatabase.empty])

/-- **A matched row atom's instance is a term the state holds.** -/
theorem mem_terms_of_patternHolds_values {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {vs as : List Expr} {f : FnName} {σ : Env}
    (h : patternHolds d (.values vs f as) σ = true) :
    ∃ ts us, Expr.evalList d.sig as (d.env ++ σ) = some ts ∧
      Expr.evalList d.sig vs (d.env ++ σ) = some us ∧
      Term.app f (ts ++ us) ∈ d.terms := by
  cases hv : Expr.evalList d.sig vs (d.env ++ σ) with
  | none => simp only [patternHolds, hv, Bool.false_eq_true] at h
  | some us =>
    cases ha : Expr.evalList d.sig as (d.env ++ σ) with
    | none => simp only [patternHolds, hv, ha, Bool.false_eq_true] at h
    | some ts =>
      refine ⟨ts, us, rfl, rfl, ?_⟩
      by_cases hmg : (d.sig.mergeOf f).isSome = true
      · simp only [patternHolds, hv, ha, hmg, if_true, List.any_eq_true,
          Bool.and_eq_true_iff, decide_eq_true_eq] at h
        obtain ⟨r, hmem, ⟨⟨hfn, hargs⟩, hout⟩⟩ := h
        have hcl : ∀ p ∈ ((d.addTerms ts).addTerms us).closureF, p.1 = p.2 := by
          refine fun p hp => diag_closureF (fun q hq => ?_) hp
          rw [FDatabase.addTerms_eqs, FDatabase.addTerms_eqs] at hq
          exact hr q hq
        obtain rfl : ts = r.args := eq_of_congrKeys hcl hargs
        obtain rfl : us = r.out := eq_of_congrKeys hcl hout
        have hmt := mem_terms_of_indexOk hr hidx hmem
          (by rw [hfn]; intro hc; rw [hc] at hmg; simp at hmg)
        rw [hfn] at hmt
        exact hmt
      · rw [Bool.not_eq_true] at hmg
        simp only [patternHolds, hv, ha, hmg, Bool.false_eq_true, if_false,
          decide_eq_true_eq] at h
        obtain ⟨w, hw, hcl⟩ := h
        have hdiag : ∀ p ∈ (d.addTerm (Term.app f (ts ++ us))).closureF, p.1 = p.2 :=
          fun p hp => diag_closureF
            (fun q hq => hr q (by rw [FDatabase.addTerm_eqs] at hq; exact hq)) hp
        obtain rfl : w = Term.app f (ts ++ us) := hdiag (w, Term.app f (ts ++ us)) hcl
        exact hw

/-! ##### The substitution a pattern was checked at, and the one the head runs under -/

/-- A binding a restricted substitution answers with is one the full substitution answers
with, the globals shadowing both alike. -/
theorem lookup_append_of_refines {env ρ σ : Env} (hr : Env.Refines ρ σ) {v : Var} {t : Term}
    (h : Env.lookup v (env ++ ρ) = some t) : Env.lookup v (env ++ σ) = some t := by
  by_cases hv : v ∈ Env.dom env
  · rw [Env.lookup_append_of_mem hv]
    rw [Env.lookup_append_of_mem hv] at h
    exact h
  · rw [Env.lookup_append_of_not_mem hv]
    rw [Env.lookup_append_of_not_mem hv] at h
    exact hr (v, t) (Env.mem_of_lookup h)

mutual

/-- **An evaluation survives un-restricting the substitution.** `Expr.eval` reads the
environment only through `Env.lookup`, so what the pattern's own restriction pinned down the
whole match pins down too — which is what lets a query atom's reading be used at the
environment the *head* runs in. -/
theorem Expr.eval_of_refines {sig : Signature} {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (e : Expr) {t : Term}, e.eval sig (env ++ ρ) = some t → e.eval sig (env ++ σ) = some t
  | .lit _, _, h => h
  | .var _, _, h => by
      rw [Expr.eval] at h ⊢
      exact lookup_append_of_refines hr h
  | .app f args, _, h => by
      cases hp : Prim.ofName f with
      | some p =>
        simp only [Expr.eval, hp] at h ⊢
        obtain ⟨ts, hts, hap⟩ := Option.bind_eq_some_iff.mp h
        rw [Expr.evalList_of_refines hr args hts]
        exact hap
      | none =>
        simp only [Expr.eval, hp] at h ⊢
        by_cases hct : sig.IsCtor f
        · rw [if_pos hct] at h ⊢
          obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
          rw [Expr.evalList_of_refines hr args hts]
          exact congrArg some hap
        · rw [if_neg hct] at h
          exact absurd h (by simp)

@[inherit_doc Expr.eval_of_refines]
theorem Expr.evalList_of_refines {sig : Signature} {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (es : List Expr) {ts : List Term},
      Expr.evalList sig es (env ++ ρ) = some ts → Expr.evalList sig es (env ++ σ) = some ts
  | [], _, h => h
  | e :: es, _, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_of_refines hr e ht, Expr.evalList_of_refines hr es hts]
      exact congrArg some hcons

end

/-- Every pattern of a matched query holds, at its own restriction of the substitution. -/
theorem patternHolds_of_mem_matchQuery {d : FDatabase} {q : Query} {σ : Env}
    (h : σ ∈ matchQuery d q) {p : Pattern} (hp : p ∈ q) :
    patternHolds d p (Env.canon (p.freeVars d.env) σ) = true := by
  rw [matchQuery, List.mem_filter] at h
  exact List.all_eq_true.mp h.2 p hp

/-- **A matched query's row atom, read at the substitution its head runs under.** -/
theorem mem_terms_of_mem_matchQuery_values {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {q : Query} {σ : Env} (hσ : σ ∈ matchQuery d q) {vs as : List Expr} {f : FnName}
    (hp : Pattern.values vs f as ∈ q) :
    ∃ ts us, Expr.evalList d.sig as (d.env ++ σ) = some ts ∧
      Expr.evalList d.sig vs (d.env ++ σ) = some us ∧
      Term.app f (ts ++ us) ∈ d.terms := by
  obtain ⟨ts, us, ha, hv, hmem⟩ :=
    mem_terms_of_patternHolds_values hr hidx (patternHolds_of_mem_matchQuery hσ hp)
  exact ⟨ts, us, Expr.evalList_of_refines Env.refines_canon as ha,
    Expr.evalList_of_refines Env.refines_canon vs hv, hmem⟩

/-! ##### The one `set` a maintenance head is -/

/-- **A block that is one `set`, read back.** The environment and rule list come back from the
pre-state, so what the firing contributes to `terms` is exactly the entry the `set` recorded. -/
theorem execLocalActions_set {d d' : FDatabase} {g : FnName} {args out : List Expr} {σ : Env}
    (h : execLocalActions d [.set g args out] σ = some d') :
    ∃ es vs, Expr.evalList d.sig args (d.env ++ σ) = some es ∧
      Expr.evalList d.sig out (d.env ++ σ) = some vs ∧
      ∀ t ∈ d'.terms, t ∈ (FDatabase.addRow g es vs d).terms := by
  rw [execLocalActions] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [execActions] at he
  obtain ⟨e₁, he₁, he₂⟩ := Option.bind_eq_some_iff.mp he
  rw [execActions, Option.some.injEq] at he₂
  subst he₂
  rw [execAction] at he₁
  obtain ⟨es, hes, he₁⟩ := Option.bind_eq_some_iff.mp he₁
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp he₁
  exact ⟨es, vs, hes, hvs, fun t ht => ht⟩

/-! ##### The proof shells a maintenance head mints -/

/-- **A view is never a congruence head**, whatever the constructor and whatever the arity:
`Nat.isDigit_of_mem_toDigits` is what says the arity suffix carries no `'w'`. -/
theorem viewName_ne_congrName {f : FnName} {k : Nat} : viewName f ≠ congrName k := by
  intro h
  have hw : 'w' ∈ (viewName f).toList := by
    rw [viewName, String.toList_append]
    exact List.mem_append_right _ (by decide)
  rw [h, congrName, String.toList_append] at hw
  rcases List.mem_append.mp hw with h1 | h1
  · exact absurd h1 (by decide)
  · have hd := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
      (show 'w' ∈ Nat.toDigits 10 k by rw [Nat.toString_eq_repr, Nat.toList_repr] at h1; exact h1)
    simp at hd

@[inherit_doc viewName_ne_congrName]
theorem ufName_ne_congrName {k : Nat} : ufName ≠ congrName k := by
  intro h
  have hw : 'U' ∈ ufName.toList := by rw [ufName]; decide
  rw [h, congrName, String.toList_append] at hw
  rcases List.mem_append.mp hw with h1 | h1
  · exact absurd h1 (by decide)
  · have hd := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
      (show 'U' ∈ Nat.toDigits 10 k by rw [Nat.toString_eq_repr, Nat.toList_repr] at h1; exact h1)
    simp at hd

/-- `@Congr_k` is neither shape, which is what a column rule's proof column costs. -/
theorem not_entryShaped_congr {k : Nat} {as : List Term} :
    ¬ (Term.app (congrName k) as).EntryShaped :=
  not_entryShaped_of_ne (fun _ h => viewName_ne_congrName h.symm)
    (fun h => ufName_ne_congrName h.symm)

/-- **A minted shell of neither shape, at any depth.** `entryShaped_mem_of_columns` with the
"is not the written term" side condition replaced by the shape refutation, so that the
encoding's nested proof nodes can be peeled one at a time. -/
theorem entryShaped_mem_of_shell {d : FDatabase} {g : FnName} {as : List Term}
    (hsh : ¬ (Term.app g as).EntryShaped)
    (ha : ∀ a ∈ as, ∀ s ∈ a.subtermList, s.EntryShaped → s ∈ d.terms) :
    ∀ s ∈ (Term.app g as).subtermList, s.EntryShaped → s ∈ d.terms := by
  intro s hs hshaped
  rw [Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact absurd hshaped hsh
  · obtain ⟨c, hc, hsub⟩ := (Term.mem_subtermListL _).mp hs
    exact ha c hc s ((Term.mem_subtermList c).mpr hsub) hshaped

/-! ##### Three list facts about `Expr.evalList` -/

/-- Every value an operand list evaluates to is some operand's. -/
theorem Expr.exists_of_mem_evalList {sig : Signature} {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ t ∈ ts, ∃ e ∈ es, e.eval sig ρ = some t
  | [], _, h, t, ht => by
      rw [Expr.evalList, Option.some.injEq] at h
      cases h
      simp at ht
  | e :: es, _, h, t, ht => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨e, List.mem_cons_self, hu⟩
      · obtain ⟨e', he', hev⟩ := Expr.exists_of_mem_evalList hus t ht'
        exact ⟨e', List.mem_cons_of_mem _ he', hev⟩

/-- The value at one position is that operand's. -/
theorem Expr.getElem?_of_evalList {sig : Signature} {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ (i : Nat) {e : Expr}, es[i]? = some e →
        ∃ t, ts[i]? = some t ∧ e.eval sig ρ = some t
  | [], _, _, i, _, hi => by simp at hi
  | e :: es, _, h, 0, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain rfl : e = e' := by simpa using hi
      exact ⟨u, by simp, hu⟩
  | e :: es, _, h, i + 1, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hus i (by simpa using hi)
      exact ⟨t, by simpa using ht, hev⟩

/-- Replacing one operand replaces one value: what a column rule's key expression is. -/
theorem Expr.evalList_set {sig : Signature} {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ (i : Nat) {e : Expr} {t : Term}, e.eval sig ρ = some t →
        Expr.evalList sig (es.set i e) ρ = some (ts.set i t)
  | [], _, h, _, _, _, _ => by
      rw [Expr.evalList, Option.some.injEq] at h
      cases h
      simp
  | a :: as, _, h, 0, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_zero, List.set_cons_zero, Expr.evalList, he, Option.bind_some, hus]
      rfl
  | a :: as, _, h, i + 1, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_succ, List.set_cons_succ, Expr.evalList, hu, Option.bind_some,
        Expr.evalList_set hus i he]
      rfl

/-- A singleton operand list. -/
theorem Expr.evalList_single {sig : Signature} {ρ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList sig [e] ρ = some ts) : ∃ t, e.eval sig ρ = some t ∧ ts = [t] := by
  rw [Expr.evalList] at h
  obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
  rw [Expr.evalList, Option.some.injEq] at hus
  exact ⟨t, ht, by rw [← hus]⟩

/-! ##### The value a minted proof term has

The clause `FDatabase.SoundTerms.addTerm_top` asks at a written term's *subterms* is answered
at a proof column by the shape of the vocabulary that built it: no head the encoding applies
inside a proof is a view or `@UF`, and a primitive answers with a literal or with one of its
own operands, so what the clause has to answer for under a proof node is what its leaves —
the columns the match bound — already answer. -/

/-- A view is never `@Sym`, by the last character. -/
theorem viewName_ne_symName {f : FnName} : viewName f ≠ symName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, symName, String.toList_append, List.reverse_append] at h2

/-- A view is never `@Fiat`, by the last character. -/
theorem viewName_ne_fiatName {f : FnName} : viewName f ≠ fiatName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [viewName, fiatName, String.toList_append, List.reverse_append] at h2

/-- A literal is of neither shape. -/
theorem not_entryShaped_lit {l : Lit} : ¬ (Term.lit l).EntryShaped := by
  rintro (⟨f, cs, e, pf, h⟩ | ⟨x, p, pf, h⟩) <;> exact absurd h (by simp)

/-- A name that no entry term can be headed by. -/
def NotEntryHead (g : FnName) : Prop := (∀ f, g ≠ viewName f) ∧ g ≠ ufName

theorem notEntryHead_transName : NotEntryHead transName :=
  ⟨fun _ h => viewName_ne_transName h.symm, by decide⟩

theorem notEntryHead_symName : NotEntryHead symName :=
  ⟨fun _ h => viewName_ne_symName h.symm, by decide⟩

theorem notEntryHead_fiatName : NotEntryHead fiatName :=
  ⟨fun _ h => viewName_ne_fiatName h.symm, by decide⟩

theorem notEntryHead_congrName {k : Nat} : NotEntryHead (congrName k) :=
  ⟨fun _ h => viewName_ne_congrName h.symm, fun h => ufName_ne_congrName h.symm⟩

/-- **A primitive answers with a literal or with one of its operands.** `ordering-gt`, `min`
and `max` compute a literal; `if` selects between two values it was given. -/
theorem prim_apply_cases {p : Prim} {ts : List Term} {t : Term} (h : p.apply ts = some t) :
    (∃ l, t = Term.lit l) ∨ t ∈ ts := by
  unfold Prim.apply at h
  split at h
  · exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  · rename_i c a b
    rw [Option.some.injEq] at h
    subst h
    by_cases hc : c <;> simp [hc]
  · exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  · exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

mutual

/-- **Every view- or `@UF`-shaped subterm of a proof term's value is one the state holds.**
The two hypotheses are the whole of it: no head applied is an entry head, and the variables
the expression reads are bound to terms whose own entries the state holds. -/
theorem entryShaped_mem_of_eval {d : FDatabase} {sig : Signature} {ρ : Env} :
    ∀ (e : Expr), (∀ g ∈ e.fns, NotEntryHead g) →
      (∀ v ∈ e.vars, ∀ u, Env.lookup v ρ = some u →
        ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms) →
      ∀ {t : Term}, e.eval sig ρ = some t →
        ∀ s ∈ t.subtermList, s.EntryShaped → s ∈ d.terms
  | .lit l, _, _, t, h => by
      obtain rfl : t = Term.lit l := (Option.some.inj h).symm
      intro s hs hsh
      rw [Term.subtermList_lit, List.mem_singleton] at hs
      exact absurd (hs ▸ hsh) not_entryShaped_lit
  | .var v, _, hb, t, h => by
      rw [Expr.eval] at h
      exact hb v (by simp [Expr.vars]) t h
  | .app f args, hf, hb, t, h => by
      have hfl : ∀ g ∈ Expr.fnsList args, NotEntryHead g :=
        fun g hg => hf g (by rw [Expr.fns, List.mem_cons]; exact Or.inr hg)
      have hbl : ∀ v ∈ Expr.varsList args, ∀ u, Env.lookup v ρ = some u →
          ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms :=
        fun v hv => hb v (by rw [Expr.vars]; exact hv)
      cases hp : Prim.ofName f with
      | some p =>
          simp only [Expr.eval, hp] at h
          obtain ⟨ts, hargs, hap⟩ := Option.bind_eq_some_iff.mp h
          have hts := entryShaped_mem_of_evalList args hfl hbl hargs
          rcases prim_apply_cases hap with ⟨l, rfl⟩ | hmem
          · intro s hs hsh
            rw [Term.subtermList_lit, List.mem_singleton] at hs
            exact absurd (hs ▸ hsh) not_entryShaped_lit
          · exact hts t hmem
      | none =>
          simp only [Expr.eval, hp] at h
          by_cases hct : sig.IsCtor f
          · rw [if_pos hct] at h
            obtain ⟨ts, hargs, happ⟩ := Option.map_eq_some_iff.mp h
            have hts := entryShaped_mem_of_evalList args hfl hbl hargs
            obtain rfl : Term.app f ts = t := happ
            exact entryShaped_mem_of_shell
              (not_entryShaped_of_ne (hf f (by simp [Expr.fns])).1
                (hf f (by simp [Expr.fns])).2) hts
          · rw [if_neg hct] at h
            exact absurd h (by simp)

@[inherit_doc entryShaped_mem_of_eval]
theorem entryShaped_mem_of_evalList {d : FDatabase} {sig : Signature} {ρ : Env} :
    ∀ (es : List Expr), (∀ g ∈ Expr.fnsList es, NotEntryHead g) →
      (∀ v ∈ Expr.varsList es, ∀ u, Env.lookup v ρ = some u →
        ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms) →
      ∀ {ts : List Term}, Expr.evalList sig es ρ = some ts →
        ∀ u ∈ ts, ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms
  | [], _, _, ts, h => by
      rw [Expr.evalList, Option.some.injEq] at h
      subst h
      intro u hu
      simp at hu
  | e :: es, hf, hb, ts, h => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact entryShaped_mem_of_eval e
          (fun g hg => hf g (by rw [Expr.fnsList]; simp [hg]))
          (fun v hv => hb v (by rw [Expr.varsList]; simp [hv])) ht
      · exact entryShaped_mem_of_evalList es
          (fun g hg => hf g (by rw [Expr.fnsList]; simp [hg]))
          (fun v hv => hb v (by rw [Expr.varsList]; simp [hv])) hus u hu'

end

/-! ##### Two more list facts -/

/-- A member of a list one position was replaced in is a member or the replacement. -/
theorem mem_or_eq_of_mem_set {α : Type _} {l : List α} {i : Nat} {b a : α}
    (h : a ∈ l.set i b) : a ∈ l ∨ a = b := by
  induction l generalizing i with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero =>
      rw [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ j =>
      rw [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact (ih h).imp (List.mem_cons_of_mem _) id

/-! ##### The three families, one firing each

Each rule's query is two row atoms and its head is one `set`, so each proof is the same three
moves: read the two atoms back as entry terms (`mem_terms_of_mem_matchQuery_values`), justify
them against the invariant, and hand the written entry to the one lemma its family is
(`EntrySound.eclass`, `EntrySound.column`, `cong_of_pathCompress`). -/

/-- **`pathCompressRule`'s firing.** Two `@UF` edges compose. -/
theorem pathCompressRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : d.SoundTerms src)
    (hσ : σ ∈ matchQuery d pathCompressRule.query)
    (hf : execLocalActions d pathCompressRule.actions σ = some d') : d'.SoundTerms src := by
  obtain ⟨ts₁, us₁, ha₁, hv₁, hm₁⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@b", Expr.var "@p"]) (f := ufName) (as := [Expr.var "@a"])
    (by simp [pathCompressRule])
  obtain ⟨a, hla, rfl⟩ := Expr.evalList_single ha₁
  obtain ⟨b, p, hlb, hlp, rfl⟩ := Expr.evalList_pair hv₁
  obtain ⟨ts₂, us₂, ha₂, hv₂, hm₂⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@c", Expr.var "@q"]) (f := ufName) (as := [Expr.var "@b"])
    (by simp [pathCompressRule])
  obtain ⟨b', hlb', rfl⟩ := Expr.evalList_single ha₂
  obtain ⟨c, q, hlc, hlq, rfl⟩ := Expr.evalList_pair hv₂
  obtain rfl : b = b' := Option.some.inj (hlb.symm.trans hlb')
  have hab : Cong src a b := h.2 a b p hm₁
  have hbc : Cong src b c := h.2 b c q hm₂
  have ham : a ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₁ (by simp)
  have hpm : p ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₁ (by simp)
  have hcm : c ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₂ (by simp)
  have hqm : q ∈ d.terms := FDatabase.mem_terms_of_column hsc hm₂ (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_set hf
  obtain ⟨a', hla', rfl⟩ := Expr.evalList_single hesh
  obtain rfl : a = a' := Option.some.inj (hla.symm.trans hla')
  obtain ⟨c', pf, hlc', hpf, rfl⟩ := Expr.evalList_pair hvsh
  obtain rfl : c = c' := Option.some.inj (hlc.symm.trans hlc')
  refine FDatabase.SoundTerms.mono_terms hterms (h.addRow_top ?_ ?_ ?_)
  · refine entryShaped_mem_of_columns (fun z hz => ?_)
    have hz2 : z = a ∨ z = c ∨ z = pf := by simpa using hz
    rcases hz2 with rfl | rfl | rfl
    · exact entryShaped_mem_of_held hsc ham
    · exact entryShaped_mem_of_held hsc hcm
    · refine entryShaped_mem_of_eval (transE (Expr.var "@p") (Expr.var "@q")) ?_ ?_ hpf
      · intro g hg
        obtain rfl : g = transName := by simpa [transE, Expr.fns, Expr.fnsList] using hg
        exact notEntryHead_transName
      · intro v hv u hu
        have hv2 : v = "@p" ∨ v = "@q" := by
          simpa [transE, Expr.vars, Expr.varsList] using hv
        rcases hv2 with rfl | rfl
        · obtain rfl : u = p := Option.some.inj (hu.symm.trans hlp)
          exact entryShaped_mem_of_held hsc hpm
        · obtain rfl : u = q := Option.some.inj (hu.symm.trans hlq)
          exact entryShaped_mem_of_held hsc hqm
  · intro f' cs' e' pf' hq
    exact absurd (Term.app.inj hq).1 (fun hz => viewName_ne_ufName hz.symm)
  · intro y z pf' hq
    obtain ⟨-, hcols⟩ := Term.app.inj hq
    have h3 : [a, c, pf] = [y, z, pf'] := hcols
    obtain rfl : a = y := (List.cons.inj h3).1
    obtain rfl : c = z := (List.cons.inj (List.cons.inj h3).2).1
    exact cong_of_pathCompress hab hbc

/-- **The e-class rebuild rule's firing.** The entry keeps its key and its e-class moves along
the edge the second atom matched, which is `EntrySound.eclass`. The key expression list is
whatever the rule was built over — nothing here reads `rebuildVars`. -/
theorem eclassRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env} {f : FnName}
    {cs : List Expr}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : d.SoundTerms src)
    (hσ : σ ∈ matchQuery d
      [Pattern.values [.var "@e", .var "@p"] (viewName f) cs,
       Pattern.values [.var "@x", .var "@q"] ufName [.var "@e"]])
    (hf : execLocalActions d
      [Action.set (viewName f) cs [.var "@x", transE (.var "@p") (.var "@q")]] σ = some d') :
    d'.SoundTerms src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@e", Expr.var "@p"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, p, hle, hlp, rfl⟩ := Expr.evalList_pair hvus
  have hes : EntrySound src f ts e := h.1 f ts e p hmv
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@x", Expr.var "@q"]) (f := ufName) (as := [Expr.var "@e"]) (by simp)
  obtain ⟨e', hle', rfl⟩ := Expr.evalList_single hats₂
  obtain ⟨x, q, hlx, hlq, rfl⟩ := Expr.evalList_pair hvus₂
  obtain rfl : e = e' := Option.some.inj (hle.symm.trans hle')
  have hex : Cong src e x := h.2 e x q hmu
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => FDatabase.mem_terms_of_column hsc hmv (List.mem_append_left _ hz)
  have hpm : p ∈ d.terms := FDatabase.mem_terms_of_column hsc hmv (by simp)
  have hxm : x ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  have hqm : q ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_set hf
  obtain rfl : esh = ts := Option.some.inj (hesh.symm.trans hats)
  obtain ⟨x', pf, hlx', hpf, rfl⟩ := Expr.evalList_pair hvsh
  obtain rfl : x = x' := Option.some.inj (hlx.symm.trans hlx')
  refine FDatabase.SoundTerms.mono_terms hterms (h.addRow_top ?_ ?_ ?_)
  · refine entryShaped_mem_of_columns (fun z hz => ?_)
    rcases List.mem_append.mp hz with hz' | hz'
    · exact entryShaped_mem_of_held hsc (hcol z hz')
    · have hz2 : z = x ∨ z = pf := by simpa using hz'
      rcases hz2 with rfl | rfl
      · exact entryShaped_mem_of_held hsc hxm
      · refine entryShaped_mem_of_eval (transE (Expr.var "@p") (Expr.var "@q")) ?_ ?_ hpf
        · intro g hg
          obtain rfl : g = transName := by simpa [transE, Expr.fns, Expr.fnsList] using hg
          exact notEntryHead_transName
        · intro v hv u hu
          have hv2 : v = "@p" ∨ v = "@q" := by
            simpa [transE, Expr.vars, Expr.varsList] using hv
          rcases hv2 with rfl | rfl
          · obtain rfl : u = p := Option.some.inj (hu.symm.trans hlp)
            exact entryShaped_mem_of_held hsc hpm
          · obtain rfl : u = q := Option.some.inj (hu.symm.trans hlq)
            exact entryShaped_mem_of_held hsc hqm
  · intro f' cs' e'' pf' hq
    obtain ⟨hfname, hcols⟩ := Term.app.inj hq
    obtain rfl : f' = f := viewName_inj hfname.symm
    obtain ⟨rfl, hlast⟩ := List.append_inj' hcols rfl
    obtain rfl : x = e'' := (List.cons.inj hlast).1
    exact hes.eclass hex
  · intro y z pf' hq
    exact absurd (Term.app.inj hq).1 viewName_ne_ufName

/-- **A column rebuild rule's firing.** Column `i` of the key moves along the edge and the
e-class stays, which is `EntrySound.column`. The proof column is the one that mints a
`@Congr_k`, and `entryShaped_mem_of_eval` is what makes that cost nothing. -/
theorem columnRule_soundTerms {src : Database} {d d' : FDatabase} {σ : Env} {f : FnName}
    {k i : Nat} {cs : List Expr} {cv : Var} (hcv : cs[i]? = some (.var cv))
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : d.SoundTerms src)
    (hσ : σ ∈ matchQuery d
      [Pattern.values [.var "@e", .var "@p"] (viewName f) cs,
       Pattern.values [.var "@x", .var "@q"] ufName [.var cv]])
    (hf : execLocalActions d
      [Action.set (viewName f) (cs.set i (.var "@x"))
        [.var "@e", transE (symE (congrE (congrChildren k i))) (.var "@p")]] σ = some d') :
    d'.SoundTerms src := by
  obtain ⟨ts, us, hats, hvus, hmv⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@e", Expr.var "@p"]) (f := viewName f) (as := cs) (by simp)
  obtain ⟨e, p, hle, hlp, rfl⟩ := Expr.evalList_pair hvus
  have hes : EntrySound src f ts e := h.1 f ts e p hmv
  obtain ⟨ts₂, us₂, hats₂, hvus₂, hmu⟩ := mem_terms_of_mem_matchQuery_values hr hidx hσ
    (vs := [Expr.var "@x", Expr.var "@q"]) (f := ufName) (as := [Expr.var cv]) (by simp)
  obtain ⟨c₀, hlc₀, rfl⟩ := Expr.evalList_single hats₂
  obtain ⟨x, q, hlx, hlq, rfl⟩ := Expr.evalList_pair hvus₂
  have hcx : Cong src c₀ x := h.2 c₀ x q hmu
  obtain ⟨t₀, ht₀, hev₀⟩ := Expr.getElem?_of_evalList hats i hcv
  obtain rfl : t₀ = c₀ := Option.some.inj (hev₀.symm.trans hlc₀)
  have hcol : ∀ z ∈ ts, z ∈ d.terms :=
    fun z hz => FDatabase.mem_terms_of_column hsc hmv (List.mem_append_left _ hz)
  have hem : e ∈ d.terms := FDatabase.mem_terms_of_column hsc hmv (by simp)
  have hpm : p ∈ d.terms := FDatabase.mem_terms_of_column hsc hmv (by simp)
  have hxm : x ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  have hqm : q ∈ d.terms := FDatabase.mem_terms_of_column hsc hmu (by simp)
  obtain ⟨esh, vsh, hesh, hvsh, hterms⟩ := execLocalActions_set hf
  obtain rfl : esh = ts.set i x :=
    Option.some.inj (hesh.symm.trans (Expr.evalList_set hats i hlx))
  obtain ⟨e'', pf, hle'', hpf, rfl⟩ := Expr.evalList_pair hvsh
  obtain rfl : e = e'' := Option.some.inj (hle.symm.trans hle'')
  refine FDatabase.SoundTerms.mono_terms hterms (h.addRow_top ?_ ?_ ?_)
  · refine entryShaped_mem_of_columns (fun z hz => ?_)
    rcases List.mem_append.mp hz with hz' | hz'
    · rcases mem_or_eq_of_mem_set hz' with hz'' | rfl
      · exact entryShaped_mem_of_held hsc (hcol z hz'')
      · exact entryShaped_mem_of_held hsc hxm
    · have hz2 : z = e ∨ z = pf := by simpa using hz'
      rcases hz2 with rfl | rfl
      · exact entryShaped_mem_of_held hsc hem
      · refine entryShaped_mem_of_eval
          (transE (symE (congrE (congrChildren k i))) (Expr.var "@p")) ?_ ?_ hpf
        · intro g hg
          have hg2 : g = transName ∨ g = symName ∨ g = congrName (congrChildren k i).length ∨
              g = fiatName := by
            rw [transE, Expr.fns, List.mem_cons] at hg
            rcases hg with rfl | hg
            · exact Or.inl rfl
            · obtain ⟨e₀, he₀, hg⟩ := Expr.mem_fnsList hg
              have he₁ : e₀ = symE (congrE (congrChildren k i)) ∨ e₀ = Expr.var "@p" := by
                simpa using he₀
              rcases he₁ with rfl | rfl
              · rw [symE, Expr.fns, List.mem_cons] at hg
                rcases hg with rfl | hg
                · exact Or.inr (Or.inl rfl)
                · obtain ⟨e₂, he₂, hg⟩ := Expr.mem_fnsList hg
                  obtain rfl : e₂ = congrE (congrChildren k i) := by simpa using he₂
                  rw [congrE, Expr.fns, List.mem_cons] at hg
                  rcases hg with rfl | hg
                  · exact Or.inr (Or.inr (Or.inl rfl))
                  · obtain ⟨e₃, he₃, hg⟩ := Expr.mem_fnsList hg
                    rw [congrChildren, List.mem_map] at he₃
                    obtain ⟨j, -, rfl⟩ := he₃
                    by_cases hj : j = i
                    · rw [if_pos hj, Expr.fns] at hg; simp at hg
                    · rw [if_neg hj, fiatE, Expr.fns, List.mem_cons] at hg
                      rcases hg with rfl | hg
                      · exact Or.inr (Or.inr (Or.inr rfl))
                      · rw [Expr.fnsList] at hg; simp at hg
              · rw [Expr.fns] at hg; simp at hg
          rcases hg2 with rfl | rfl | rfl | rfl
          · exact notEntryHead_transName
          · exact notEntryHead_symName
          · exact notEntryHead_congrName
          · exact notEntryHead_fiatName
        · intro v hv u hu
          have hv2 : v = "@q" ∨ v = "@p" := by
            rw [transE, Expr.vars] at hv
            obtain ⟨e₀, he₀, hv⟩ := Expr.mem_varsList hv
            have he₁ : e₀ = symE (congrE (congrChildren k i)) ∨ e₀ = Expr.var "@p" := by
              simpa using he₀
            rcases he₁ with rfl | rfl
            · rw [symE, Expr.vars] at hv
              obtain ⟨e₂, he₂, hv⟩ := Expr.mem_varsList hv
              obtain rfl : e₂ = congrE (congrChildren k i) := by simpa using he₂
              rw [congrE, Expr.vars] at hv
              obtain ⟨e₃, he₃, hv⟩ := Expr.mem_varsList hv
              rw [congrChildren, List.mem_map] at he₃
              obtain ⟨j, -, rfl⟩ := he₃
              by_cases hj : j = i
              · rw [if_pos hj, Expr.vars, List.mem_singleton] at hv
                exact Or.inl hv
              · rw [if_neg hj, fiatE, Expr.vars, Expr.varsList] at hv
                simp at hv
            · rw [Expr.vars, List.mem_singleton] at hv
              exact Or.inr hv
          rcases hv2 with rfl | rfl
          · obtain rfl : u = q := Option.some.inj (hu.symm.trans hlq)
            exact entryShaped_mem_of_held hsc hqm
          · obtain rfl : u = p := Option.some.inj (hu.symm.trans hlp)
            exact entryShaped_mem_of_held hsc hpm
  · intro f' cs' e₄ pf' hq
    obtain ⟨hfname, hcols⟩ := Term.app.inj hq
    obtain rfl : f' = f := viewName_inj hfname.symm
    obtain ⟨rfl, hlast⟩ := List.append_inj' hcols rfl
    obtain rfl : e = e₄ := (List.cons.inj hlast).1
    exact hes.column ht₀ hcx
  · intro y z pf' hq
    exact absurd (Term.app.inj hq).1 viewName_ne_ufName

/-! ##### Any maintenance rule at all

The case split the rule invariant delivers, on the maintenance side: `maintenanceRules` is
`pathCompressRule` and, per source constructor, one e-class rule and one column rule per
column. -/

/-- The `i`th column variable of a `k`-ary rebuild rule's key. -/
theorem getElem?_rebuildVars {k i : Nat} (hi : i < k) :
    (rebuildVars k)[i]? = some (Expr.var ("@c" ++ toString i)) := by
  simp [rebuildVars, hi]

/-- **Every maintenance rule's firing preserves the invariant.** Nothing beyond the state is
asked: the two atoms the query matched are entry terms the state holds, and the invariant
justifies them. -/
theorem maintenance_soundTerms {P : Program} {src : Database} {d d' : FDatabase} {r : Rule}
    {σ : Env} (hmem : r ∈ maintenanceRules P)
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed) (h : d.SoundTerms src)
    (hσ : σ ∈ matchQuery d r.query) (hf : execLocalActions d r.actions σ = some d') :
    d'.SoundTerms src := by
  rw [maintenanceRules, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact pathCompressRule_soundTerms hr hidx hsc h hσ hf
  · obtain ⟨fk, -, hmem⟩ := List.mem_flatMap.mp hmem
    rw [rebuildRules] at hmem
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hmem
    rcases hmem with rfl | ⟨i, hi, rfl⟩
    · exact eclassRule_soundTerms hr hidx hsc h hσ hf
    · exact columnRule_soundTerms (getElem?_rebuildVars hi) hr hidx hsc h hσ hf

/-! #### The fold over rule firings

`execRunRules` is a fold of `fireRule` over the ruleset's rules and `fireRule` a fold of
`fireInto` over the matches, all read off the **pre**-state — so what a round owes the
invariant is one obligation per firing *at that one state*, which is what
`FDatabase.FiringsSound` names. Soundness is indifferent to under-firing, so no fixpoint enters:
a round that fires a subset of the source's firings writes a subset of justified terms. -/

/-- **What a round's firings owe the invariant.** Stated at the state the round reads its rules
and matches off, which is the only state `execRunRules` consults. -/
def FDatabase.FiringsSound (d : FDatabase) (src : Database) : Prop :=
  ∀ r ∈ d.rules, ∀ σ ∈ matchQuery d r.query, ∀ e : FDatabase,
    execLocalActions d r.actions σ = some e → e.SoundTerms src

/-- One firing, unioned into the accumulator. A stuck head contributes nothing. -/
theorem fireInto_soundTerms {src : Database} {d acc : FDatabase} {r : Rule} {σ : Env}
    (hr : r ∈ d.rules) (hσ : σ ∈ matchQuery d r.query) (hfire : d.FiringsSound src)
    (ha : acc.SoundTerms src) : (fireInto d r acc σ).SoundTerms src := by
  rw [fireInto]
  cases hx : execLocalActions d r.actions σ with
  | none => exact ha
  | some e => exact ha.union (hfire r hr σ hσ e hx)

/-- Every match of one rule. -/
theorem foldl_fireInto_soundTerms {src : Database} {d : FDatabase} {r : Rule}
    (hr : r ∈ d.rules) (hfire : d.FiringsSound src) :
    ∀ (σs : List Env), (∀ σ ∈ σs, σ ∈ matchQuery d r.query) →
      ∀ {acc : FDatabase}, acc.SoundTerms src → (σs.foldl (fireInto d r) acc).SoundTerms src
  | [], _, _, ha => ha
  | σ :: σs, hsub, _, ha =>
      foldl_fireInto_soundTerms hr hfire σs (fun τ hτ => hsub τ (List.mem_cons_of_mem _ hτ))
        (fireInto_soundTerms hr (hsub σ List.mem_cons_self) hfire ha)

@[inherit_doc foldl_fireInto_soundTerms]
theorem fireRule_soundTerms {src : Database} {d acc : FDatabase} {r : Rule}
    (hr : r ∈ d.rules) (hfire : d.FiringsSound src) (ha : acc.SoundTerms src) :
    (fireRule d acc r).SoundTerms src :=
  foldl_fireInto_soundTerms hr hfire _ (fun _ h => h) ha

/-- The round's fold, with the accumulator generalized; the pre-state the matches are read off
is fixed. -/
theorem foldl_fireRule_soundTerms {src : Database} {d : FDatabase} (hfire : d.FiringsSound src) :
    ∀ (rs : List Rule), (∀ r ∈ rs, r ∈ d.rules) →
      ∀ {acc : FDatabase}, acc.SoundTerms src → (rs.foldl (fireRule d) acc).SoundTerms src
  | [], _, _, ha => ha
  | r :: rs, hsub, _, ha =>
      foldl_fireRule_soundTerms hfire rs (fun r' hr' => hsub r' (List.mem_cons_of_mem _ hr'))
        (fireRule_soundTerms (hsub r List.mem_cons_self) hfire ha)

/-- **One round of rule firing preserves the invariant**, given that each of its firings does.
Every rule of the ruleset is one the state holds, so `rules` covers them. -/
theorem execRunRules_soundTerms {src : Database} {R : RulesetName} {d : FDatabase}
    (hfire : d.FiringsSound src) (h : d.SoundTerms src) : (execRunRules R d).SoundTerms src :=
  foldl_fireRule_soundTerms hfire _ (fun _ hr => List.mem_of_mem_filter hr) h

/-- **And so does a whole round**, rule firing followed by the merge phase to a fixpoint. -/
theorem runRoundM_soundTerms {src : Database} {R : RulesetName} {d e : FDatabase}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hn : d.NoUnions)
    (hwl : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hfire : d.FiringsSound src) (h : d.SoundTerms src)
    (hrun : d.runRoundM R = some e) : e.SoundTerms src := by
  rw [FDatabase.runRoundM] at hrun
  refine mergeSaturateF_soundTerms mergeFuel ?_ ?_ ?_ ?_ (execRunRules_soundTerms hfire h) hrun
  · rw [FDatabase.execRunRules_fields.1]; exact hshape
  · rw [FDatabase.execRunRules_fields.1]; exact hlegal
  · exact hinv.execRunRules hwl
  · exact execRunRules_noUnions hn

/-- **The rule invariant applied to the fold.** At a state whose rules are all encoded, a
firing is either an encoded source rule's or a maintenance rule's, and the second kind is
discharged outright — so what is left of `FDatabase.FiringsSound` at an encoded target is
exactly the one hypothesis below, about a head `encodeActions` emitted.

This is the factorisation `execM_soundTerms` is reduced to: the fold, the merge phase and the
three maintenance families are proved, and the source-rule head is what is not. -/
theorem firingsSound_of_rulesEncoded {P : Program} {src : Database} {d : FDatabase}
    (hrules : d.RulesEncoded P) (hr : d.EqsRefl) (hidx : d.IndexOk) (hsc : d.SubtermClosed)
    (h : d.SoundTerms src)
    (hsrc : ∀ (s : Rule) (i n : Nat), Cmd.rule s ∈ P → (encodeRule i s n).1 ∈ d.rules →
      ∀ σ ∈ matchQuery d (encodeRule i s n).1.query, ∀ e : FDatabase,
        execLocalActions d (encodeRule i s n).1.actions σ = some e → e.SoundTerms src) :
    d.FiringsSound src := by
  intro r hrm σ hσ e he
  rcases hrules r hrm with ⟨s, i, n, hmem, rfl⟩ | hmaint
  · exact hsrc s i n hmem hrm σ hσ e he
  · exact maintenance_soundTerms hmaint hr hidx hsc h hσ he

/-! ###### The maintenance firing is real

`ENCODING.md`'s discipline, at the hypothesis that could have made all three families vacuous:
`hσ` asks the encoded query to have *matched*, and `matchQuery` is exactly what the kernel
cannot run — `closureF` is well-founded-recursive and so irreducible, the same limit every
other target-side witness here works around. So the match is **proved** rather than decided,
through `patternHolds_values_of_mem_rows`: a row of a `:merge` function makes its own atom
hold, at the values its own columns are, and the only closure facts needed are reflexive ones.

The state is `cxPre` **without its third `set`** — and that third `set` *is* this firing: the
e-class rule at the nullary `B` reads `@BView() ↦ ((B), @Fiat)` and the edge
`@UF((B)) ↦ ((A), @Fiat)`, and re-keys the entry onto `(A)` with the composed proof. So the
merge-phase witness `cxPre` above is the state this firing produced. -/

/-- **A row of a `:merge` function makes its own atom hold**, at the values its columns are.
The converse of `mem_terms_of_patternHolds_values`, and what says that lemma — and the three
families over it — is not vacuous. The only closure facts it needs are reflexive, so nothing
here asks the kernel for a congruence closure. -/
theorem patternHolds_values_of_mem_rows {d : FDatabase} {vs as : List Expr} {f : FnName}
    {σ : Env} {ts us : List Term} (hmg : (d.sig.mergeOf f).isSome = true)
    (hats : Expr.evalList d.sig as (d.env ++ σ) = some ts)
    (hvus : Expr.evalList d.sig vs (d.env ++ σ) = some us)
    (hrow : (⟨f, ts, us⟩ : Row) ∈ d.rows) (hcol : ∀ c ∈ ts ++ us, c ∈ d.terms) :
    patternHolds d (.values vs f as) σ = true := by
  have hrefl : ∀ c ∈ ts ++ us, (c, c) ∈ ((d.addTerms ts).addTerms us).closureF := by
    intro c hc
    exact FDatabase.mem_closureF_iff.mpr (Cong.assert (Or.inl ⟨rfl,
      FDatabase.mem_addTerms_terms (FDatabase.mem_addTerms_terms (hcol c hc))⟩))
  have hct : ∀ (xs : List Term),
      (∀ c ∈ xs, (c, c) ∈ ((d.addTerms ts).addTerms us).closureF) →
      FDatabase.congrTuple ((d.addTerms ts).addTerms us).closureF xs xs = true := by
    intro xs hxs
    refine Bool.and_eq_true_iff.mpr ⟨by simp, List.all_eq_true.mpr (fun q hq => ?_)⟩
    obtain ⟨a, b⟩ := q
    obtain ⟨heq, hmem⟩ := mem_zip_self hq
    simp only at heq hmem
    subst heq
    simpa using hxs a hmem
  simp only [patternHolds, hvus, hats, hmg, if_true, List.any_eq_true]
  refine ⟨⟨f, ts, us⟩, hrow, Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨by simp, ?_⟩, ?_⟩⟩
  · exact hct ts (fun c hc => hrefl c (List.mem_append_left _ hc))
  · exact hct us (fun c hc => hrefl c (List.mem_append_right _ hc))

/-- The state `cxPre`'s first two `set`s leave: `(B)`'s view entry and the `union`'s edge. -/
def cxRb : FDatabase :=
  (cxBase.addRow (viewName "B") [] [cxB, cxFiat]).addRow ufName [cxB] [cxA, cxFiat]

/-- `rebuildRules "B" 0`'s e-class rule, query and head. -/
def cxRbQuery : Query :=
  [Pattern.values [.var "@e", .var "@p"] (viewName "B") [],
   Pattern.values [.var "@x", .var "@q"] ufName [.var "@e"]]

@[inherit_doc cxRbQuery]
def cxRbActions : List Action :=
  [Action.set (viewName "B") [] [.var "@x", transE (.var "@p") (.var "@q")]]

/-- The match, in the order `Query.freeVars` produces it. -/
def cxRbSubst : Env := [("@p", cxFiat), ("@x", cxA), ("@q", cxFiat), ("@e", cxB)]

set_option maxRecDepth 100000 in
/-- **The two atoms match.** Proved, not decided: `matchQuery` computes a closure. -/
theorem cxRb_mem_matchQuery : cxRbSubst ∈ matchQuery cxRb cxRbQuery := by
  rw [matchQuery, List.mem_filter]
  refine ⟨mem_assignments.mpr ⟨by decide, by decide⟩, List.all_eq_true.mpr ?_⟩
  intro p hp
  have hp2 : p = Pattern.values [.var "@e", .var "@p"] (viewName "B") [] ∨
      p = Pattern.values [.var "@x", .var "@q"] ufName [.var "@e"] := by
    simpa [cxRbQuery] using hp
  rcases hp2 with rfl | rfl
  · exact patternHolds_values_of_mem_rows (ts := []) (us := [cxB, cxFiat])
      (by decide) rfl rfl (by decide) (by decide)
  · exact patternHolds_values_of_mem_rows (ts := [cxB]) (us := [cxA, cxFiat])
      (by decide) rfl rfl (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- **And the head writes**, an entry the state did not hold — which is `cxPre`'s third
`set`. -/
theorem cxRb_eclassRule_writes :
    (execLocalActions cxRb cxRbActions cxRbSubst).isSome = true ∧
      ((execLocalActions cxRb cxRbActions cxRbSubst).getD FDatabase.empty).terms.contains
        (Term.app (viewName "B") ([] ++ [cxA, cxTransFiat])) = true ∧
      cxRb.terms.contains (Term.app (viewName "B") ([] ++ [cxA, cxTransFiat])) = false := by
  decide

set_option maxRecDepth 100000 in
/-- The two decidable state facts the family asks for. -/
theorem cxRb_eqsRefl : cxRb.EqsRefl := (FDatabase.eqsReflB_iff cxRb).mp (by decide)

set_option maxRecDepth 100000 in
@[inherit_doc cxRb_eqsRefl]
theorem cxRb_subtermClosed : cxRb.SubtermClosed :=
  (FDatabase.subtermClosedB_iff cxRb).mp (by decide)

/-- The prelude's state satisfies the interpreter's invariant: it holds no term, no row and no
equation, and a declaration is all that separates it from `FDatabase.empty`. -/
theorem cxBase_inv : cxBase.Inv where
  wf := FDatabase.empty_wf.congr rfl rfl
  eqs := by intro p hp; exact absurd hp (by simp [cxBase, FDatabase.empty])
  index := ⟨by intro r hr; exact absurd hr (by simp [cxBase, FDatabase.empty]),
    by intro r hr; exact absurd hr (by simp [cxBase, FDatabase.empty]),
    by intro r hr; exact absurd hr (by simp [cxBase, FDatabase.empty])⟩

/-- And so does the state two `set`s leave, which is `FDatabase.IndexOk` where the family
reads its rows. -/
theorem cxRb_inv : cxRb.Inv :=
  ((cxBase_inv.addRow (f := viewName "B") (as := []) (vs := [cxB, cxFiat])
      (by decide) (by decide)).addRow (f := ufName) (as := [cxB]) (vs := [cxA, cxFiat])
    (by decide) (by decide))

/-- The source the firing is justified against: it holds `(B)` and asserts `(B) = (A)`, which
is the source `union` `cxPre`'s second `set` encoded. -/
def cxRbSrc : Database := Database.empty.addEq cxB cxA

/-- The equation, which is what the edge the second atom matched owes. -/
theorem cxRbSrc_cong : Cong cxRbSrc cxB cxA :=
  Cong.assert (by rw [cxRbSrc, Database.addEq_eqs]; exact Set.mem_insert _ _)

theorem cxRbSrc_mem_B : cxB ∈ cxRbSrc.terms := cxRbSrc_cong.mem_left

/-- And the view entry, which is what the first atom owes. -/
theorem cxRbSrc_entrySound : EntrySound cxRbSrc "B" [] cxB :=
  ⟨[], cxRbSrc_mem_B, CongList.refl (fun a ha => absurd ha (by simp)), cxRbSrc_mem_B⟩

set_option maxRecDepth 100000 in
/-- The five terms two `set`s recorded. -/
private theorem cxRb_mem_cases : ∀ t ∈ cxRb.terms,
    t = Term.app ufName [cxB, cxA, cxFiat] ∨ t = cxFiat ∨ t = cxA ∨ t = cxB ∨
      t = Term.app (viewName "B") [cxB, cxFiat] := by decide

/-- **The invariant holds at `cxRb`, against that source.** The two clauses are asked at the
one view entry and the one `@UF` edge two `set`s wrote, so neither is carried by its vacuous
case. -/
theorem cxRb_soundTerms : cxRb.SoundTerms cxRbSrc := by
  refine ⟨fun f cs e pf hm => ?_, fun t p pf hm => ?_⟩
  · rcases cxRb_mem_cases _ hm with h | h | h | h | h
    · exact absurd (Term.app.inj h).1 viewName_ne_ufName
    · exact absurd (Term.app.inj h).2 (by simp)
    · exact absurd (Term.app.inj h).2 (by simp)
    · exact absurd (Term.app.inj h).2 (by simp)
    · obtain ⟨hfname, hcols⟩ := Term.app.inj h
      obtain rfl : f = "B" := viewName_inj hfname
      obtain ⟨rfl, hlast⟩ :=
        List.append_inj' (show cs ++ [e, pf] = [] ++ [cxB, cxFiat] from hcols) rfl
      obtain rfl : e = cxB := (List.cons.inj hlast).1
      exact cxRbSrc_entrySound
  · rcases cxRb_mem_cases _ hm with h | h | h | h | h
    · obtain ⟨-, hcols⟩ := Term.app.inj h
      have h3 : [t, p, pf] = [cxB, cxA, cxFiat] := hcols
      obtain rfl : t = cxB := (List.cons.inj h3).1
      obtain rfl : p = cxA := (List.cons.inj (List.cons.inj h3).2).1
      exact cxRbSrc_cong
    · exact absurd (Term.app.inj h).2 (by simp)
    · exact absurd (Term.app.inj h).2 (by simp)
    · exact absurd (Term.app.inj h).2 (by simp)
    · exact absurd (Term.app.inj h).1.symm viewName_ne_ufName

/-- **Every hypothesis of `eclassRule_soundTerms` holds together**, at a firing that writes an
entry the state did not hold, over a source that really derives the equation the edge
carries. -/
theorem cxRb_eclassRule_soundTerms : ∀ e : FDatabase,
    execLocalActions cxRb cxRbActions cxRbSubst = some e → e.SoundTerms cxRbSrc :=
  fun _ hf => eclassRule_soundTerms (f := "B") (cs := []) cxRb_eqsRefl cxRb_inv.index
    cxRb_subtermClosed cxRb_soundTerms cxRb_mem_matchQuery hf

/-! #### The residue itself is in `Encoding/Complete.lean`

`execM_soundTerms` consumes `entrySound_headBuild` and `cong_headUnion`, the two writers a
rule head has, and those need the query-to-substitution correspondence — which is
`Encoding/Match.lean`, downstream of this file. So the residue and the three theorems built
on it (`execM_viewsSound`, `encode_corresponds_complete`, `encode_corresponds`) are stated
there instead. Everything else the completeness half needs is above, and the witnesses that
pin the statement are below. -/

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
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> trivial
  noLitUnion := Or.inr (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

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
  · exact (exec_programStep witnessProgram_encodeDomain.ctorsOnly
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
  · exact (exec_programStep witnessProgram_encodeDomain.ctorsOnly
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · exact FDatabase.mem_closureF_iff.mpr hmem

/-! ### The two refutations the domain's last two clauses answer

`Program.EncodeDomain` gained `noLitUnion` and `headsDeclared` because the completeness
half is **false** without them, and these are the two programs. Both are one defect:
`RuleResults` asks `evalLocalActions` for a `some`, so a source rule head that gets *stuck*
drops the firing silently, while the encoded head — which `encodeAction` emits as `.set`s —
writes anyway. A stuck **top-level** action costs nothing, because it drops `ProgramStep` and
makes the claim vacuous; a stuck rule head leaves the source running and the target one entry
ahead.

Same discipline as the witnesses above: every hypothesis is a *decidable* fact about one
concrete program's two runs, and `difftest correspond-selftest` evaluates them. -/

/-- A rule head that unions two **literals**. `evalAction` refuses it — egglog's type checker
rejects `union` on a non-eq-sort and this untyped model cannot see it until the operands are
values — so the source rule never fires and the source asserts nothing. `encodeAction` emits
`.set @UF [ordering-max 1 2] [ordering-min 1 2, @Rule_0 …]`, which `execAction` does not
refuse, and the `@UF` edge between the two literals is then what a rebuild **column** rule
re-keys `@FView(2)` along — putting `(F 1)` and `(F 2)` in one e-class. -/
def luProgram : Program :=
  [.decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.lit (.int 1)])),
   .action (.expr (.app "F" [.lit (.int 2)])),
   .rule { query := [.expr (.app "F" [.lit (.int 1)])],
           actions := [.union (.lit (.int 1)) (.lit (.int 2))], ruleset := "r" },
   .run "r"]

/-- `(F 1)`, a source e-node. -/
def luF1 : Term := .app "F" [.lit (.int 1)]

/-- `(F 2)`, the other, which the source never equates to `luF1`. -/
def luF2 : Term := .app "F" [.lit (.int 2)]

theorem luProgram_ctorDecls : luProgram.CtorDecls := by
  intro c hc
  simp only [luProgram, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]

/-- **`noLitUnion` is the clause it fails**, and it fails both ways round: the program has a
`union` and it builds literals. -/
theorem luProgram_not_noLitUnion :
    ¬ ((∀ c ∈ luProgram, c.ruleUnionFreeB = true) ∨ ∀ c ∈ luProgram, c.litFreeB = true) := by
  decide

theorem luProgram_not_encodeDomain : ¬ luProgram.EncodeDomain :=
  fun h => luProgram_not_noLitUnion h.noLitUnion

/-- **And every other clause holds of it**, which is what makes it a program the encoder
claimed before `noLitUnion` was folded in — the same standing `litProgram` had before
`queryEncodable` was. -/
theorem luProgram_encodeDomain_but_noLitUnion :
    luProgram.CtorDecls ∧ Program.SetLegal luProgram (fun _ => none) ∧
      (∀ fk ∈ luProgram.ctors, Prim.ofName fk.1 = none) ∧
      (∀ n ∈ luProgram.names, ¬ "@".isPrefixOf n) ∧
      (∀ c ∈ luProgram, c.QueryEncodable) ∧
      Program.HeadsDeclared luProgram (fun _ => none) ∧ luProgram.arityConflicts = [] ∧
      luProgram.HeadsScoped := by
  refine ⟨?_, by decide, by decide, by decide +kernel, ?_, by decide, by decide, by decide⟩
  · intro c hc
    simp only [luProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  · intro c hc
    simp only [luProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.QueryEncodable, Pattern.Grounded, Pattern.NoValues, Query.VarsKeyed,
        Query.vars, Pattern.vars, Expr.vars]

/-- **The encoding equates two source e-nodes the source does not, so
`encode_corresponds_complete` is false without `noLitUnion`.**

Not the residue and not a membership side condition: `luF1` and `luF2` are both source
e-nodes — the two hypotheses `encode_corresponds_complete` carries are *satisfied* — the
target puts them in one class, and the source derives no equation between them. The pair
`encode_corresponds_invents_enode` refutes the unrestricted `iff` at is a term the source does
not hold; this one is inside the restriction. -/
theorem encode_corresponds_unions_literals {d e : FDatabase}
    (hd : exec luProgram = some d) (he : execM (encode luProgram) = some e)
    (hsc : e.SubtermClosed) (hr : e.EqsRefl) (hm₁ : luF1 ∈ d.terms) (hm₂ : luF2 ∈ d.terms)
    (hyes : sameClassF e luF1 luF2 = true) (hno : (luF1, luF2) ∉ d.closureF) :
    ∃ src, ProgramStep Database.empty luProgram src ∧
      execM (encode luProgram) = some e ∧
      luF1 ∈ src.terms ∧ luF2 ∈ src.terms ∧
      SameClass e.toDatabase luF1 luF2 ∧ ¬ Cong src luF1 luF2 := by
  refine ⟨d.toDatabase, ?_, he, ?_, ?_, (sameClassF_iff hsc hr _ _).mp hyes, ?_⟩
  · exact (exec_programStep luProgram_ctorDecls
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · rw [FDatabase.toDatabase_terms]; exact hm₁
  · rw [FDatabase.toDatabase_terms]; exact hm₂
  · exact fun h => hno (FDatabase.mem_closureF_iff.mpr h)

/-- A rule head applying a constructor the program never **declares**. `Expr.eval` needs
`Signature.IsCtor`, so the source head is stuck and the source holds no `Z`-application at
all; `encodePrelude` emits `.decl f (skolemDecl k)` for every `fk ∈ Program.ctors`, which is
read off the *uses*, so the encoded head builds `(Z (A))` and writes the view entry for it. -/
def udProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "F" { arity := 1, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "A" []])),
   .rule { query := [.expr (.app "F" [.var "x"])],
           actions := [.expr (.app "Z" [.var "x"])], ruleset := "r" },
   .run "r"]

/-- `(Z (A))`, the term only the encoded head builds. -/
def udZA : Term := .app "Z" [.app "A" []]

/-- The view entry the encoded head writes for it. -/
def udEntry : Term := .app (viewName "Z") ([.app "A" []] ++ [udZA, .app fiatName []])

/-- Whether a term is *not* a `Z`-application, so that `terms.all` says the source holds
none. -/
def udNoZ (t : Term) : Bool :=
  match t with
  | .app f _ => f != "Z"
  | .lit _ => true

theorem udProgram_ctorDecls : udProgram.CtorDecls := by
  intro c hc
  simp only [udProgram, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]

/-- **`headsDeclared` is the clause it fails.** -/
theorem udProgram_not_headsDeclared :
    ¬ Program.HeadsDeclared udProgram (fun _ => none) := by decide

theorem udProgram_not_encodeDomain : ¬ udProgram.EncodeDomain :=
  fun h => udProgram_not_headsDeclared h.headsDeclared

/-- **And every other clause holds of it.** -/
theorem udProgram_encodeDomain_but_headsDeclared :
    udProgram.CtorDecls ∧ Program.SetLegal udProgram (fun _ => none) ∧
      (∀ fk ∈ udProgram.ctors, Prim.ofName fk.1 = none) ∧
      (∀ n ∈ udProgram.names, ¬ "@".isPrefixOf n) ∧
      (∀ c ∈ udProgram, c.QueryEncodable) ∧
      (∀ c ∈ udProgram, c.ruleUnionFreeB = true) ∧ udProgram.arityConflicts = [] ∧
      udProgram.HeadsScoped := by
  refine ⟨?_, by decide, by decide, by decide +kernel, ?_, by decide, by decide, by decide⟩
  · intro c hc
    simp only [udProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  · intro c hc
    simp only [udProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.QueryEncodable, Pattern.Grounded, Pattern.NoValues, Query.VarsKeyed,
        Query.vars, Pattern.vars, Expr.vars, Pattern.ArgVar, Expr.ArgVar]

/-- **`FDatabase.SoundTerms` is false at an `execM` target, so `execM_soundTerms` needs
`headsDeclared`.** The view entry the encoded head wrote claims `∃ as, (Z as)` is a
source term, and the source holds no `Z`-application whatever.

Weaker than the refutation above — it does not reach `SameClass`, since `(Z (A))` is not a
source e-node and the sweep never puts it on a pair — and that is why it refutes the residue
rather than the conclusion. -/
theorem execM_soundTerms_false {d e : FDatabase}
    (hd : exec udProgram = some d) (he : execM (encode udProgram) = some e)
    (hmem : udEntry ∈ e.terms) (hno : d.terms.all udNoZ = true) :
    ∃ src, ProgramStep Database.empty udProgram src ∧
      execM (encode udProgram) = some e ∧ ¬ e.SoundTerms src := by
  refine ⟨d.toDatabase, (exec_programStep udProgram_ctorDecls
    (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl), he, ?_⟩
  intro hs
  obtain ⟨as, ham, -, -⟩ := hs.1 "Z" [.app "A" []] udZA (.app fiatName []) hmem
  rw [FDatabase.toDatabase_terms] at ham
  have hz := List.all_eq_true.mp hno _ ham
  simp [udNoZ] at hz

/-! ## The clause is needed, and this is what it costs

**A third shape of stuck head, and the one `EncodeDomain.headsScoped` excludes.**
`Encoding/Encode.lean` names two others — a `union` on a literal, and an application of an
undeclared name — and it long said a head variable neither the query nor a global binds is not
a third because it "sticks the encoded head too". That is true wherever the encoded head
**reads** the variable, and `encodeBuild` reads a source variable at every position but one:
`.expr (.var v)` is a build of a *leaf*, and `encodeBuild` emits **no action at all** for a
leaf. So the source block stops at the unbound variable and contributes nothing, while the
encoded block skips that action and runs the rest of the head.

`bareProgram` is that, with a `union` after the bare build: the source rule never fires, so
its two operands stay in different classes, and the encoded rule fires and writes the `@UF`
edge between them. That is an equality the target has and the source has not, **at a pair of
source e-nodes** — so it refutes `encode_corresponds_complete` itself and not only the
invariant behind it, exactly as `encode_corresponds_unions_literals` does for `noLitUnion`.
Every *other* clause of the domain holds of it (`bareProgram_encodeDomain_but_headsScoped`),
which is what makes `headsScoped` load-bearing for the conclusion rather than for the proof.
egglog rejects the program outright — an action's unbound variable is `TypeError::Unbound` in
`to_core_actions` (`egglog/src/core.rs:663-670`) — so the clause is faithfulness and not a
narrowing.

Everything below is compiled and `sorry`-free; the run itself is a hypothesis, for the reason
every other target-side witness here takes one. -/

/-- A rule head that reads an unbound variable **before** asserting an equation. Every clause
of `Program.EncodeDomain` but `headsScoped` holds of it. -/
def bareRule : Rule where
  query := [.expr (.app "G" [])]
  actions := [.expr (.var "z"), .union (.app "A" []) (.app "B" [])]
  ruleset := "r"

@[inherit_doc bareRule]
def bareProgram : Program :=
  [.decl "A" { arity := 0, outArity := 1, merge := none },
   .decl "B" { arity := 0, outArity := 1, merge := none },
   .decl "G" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.app "A" [])),
   .action (.expr (.app "B" [])),
   .action (.expr (.app "G" [])),
   .rule bareRule,
   .run "r"]

/-- The two source e-nodes the encoded run puts in one class. -/
def bareA : Term := .app "A" []

@[inherit_doc bareA]
def bareB : Term := .app "B" []

theorem bareProgram_ctorDecls : bareProgram.CtorDecls := by
  intro c hc
  simp only [bareProgram, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl]

private theorem bareRule_queryEncodable : (Cmd.rule bareRule).QueryEncodable := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain rfl : p = Pattern.expr (.app "G" []) := by simpa [bareRule] using hp
    exact ⟨by intro l; simp, trivial⟩
  · intro v hv
    exact absurd hv (by simp [bareRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList])

/-- **`EncodeDomain.headsScoped` is the clause it fails**, at `z` — the head's first action
builds the bare variable, and the query binds only `G`'s nothing. -/
theorem bareProgram_not_headsScoped : ¬ bareProgram.HeadsScoped := by
  intro h
  have hr : Cmd.rule bareRule ∈ bareProgram := by simp [bareProgram]
  have hz := (h _ hr : Actions.Scoped bareRule.actions _).1.2 "z" (by simp)
  exact absurd hz (by simp [bareRule, Query.vars, Pattern.vars, Expr.vars])

theorem bareProgram_not_encodeDomain : ¬ bareProgram.EncodeDomain :=
  fun h => bareProgram_not_headsScoped h.headsScoped

/-- **And every other clause holds of it**, which is what says `headsScoped` is not
decoration: it is the only thing standing between the domain and the refutation below, as
`noLitUnion` is at `luProgram` and `headsDeclared` at `udProgram`. -/
theorem bareProgram_encodeDomain_but_headsScoped :
    bareProgram.CtorDecls ∧ Program.SetLegal bareProgram (fun _ => none) ∧
      (∀ fk ∈ bareProgram.ctors, Prim.ofName fk.1 = none) ∧
      (∀ n ∈ bareProgram.names, ¬ "@".isPrefixOf n) ∧
      (∀ c ∈ bareProgram, c.QueryEncodable) ∧
      (∀ c ∈ bareProgram, c.litFreeB = true) ∧
      Program.HeadsDeclared bareProgram (fun _ => none) ∧
      bareProgram.arityConflicts = [] := by
  refine ⟨bareProgram_ctorDecls, by decide, by decide, by decide +kernel, ?_, by decide,
    by decide, by decide⟩
  intro c hc
  simp only [bareProgram, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact bareRule_queryEncodable
  · trivial
  · exact absurd h (by simp)

/-- **The completeness half is false without `headsScoped`.** `A` and `B` are both source
e-nodes, the source relates them in no way — its rule is stuck at `z` before it reaches the
`union` — and the encoded run puts them in one class. Every other clause of the domain holds
(`bareProgram_encodeDomain_but_headsScoped`), so this is the clause's necessity and not a
statement about a program the encoder was excused from.

Compiled, and with no `sorry` anywhere under it. The four hypotheses are decidable facts about
the two runs, checked by `difftest encode-selftest`; `sameClassF_iff`'s two side conditions
are the first two. -/
theorem bare_build_invents_equality {d e : FDatabase}
    (hd : exec bareProgram = some d) (he : execM (encode bareProgram) = some e)
    (hsc : e.SubtermClosed) (hr : e.EqsRefl) (hm₁ : bareA ∈ d.terms) (hm₂ : bareB ∈ d.terms)
    (hyes : sameClassF e bareA bareB = true) (hno : (bareA, bareB) ∉ d.closureF) :
    ∃ src, ProgramStep Database.empty bareProgram src ∧
      execM (encode bareProgram) = some e ∧
      bareA ∈ src.terms ∧ bareB ∈ src.terms ∧
      SameClass e.toDatabase bareA bareB ∧ ¬ Cong src bareA bareB := by
  refine ⟨d.toDatabase, ?_, he, ?_, ?_,
    (sameClassF_iff hsc hr _ _).mp hyes, ?_⟩
  · exact (exec_programStep bareProgram_ctorDecls
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · rw [FDatabase.toDatabase_terms]; exact hm₁
  · rw [FDatabase.toDatabase_terms]; exact hm₂
  · exact fun h => hno (FDatabase.mem_closureF_iff.mpr h)


end Egglog
