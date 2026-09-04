import EgglogSemantics.Encoding.Match

/-!
# The completeness half, assembled

`Encoding/Correspond.lean` proves the forward half outright from properties of the two states
and reduces the completeness half to one invariant of the state `execM` returned —
`FDatabase.SoundTerms`, the term-list form of `Database.ViewsSound` and
`Database.EdgesSound`. Everything the invariant's *writers* owe is discharged there — the
whole merge phase included (`mergeSaturateF_soundTerms`) — except the two a rule head has:
`entrySound_headBuild` and `cong_headUnion`, which need the query-to-substitution
correspondence and so live in `Encoding/Match.lean`.

That is the whole reason this file exists. `Encoding/Match.lean` is **downstream** of
`Encoding/Correspond.lean`, so the residue that consumes its two head-writer lemmas cannot be
stated where the rest of the completeness half is; the four theorems below are the ones that
have to be after it, and nothing else moved. The witnesses and refutations that pin the
statement — `encode_corresponds_witness`, `encode_corresponds_invents_enode`,
`encode_corresponds_unions_literals` and `execM_soundTerms_false` — depend on none of them and
stay in `Encoding/Correspond.lean`, which is what keeps `DiffTest.lean`'s imports unchanged.
-/

namespace Egglog


/-! ## The firing fold, restricted to the ruleset a round fires

`FDatabase.FiringsSound` quantifies over **every** rule the state holds, and a round runs
only the rules of one ruleset (`execRunRules` filters). At an encoded target that gap is the
whole of the `Cmd.saturate rebuildRuleset` case: an encoded source rule keeps its own ruleset
(`encodeRule`) and `Program.EncodeDomain.noAt` keeps a source ruleset out of the generated
namespace, so no encoded source rule is ever *run* by a rebuild — while `FiringsSound` would
still ask what one would write. The restriction is what lets those rounds be discharged by
`maintenance_soundTerms` alone. -/

/-- `FDatabase.FiringsSound` at the rules a round of `R` actually fires. -/
def FDatabase.FiringsSoundIn (d : FDatabase) (R : RulesetName) (src : Database) : Prop :=
  ∀ r ∈ d.rules, r.ruleset = R → ∀ σ ∈ matchQuery d r.query, ∀ e : FDatabase,
    execLocalActions d r.actions σ = some e → e.SoundTerms src

theorem FDatabase.FiringsSound.toIn {d : FDatabase} {src : Database} (h : d.FiringsSound src)
    (R : RulesetName) : d.FiringsSoundIn R src := fun r hr _ => h r hr

/-- Every match of one rule, with the rule's own obligation taken directly. -/
theorem foldl_fireInto_soundTerms_of {src : Database} {d : FDatabase} {r : Rule}
    (hfire : ∀ σ ∈ matchQuery d r.query, ∀ e : FDatabase,
      execLocalActions d r.actions σ = some e → e.SoundTerms src) :
    ∀ (σs : List Env), (∀ σ ∈ σs, σ ∈ matchQuery d r.query) →
      ∀ {acc : FDatabase}, acc.SoundTerms src → (σs.foldl (fireInto d r) acc).SoundTerms src
  | [], _, _, ha => ha
  | σ :: σs, hsub, _, ha =>
      foldl_fireInto_soundTerms_of hfire σs (fun τ hτ => hsub τ (List.mem_cons_of_mem _ hτ))
        (by
          rw [fireInto]
          cases hx : execLocalActions d r.actions σ with
          | none => exact ha
          | some e => exact ha.union (hfire σ (hsub σ List.mem_cons_self) e hx))

@[inherit_doc foldl_fireInto_soundTerms_of]
theorem fireRule_soundTerms_of {src : Database} {d acc : FDatabase} {r : Rule}
    (hfire : ∀ σ ∈ matchQuery d r.query, ∀ e : FDatabase,
      execLocalActions d r.actions σ = some e → e.SoundTerms src)
    (ha : acc.SoundTerms src) : (fireRule d acc r).SoundTerms src :=
  foldl_fireInto_soundTerms_of hfire _ (fun _ h => h) ha

/-- The round's fold, with the rule list restricted to the ruleset. -/
theorem foldl_fireRule_soundTerms_in {src : Database} {R : RulesetName} {d : FDatabase}
    (hfire : d.FiringsSoundIn R src) :
    ∀ (rs : List Rule), (∀ r ∈ rs, r ∈ d.rules ∧ r.ruleset = R) →
      ∀ {acc : FDatabase}, acc.SoundTerms src → (rs.foldl (fireRule d) acc).SoundTerms src
  | [], _, _, ha => ha
  | r :: rs, hsub, _, ha =>
      foldl_fireRule_soundTerms_in hfire rs
        (fun r' hr' => hsub r' (List.mem_cons_of_mem _ hr'))
        (fireRule_soundTerms_of
          (hfire r (hsub r List.mem_cons_self).1 (hsub r List.mem_cons_self).2) ha)

/-- **One round of rule firing preserves the invariant**, given that each firing *of the
ruleset* does. `execRunRules_soundTerms`, with the rules it does not run left alone. -/
theorem execRunRules_soundTerms_in {src : Database} {R : RulesetName} {d : FDatabase}
    (hfire : d.FiringsSoundIn R src) (h : d.SoundTerms src) :
    (execRunRules R d).SoundTerms src :=
  foldl_fireRule_soundTerms_in hfire _
    (fun _ hr => ⟨List.mem_of_mem_filter hr, by
      have := List.of_mem_filter hr
      simpa using this⟩) h

/-- **And a whole round**, rule firing followed by the merge phase. -/
theorem runRoundM_soundTerms_in {src : Database} {R : RulesetName} {d e : FDatabase}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hn : d.NoUnions)
    (hwl : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hfire : d.FiringsSoundIn R src) (h : d.SoundTerms src)
    (hrun : d.runRoundM R = some e) : e.SoundTerms src := by
  rw [FDatabase.runRoundM] at hrun
  refine mergeSaturateF_soundTerms mergeFuel ?_ ?_ ?_ ?_ (execRunRules_soundTerms_in hfire h) hrun
  · rw [FDatabase.execRunRules_fields.1]; exact hshape
  · rw [FDatabase.execRunRules_fields.1]; exact hlegal
  · exact hinv.execRunRules hwl
  · exact execRunRules_noUnions hn

/-- **A property closed under one round is closed under a saturating run.** `runSaturateM`
returns either the state it started at or one a round produced, so nothing beyond closure
under `FDatabase.runRoundM` is needed — and in particular no fixpoint. -/
theorem runSaturateM_closed {R : RulesetName} {Φ : FDatabase → Prop}
    (hstep : ∀ {d e : FDatabase}, Φ d → d.runRoundM R = some e → Φ e) :
    ∀ (n : Nat) {d e : FDatabase}, Φ d → d.runSaturateM R n = some e → Φ e
  | 0, _, _, hd, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨x, -, hx⟩ := Option.bind_eq_some_iff.mp h
      split at hx
      · rw [Option.some.injEq] at hx; exact hx ▸ hd
      · exact absurd hx (by simp)
  | n + 1, _, _, hd, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨x, hx, hrest⟩ := Option.bind_eq_some_iff.mp h
      split at hrest
      · rw [Option.some.injEq] at hrest; exact hrest ▸ hd
      · exact runSaturateM_closed hstep n (hstep hd hx) hrest


/-! ## The match, read back at a diagonal target

`validQuerySubst_of_mem_matchQuery` needs `Signature.AllConstructors`, which is exactly what
an encoded target does not have: `@UF` and every `@fView` carry a `:merge`. The clause that
needs it is `patternHolds`' **read** branch, and at a target whose `Cong` is the identity
that branch is `mem_terms_of_patternHolds_values` — a matched row is an entry term. So the
same repackaging goes through with `FDatabase.EqsRefl` and `FDatabase.IndexOk` in place of
the signature condition, which is what the encoded target has. -/

/-- `withOperands` records the operand, so it is congruent to itself there whether or not
the state held it. -/
theorem congOn_self {db : Database} (t : Term) : CongOn db [t] t t :=
  Cong.assert (by
    simp only [Database.withOperands, Database.addTerms, List.foldl_cons,
      List.foldl_nil, Database.addTerm, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inr ⟨t, Term.self_mem_subterms t, rfl⟩)

/-- **`patternHolds` is `Matches`, at a diagonal state whose index is faithful.**
`patternHolds_iff` with `Signature.AllConstructors` traded for the two invariants an encoded
target has; only the read branch differs, and there it is `mem_terms_of_patternHolds_values`. -/
theorem matches_of_patternHolds {d : FDatabase} (he : d.EqsInTerms) (hr : d.EqsRefl)
    (hidx : d.IndexOk) {p : Pattern} {σ : Env} (h : patternHolds d p σ = true) :
    Matches d.toDatabase p σ := by
  cases p with
  | values vs f as =>
    obtain ⟨ts, us, hats, hvus, hmem⟩ := mem_terms_of_patternHolds_values hr hidx h
    exact .values (FDatabase.mem_toDatabase_terms.mpr hmem)
      (by rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig]; exact hats)
      (by rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig]; exact hvus)
      (congOn_self _)
  | expr e =>
    cases hev : e.eval d.sig (d.env ++ σ) with
    | none => rw [patternHolds, hev] at h; simp at h
    | some t =>
      simp only [patternHolds, hev, decide_eq_true_eq] at h
      obtain ⟨w, hwm, hcl⟩ := h
      exact .expr (FDatabase.mem_toDatabase_terms.mpr hwm)
        (by rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig]; exact hev)
        (congOn_singleton.mpr ((FDatabase.mem_closureF_addTerm he).mp hcl))
  | eq e₁ e₂ =>
    cases hev₁ : e₁.eval d.sig (d.env ++ σ) with
    | none => rw [patternHolds, hev₁] at h; simp at h
    | some t₁ =>
      cases hev₂ : e₂.eval d.sig (d.env ++ σ) with
      | none => rw [patternHolds, hev₁, hev₂] at h; simp at h
      | some t₂ =>
        simp only [patternHolds, hev₁, hev₂, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨heq, w, hwm, hcl⟩ := h
        exact .eq (FDatabase.mem_toDatabase_terms.mpr hwm)
          (by rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig]; exact hev₁)
          (by rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig]; exact hev₂)
          (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp hcl))
          (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp heq))

/-- **A substitution the enumerator produced is one the specification admits**, at a
diagonal target with a faithful index. `validQuerySubst_of_mem_matchQuery` with its
signature hypothesis replaced; the repackaging from one restricted substitution to the
specification's `Env.UnionAll` of per-pattern ones is the same. -/
theorem validQuerySubst_of_mem_matchQuery_diag {d : FDatabase} (he : d.EqsInTerms)
    (hr : d.EqsRefl) (hidx : d.IndexOk) {q : Query} {σ : Env} (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at h
  obtain ⟨⟨hdom, hval⟩, hall⟩ := h
  obtain ⟨τ, hu, hrf⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars d.env) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self (fun p hp =>
    ⟨validEnv_canon hp hdom hval, matches_of_patternHolds he hr hidx (hall p hp)⟩), hu⟩,
    Env.agree_of_refines hrf ?_⟩
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars d.env) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp


/-! ## What the induction carries at a target state

`FDatabase.SoundTerms` is not a property a single command can be checked against: the head
of an encoded source rule reads its rows at the **contemporaneous** source state and writes a
term the source's *post*-state holds (`entrySound_headBuild_post`), and the merge phase and
the firing fold each want the interpreter's own structural invariants at the state they run
in. So the induction carries two things at once — a structural bundle about the target alone,
and the two source-relative clauses — and lifts to the run's final source only at the end,
by `FDatabase.SoundTerms.mono_src`.

`sg` is the signature the prelude installs. It is a **parameter** and not a field because
`encodeCmds` emits no declaration (`noDecl_encodeCmds`), so the signature is fixed for the
whole of the aligned run — which is what lets the two legality conditions
(`Signature.MergesLegal`, `Actions.WriteLegal` at each head) be stated once. -/

/-- The structural half: everything `runRoundM_soundTerms`, `mergeSaturateF_soundTerms` and
`firingsSound_of_rulesEncoded` ask of the state they run at, and nothing about the source. -/
structure FDatabase.EncBase (d : FDatabase) (P : Program) (sg : Signature) : Prop where
  /-- The prelude's signature, unmoved. -/
  sig : d.sig = sg
  /-- Every rule the state holds is an encoded source rule or a maintenance rule. -/
  rules : d.RulesEncoded P
  /-- Only `@UF` and the views carry a `:merge`, and both carry `mergeBody`. -/
  shape : Signature.MergeShape sg
  /-- Those bodies are legal writes at their declared widths. -/
  merges : Signature.MergesLegal sg
  /-- The interpreter's refinement invariant. -/
  inv : d.Inv
  /-- Nothing is asserted, so `Cong` is the identity. -/
  nounions : d.NoUnions
  /-- Every rule head writes legally. -/
  wl : ∀ r ∈ d.rules, Actions.WriteLegal r.actions sg

namespace FDatabase.EncBase

variable {d : FDatabase} {P : Program} {sg : Signature}

theorem eqsRefl (h : d.EncBase P sg) : d.EqsRefl := h.nounions.eqsRefl

theorem subtermClosed (h : d.EncBase P sg) : d.SubtermClosed :=
  FDatabase.SubtermClosed.of_wf h.inv.wf

theorem diag (h : d.EncBase P sg) : d.toDatabase.Diag := h.eqsRefl.toDatabase

theorem subterms (h : d.EncBase P sg) : ∀ t ∈ d.toDatabase.terms, t.subterms ⊆ d.toDatabase.terms :=
  h.inv.wf.subtermClosed

theorem wl' (h : d.EncBase P sg) : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig := by
  rw [h.sig]; exact h.wl

/-- **One command of the aligned run.** Every hypothesis but `hwl` is a fact `encodeCmd`'s
read-back already supplies at each command it emits; `hwl` is the one legality condition the
signature has to be checked for. -/
theorem execCmdM {d d' : FDatabase} {c : Cmd} (h : d.EncBase P sg)
    (hro : Cmd.RulesEncodedOk P c) (huf : c.UnionFree) (hnd : c.NoDecl)
    (hwl : c.WriteLegal sg) (hs : d.execCmdM c = some d') : d'.EncBase P sg where
  sig := (execCmdM_sig_of_noDecl hs hnd).trans h.sig
  rules := FDatabase.execCmdM_rulesEncoded hro h.rules hs
  shape := h.shape
  merges := h.merges
  inv := h.inv.execCmdM (by rw [h.sig]; exact hwl) (by rw [h.sig]; exact h.merges)
    (by cases c with | decl f dc => exact (hnd : False).elim | _ => trivial) h.wl' hs
  nounions := execCmdM_noUnions huf h.nounions hs
  wl := by
    rw [← (execCmdM_sig_of_noDecl hs hnd).trans h.sig]
    exact FDatabase.execCmdM_rulesLegal (by rw [h.sig]; exact hwl)
      (by cases c with | decl f dc => exact (hnd : False).elim | _ => trivial) h.wl' hs

/-- **A block of them.** -/
theorem execProgramM {P : Program} {sg : Signature} {p : Program}
    (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal sg) :
    ∀ {d D : FDatabase}, d.EncBase P sg → d.execProgramM p = some D → D.EncBase P sg := by
  induction p with
  | nil =>
    intro d D h hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro d D h hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (h.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) h₁) h₂

end FDatabase.EncBase

/-- The bundle together with the two source-relative clauses. `glob` is what
`entrySound_headBuild_post` reads the head's free variables through, and `sound` is the
invariant itself, at the source state the *reading* happens at. -/
structure FDatabase.EncOk (d : FDatabase) (P : Program) (sg : Signature) (sd : Database) :
    Prop where
  base : d.EncBase P sg
  glob : sd.GlobalsAgree d.env
  sound : d.SoundTerms sd
  /-- **And every encoded source rule the target holds is one the source already holds.**
  `FDatabase.EncBase.rules` says which rules a target *can* hold, over the whole of `P`;
  soundness needs the alignment, because a firing of a rule the source has not reached yet
  writes what no source state justifies. `encodeCmd` emits the encoded rule exactly where the
  source command adds the source one, so this is carried by `stepCmd`'s `.rule` case and by
  nothing else — the pair is carried rather than the rule alone, so that no injectivity of
  `encodeRule` is needed. -/
  srcRules : ∀ r ∈ d.rules,
    (∃ (s : Rule) (i n : Nat), Cmd.rule s ∈ P ∧ s ∈ sd.rules ∧ r = (encodeRule i s n).1) ∨
      r ∈ maintenanceRules P

/-- The three source clauses move along a source that grows and keeps its environment. -/
theorem FDatabase.EncOk.mono_src {d : FDatabase} {P : Program} {sg : Signature}
    {sd sd' : Database} (h : d.EncOk P sg sd) (heq : sd.eqs ⊆ sd'.eqs)
    (henv : ∀ v t, Env.lookup v sd'.env = some t → Env.lookup v sd.env = some t)
    (hrules : ∀ r ∈ sd.rules, r ∈ sd'.rules) :
    d.EncOk P sg sd' where
  base := h.base
  glob := fun v t hv => h.glob v t (henv v t hv)
  sound := h.sound.mono_src heq
  srcRules := fun r hr =>
    (h.srcRules r hr).imp (fun ⟨s, i, n, hm, hs, he⟩ => ⟨s, i, n, hm, hrules s hs, he⟩) id

/-- A substitution extends the target environment on the right, so the globals still agree. -/
theorem Database.GlobalsAgree.append {sd : Database} {ρ σ : Env} (h : sd.GlobalsAgree ρ) :
    sd.GlobalsAgree (ρ ++ σ) := by
  intro v t hv
  rw [Env.lookup_append_of_mem (Env.mem_dom_of_mem (Env.mem_of_lookup (h v t hv)))]
  exact h v t hv


/-! ## The two obligations one aligned command leaves

Everything below is proved from these two and the read-backs `encodeCmd` already has. They
are stated as named properties rather than inlined so that what is left of the residue is
one statement each, and so that the induction that consumes them is checkable on its own. -/

/-- **The head case.** One firing of an encoded source rule, at a target state the aligned
run reaches and a source command that fires the rule, writes only terms the source's
post-state justifies.

The reading is at `sd` and the conclusion at `sd'`, which is the two-state shape
`entrySound_headBuild_post` and `cong_headUnion_post` are stated in and the one
`FDatabase.SoundTerms.mono_src` cannot bridge. `hc` covers both firing commands at once: a
`Cmd.run R` reads at the command's pre-state, and a `Cmd.saturate R` reads at its
**post**-state, which is a `RunRules` fixpoint and so steps to itself. -/
def EncodedHeadSound (P : Program) (sg : Signature) : Prop :=
  ∀ {pre q : Program}, P = pre ++ q → ∀ {sd sd' : Database},
    ProgramStep Database.empty pre sd →
    ∀ {R : RulesetName} {c : Cmd}, (c = Cmd.run R ∨ c = Cmd.saturate R) → CmdStep sd c sd' →
    ∀ {d : FDatabase}, d.EncOk P sg sd →
    ∀ (s : Rule) (i n : Nat), Cmd.rule s ∈ P → s ∈ sd.rules → s.ruleset = R →
      (encodeRule i s n).1 ∈ d.rules →
    ∀ σ ∈ matchQuery d (encodeRule i s n).1.query, ∀ e : FDatabase,
      execLocalActions d (encodeRule i s n).1.actions σ = some e → e.SoundTerms sd'

/-- **The top-level action case.** The block of `Cmd.action`s `encodeAction` emits for one
source action preserves the invariant, and keeps the globals agreeing — a source `let` binds
`v` to the value of `e`, and the encoded block binds it to the value of `(encodeBuild e n).1`,
which *is* `e` (`encodeBuild_fst`). -/
def EncodedActionSound (P : Program) (sg : Signature) : Prop :=
  ∀ {pre q : Program} {a : Action}, P = pre ++ Cmd.action a :: q →
    ∀ {sd sd' : Database}, ProgramStep Database.empty pre sd → CmdStep sd (.action a) sd' →
    ∀ {n : Nat} {d D : FDatabase}, d.EncOk P sg sd →
      d.execProgramM ((encodeAction fiatE a n).1.map Cmd.action) = some D →
      D.EncBase P sg → D.EncOk P sg sd'

/-- **The one legality condition the signature has to be checked for.** Every command
`encodeCmd` emits writes legally at the prelude's signature: a `.run` and a `.saturate`
trivially, a `.rule` at its head's `set`s, a `.action` at its own. -/
def EncodedWriteLegal (P : Program) (sg : Signature) : Prop :=
  ∀ c ∈ P, ∀ (n i : Nat), ∀ c' ∈ (encodeCmd c n i).1, c'.WriteLegal sg

/-! ## The rebuild rounds fire no source rule

`encodeRule` keeps a source rule's own ruleset and `Program.EncodeDomain.noAt` keeps every
source name — ruleset names included — out of the generated namespace, so a
`Cmd.saturate rebuildRuleset` runs maintenance rules and nothing else. That is what makes
`FDatabase.FiringsSoundIn` the right hypothesis for those rounds and
`maintenance_soundTerms` the whole of their discharge. -/

/-- A source rule's ruleset is a source name, so it is not `@rebuild`. -/
theorem ruleset_ne_rebuild {P : Program} (hdom : P.EncodeDomain) {s : Rule}
    (hs : Cmd.rule s ∈ P) : s.ruleset ≠ rebuildRuleset := by
  intro hc
  refine hdom.noAt s.ruleset ?_ ?_
  · rw [Program.names]
    refine List.mem_append.mpr (Or.inr ?_)
    rw [Program.rulesets, List.mem_dedup]
    exact List.mem_flatMap.mpr ⟨Cmd.rule s, hs, by simp [Cmd.rulesets]⟩
  · -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
    rw [hc]
    exact (by decide +kernel : "@".isPrefixOf rebuildRuleset = true)

/-- **A rebuild round's firings are all maintenance firings.** -/
theorem firingsSoundIn_rebuild {P : Program} (hdom : P.EncodeDomain) {sg : Signature}
    {sd : Database} {d : FDatabase} (hok : d.EncOk P sg sd) :
    d.FiringsSoundIn rebuildRuleset sd := by
  intro r hr hrs σ hσ e he
  rcases hok.base.rules r hr with ⟨s, i, n, hmem, rfl⟩ | hmaint
  · exact absurd (hrs ▸ rfl : s.ruleset = rebuildRuleset) (ruleset_ne_rebuild hdom hmem)
  · exact maintenance_soundTerms hmaint hok.base.eqsRefl hok.base.inv.index
      hok.base.subtermClosed hok.sound hσ he


/-! ## The environment along a source run

`FDatabase.EncOk.glob` compares the two environments, so every command that is not a
top-level action has to be shown to move neither. On the source side that is `cmdReach`
followed by a merge phase, and both fix `env` (`MergeClosure.envRules`). -/

/-- Rounds of a ruleset do not move the environment. -/
theorem runStepReach_env {R : RulesetName} {sd d : Database}
    (h : Relation.ReflTransGen (RunStep R) sd d) : d.env = sd.env := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ((MergeClosure.envRules hstep).1.trans rfl).trans ih

/-- **Only a top-level action moves the source environment.** -/
theorem cmdStep_env_of_noAction {sd sd' : Database} {c : Cmd} (hc : ∀ a, c ≠ Cmd.action a)
    (h : CmdStep sd c sd') : sd'.env = sd.env := by
  obtain ⟨d, hreach, hcl⟩ := h
  refine (MergeClosure.envRules hcl).1.trans ?_
  cases c with
  | action a => exact absurd rfl (hc a)
  | saturate R => exact runStepReach_env (show SaturateReach R sd d from hreach).1
  | rule r =>
    replace hreach : cmdEffect sd (.rule r) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach; exact hreach ▸ rfl
  | run R =>
    replace hreach : cmdEffect sd (.run R) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach; exact hreach ▸ rfl
  | decl f dc =>
    replace hreach : cmdEffect sd (.decl f dc) = some d := hreach
    rw [cmdEffect, Option.some.injEq] at hreach; exact hreach ▸ rfl

/-- Rounds of a ruleset do not move the rule set either. -/
theorem runStepReach_rules {R : RulesetName} {sd d : Database}
    (h : Relation.ReflTransGen (RunStep R) sd d) : d.rules = sd.rules := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      exact ((MergeClosure.envRules hstep).2.trans
        (by rw [RunRules, Database.sUnion_rules])).trans ih

/-- **Rules only ever grow along a command**, and only `Cmd.rule` adds one. -/
theorem cmdStep_rule_mem {sd sd' : Database} {r : Rule} (h : CmdStep sd (.rule r) sd') :
    r ∈ sd'.rules := by
  obtain ⟨d, hreach, hcl⟩ := h
  replace hreach : cmdEffect sd (.rule r) = some d := hreach
  rw [cmdEffect, Option.some.injEq] at hreach
  rw [(MergeClosure.envRules hcl).2, ← hreach]
  exact Set.mem_insert _ _

@[inherit_doc cmdStep_rule_mem]
theorem cmdStep_rules_subset {sd sd' : Database} {c : Cmd} (h : CmdStep sd c sd') :
    ∀ r ∈ sd.rules, r ∈ sd'.rules := by
  obtain ⟨d, hreach, hcl⟩ := h
  have hd : sd'.rules = d.rules := (MergeClosure.envRules hcl).2
  intro r hr
  rw [hd]
  cases c with
  | action a =>
      have hv : evalAction sd a = some d := hreach
      rw [evalAction_rules hv]; exact hr
  | rule r' =>
      replace hreach : cmdEffect sd (.rule r') = some d := hreach
      rw [cmdEffect, Option.some.injEq] at hreach
      rw [← hreach]
      exact Set.mem_insert_of_mem _ hr
  | run R =>
      replace hreach : cmdEffect sd (.run R) = some d := hreach
      rw [cmdEffect, Option.some.injEq] at hreach
      rw [← hreach, RunRules, Database.sUnion_rules]
      exact hr
  | saturate R =>
      rw [runStepReach_rules (show SaturateReach R sd d from hreach).1]
      exact hr
  | decl f dc =>
      replace hreach : cmdEffect sd (.decl f dc) = some d := hreach
      rw [cmdEffect, Option.some.injEq] at hreach
      rw [← hreach]
      exact hr

/-- The bundle moves onto the command's post-state, where neither the source environment nor
the target's has moved. -/
theorem FDatabase.EncOk.step_src {P : Program} {sg : Signature} {sd sd' : Database}
    {d : FDatabase} (hok : d.EncOk P sg sd) {c : Cmd} (hc : ∀ a, c ≠ Cmd.action a)
    (hstep : CmdStep sd c sd') : d.EncOk P sg sd' :=
  hok.mono_src (CmdStep.contained hstep).eqs
    (fun v t hv => by rw [cmdStep_env_of_noAction hc hstep] at hv; exact hv)
    (cmdStep_rules_subset hstep)

/-! ## One round of the aligned run

Two shapes, and the second is what sub-part (3) needed. A round of the **source's** ruleset
justifies its writes by the source command that fires it, through the head obligation; a
round of `@rebuild` fires no source rule at all and is discharged by `maintenance_soundTerms`
alone. Neither needs a fixpoint on the target: `execM_contained` says the encoded round fires
a subset, and a subset of justified writes is justified. -/

/-- **A round of the source's own ruleset.** `hc` is the firing command; for a `Cmd.run R`
it is used at the command's pre-state and for a `Cmd.saturate R` at its post-state, which
`RunSaturated` makes a `CmdStep` to itself. -/
theorem FDatabase.EncOk.runRoundM {P : Program} {sg : Signature}
    (hhead : EncodedHeadSound P sg) {pre q : Program} (hP : P = pre ++ q)
    {sd sd' : Database} (hpre : ProgramStep Database.empty pre sd)
    {R : RulesetName} {c : Cmd} (hc : c = Cmd.run R ∨ c = Cmd.saturate R)
    (hstep : CmdStep sd c sd') {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.runRoundM R = some e) : e.EncOk P sg sd' := by
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hrun
  have hna : ∀ a, c ≠ Cmd.action a := by
    rcases hc with rfl | rfl <;> intro a h <;> exact absurd h (by simp)
  have hfire : d.FiringsSoundIn R sd' := by
    intro r hr hrs σ hσ e' he'
    rcases hok.srcRules r hr with ⟨s, i, n, hmem, hsr, rfl⟩ | hmaint
    · exact hhead hP hpre hc hstep hok s i n hmem hsr hrs hr σ hσ e' he'
    · exact maintenance_soundTerms hmaint hok.base.eqsRefl hok.base.inv.index
        hok.base.subtermClosed (hok.sound.mono_src (CmdStep.contained hstep).eqs) hσ he'
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_⟩, ?_, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · intro v t hv
    rw [henv]
    exact hok.glob v t (by rw [cmdStep_env_of_noAction hna hstep] at hv; exact hv)
  · exact runRoundM_soundTerms_in (by rw [hok.base.sig]; exact hok.base.shape)
      (by rw [hok.base.sig]; exact hok.base.merges) hok.base.inv hok.base.nounions
      hok.base.wl' hfire (hok.sound.mono_src (CmdStep.contained hstep).eqs) hrun
  · intro r hr
    exact (hok.srcRules r (hrules ▸ hr)).imp
      (fun ⟨s, i, n, hm, hs, he⟩ => ⟨s, i, n, hm, cmdStep_rules_subset hstep s hs, he⟩) id

/-- **A rebuild round.** No source rule joins `@rebuild`, so every firing is a maintenance
firing and the source state does not move. -/
theorem FDatabase.EncOk.runRoundM_rebuild {P : Program} (hdom : P.EncodeDomain)
    {sg : Signature} {sd : Database} {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.runRoundM rebuildRuleset = some e) : e.EncOk P sg sd := by
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hrun
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_⟩, ?_, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · intro v t hv; rw [henv]; exact hok.glob v t hv
  · exact runRoundM_soundTerms_in (by rw [hok.base.sig]; exact hok.base.shape)
      (by rw [hok.base.sig]; exact hok.base.merges) hok.base.inv hok.base.nounions
      hok.base.wl' (firingsSoundIn_rebuild hdom hok) hok.sound hrun
  · exact fun r hr => hok.srcRules r (hrules ▸ hr)

/-- **The rebuild after every writing command.** Any number of rounds, each of them the
lemma above. -/
theorem FDatabase.EncOk.saturate_rebuild {P : Program} (hdom : P.EncodeDomain)
    {sg : Signature} {sd : Database} {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.execCmdM (Cmd.saturate rebuildRuleset) = some e) : e.EncOk P sg sd :=
  runSaturateM_closed (Φ := fun x => x.EncOk P sg sd)
    (fun hx hr => FDatabase.EncOk.runRoundM_rebuild hdom hx hr) runFuel hok hrun

/-- **A saturating run of the source's ruleset.** The source's own post-state is a
`RunRules` fixpoint (`RunSaturated`), so it steps to itself and every round of the target's
saturation reads and concludes there — which is what a `.saturate` needs and a single round
does not give. -/
theorem FDatabase.EncOk.saturate_src {P : Program} {sg : Signature}
    (hhead : EncodedHeadSound P sg) {pre q : Program} {R : RulesetName}
    (hP : P = pre ++ Cmd.saturate R :: q) {sd sd' : Database}
    (hpre : ProgramStep Database.empty pre sd) (hstep : CmdStep sd (.saturate R) sd')
    {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.execCmdM (Cmd.saturate R) = some e) : e.EncOk P sg sd' := by
  have hsat : SaturateReach R sd sd' := cmdStep_saturate_iff.mp hstep
  have hfix : CmdStep sd' (Cmd.saturate R) sd' :=
    cmdStep_saturate_iff.mpr ⟨Relation.ReflTransGen.refl, hsat.2⟩
  have hpre' : ProgramStep Database.empty (pre ++ [Cmd.saturate R]) sd' :=
    hpre.append (ProgramStep.cons hstep ProgramStep.nil)
  have hP' : P = (pre ++ [Cmd.saturate R]) ++ q := by rw [List.append_assoc]; exact hP
  refine runSaturateM_closed (Φ := fun x => x.EncOk P sg sd')
    (fun hx hr => FDatabase.EncOk.runRoundM hhead hP' hpre' (Or.inr rfl) hfix hx hr)
    runFuel (hok.step_src (by intro a h; exact absurd h (by simp)) hstep) hrun



/-! ## One aligned command, and the induction over the run

`encodeCmds` maps one source command to a block, and `encodeCmd`'s five cases are five
shapes of block: nothing for a declaration, one `Cmd.rule` for a rule, a round or a
saturation followed by a rebuild for the two firing commands, and the action block followed
by a rebuild for a top-level action. The induction below is over that alignment, carrying
`FDatabase.EncOk` at the **contemporaneous** source state, and it lifts to the run's final
source only at the last step. -/

/-- `encodeCmd` emits no declaration, which is what fixes the signature for the whole
aligned run. -/
theorem noDecl_encodeCmd (c : Cmd) (n i : Nat) : ∀ c' ∈ (encodeCmd c n i).1, c'.NoDecl := by
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

/-- A one-command run is that command. -/
theorem execProgramM_single {d D : FDatabase} {c : Cmd}
    (h : d.execProgramM [c] = some D) : d.execCmdM c = some D := by
  rw [FDatabase.execProgramM] at h
  obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  rw [FDatabase.execProgramM, Option.some.injEq] at h₂
  exact h₂ ▸ h₁

/-- A two-command run splits. -/
theorem execProgramM_pair {d D : FDatabase} {c₁ c₂ : Cmd}
    (h : d.execProgramM [c₁, c₂] = some D) :
    ∃ d₁, d.execCmdM c₁ = some d₁ ∧ d₁.execCmdM c₂ = some D := by
  rw [FDatabase.execProgramM] at h
  obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨d₁, h₁, execProgramM_single h₂⟩

/-- **One aligned command.** The five cases of `encodeCmd`, each carrying
`FDatabase.EncOk` from the source command's pre-state to its post-state. -/
theorem FDatabase.EncOk.stepCmd {P : Program} (hdom : P.EncodeDomain) {sg : Signature}
    (hhead : EncodedHeadSound P sg) (hact : EncodedActionSound P sg)
    (hwlP : EncodedWriteLegal P sg) {pre q : Program} {c : Cmd} (hP : P = pre ++ c :: q)
    {sd sd' : Database} (hpre : ProgramStep Database.empty pre sd)
    (hstep : CmdStep sd c sd') {n i : Nat} {d D : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.execProgramM (encodeCmd c n i).1 = some D) : D.EncOk P sg sd' := by
  have hcP : c ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
  have hbase : ∀ {c' : Cmd} {x y : FDatabase}, c' ∈ (encodeCmd c n i).1 →
      Cmd.RulesEncodedOk P c' → x.EncBase P sg → x.execCmdM c' = some y → y.EncBase P sg :=
    fun hmem hro hb hs =>
      hb.execCmdM hro (encodeCmd_unionFree c n i _ hmem) (noDecl_encodeCmd c n i _ hmem)
        (hwlP c hcP n i _ hmem) hs
  cases c with
  | decl f dc =>
    have hnil : d.execProgramM ([] : Program) = some D := hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hnil
    subst hnil
    exact hok.step_src (by intro a h; exact absurd h (by simp)) hstep
  | rule r =>
    have hrun' : d.execProgramM [Cmd.rule (encodeRule i r n).1] = some D := hrun
    have hs : d.execCmdM (Cmd.rule (encodeRule i r n).1) = some D := execProgramM_single hrun'
    have hmem : Cmd.rule r ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
    have hmem' : Cmd.rule (encodeRule i r n).1 ∈ (encodeCmd (Cmd.rule r) n i).1 :=
      List.mem_cons_self
    have hb : D.EncBase P sg :=
      hbase hmem' (Or.inl ⟨r, i, n, hmem, rfl⟩) hok.base hs
    obtain rfl : D = { d with rules := (encodeRule i r n).1 :: d.rules } := by
      rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs.symm
    refine ⟨hb, ?_, hok.sound.mono_src (CmdStep.contained hstep).eqs, ?_⟩
    · intro v t hv
      rw [cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep] at hv
      exact hok.glob v t hv
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr''
      · exact Or.inl ⟨r, i, n, hmem, cmdStep_rule_mem hstep, rfl⟩
      · exact (hok.srcRules r' hr'').imp
          (fun ⟨s, j, m, hm, hs, he⟩ => ⟨s, j, m, hm, cmdStep_rules_subset hstep s hs, he⟩) id
  | run R =>
    have hrun' : d.execProgramM [Cmd.run R, Cmd.saturate rebuildRuleset] = some D := hrun
    obtain ⟨d₁, h₁, h₂⟩ := execProgramM_pair hrun'
    have hok₁ : d₁.EncOk P sg sd' :=
      hok.runRoundM hhead hP hpre (Or.inl rfl) hstep (by rw [FDatabase.execCmdM] at h₁; exact h₁)
    exact hok₁.saturate_rebuild hdom h₂
  | saturate R =>
    have hrun' : d.execProgramM [Cmd.saturate R, Cmd.saturate rebuildRuleset] = some D := hrun
    obtain ⟨d₁, h₁, h₂⟩ := execProgramM_pair hrun'
    exact (hok.saturate_src hhead hP hpre hstep h₁).saturate_rebuild hdom h₂
  | action a =>
    have hrun' : d.execProgramM ((encodeAction fiatE a n).1.map Cmd.action ++
        [Cmd.saturate rebuildRuleset]) = some D := hrun
    obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun'
    have hb₁ : D₁.EncBase P sg := by
      refine FDatabase.EncBase.execProgramM (P := P) (sg := sg) ?_ ?_ ?_ ?_ hok.base hblock
      all_goals
        intro c' hc'
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
        have hmem : Cmd.action b ∈ (encodeCmd (Cmd.action a) n i).1 :=
          List.mem_append_left _ (List.mem_map_of_mem hb)
      · trivial
      · exact encodeCmd_unionFree (Cmd.action a) n i _ hmem
      · exact noDecl_encodeCmd (Cmd.action a) n i _ hmem
      · exact hwlP (Cmd.action a) hcP n i _ hmem
    exact (hact hP hpre hstep hok hblock hb₁).saturate_rebuild hdom (execProgramM_single hafter)

/-- **The per-command induction.** `FDatabase.EncOk` at the state the target run has reached
and the source state the source run has reached, carried command by command along the
alignment `encodeCmds` sets up.

This is the shape the residue needed, and the reason it cannot be a single application of
`firingsSound_of_rulesEncoded`: the head's reading is at the contemporaneous source state
and its conclusion at that command's post-state, so the invariant reaches the run's final
source only at the end, by `FDatabase.SoundTerms.mono_src`. -/
theorem FDatabase.EncOk.stepCmds {P : Program} (hdom : P.EncodeDomain) {sg : Signature}
    (hhead : EncodedHeadSound P sg) (hact : EncodedActionSound P sg)
    (hwlP : EncodedWriteLegal P sg) :
    ∀ (p pre : Program), P = pre ++ p →
      ∀ {sd src : Database}, ProgramStep Database.empty pre sd → ProgramStep sd p src →
      ∀ (n i : Nat) {d D : FDatabase}, d.EncOk P sg sd →
        d.execProgramM (encodeCmds p n i).1 = some D → D.EncOk P sg src := by
  intro p
  induction p with
  | nil =>
    intro pre _ sd src _ hsrc n i d D hok hrun
    obtain rfl : sd = src := ProgramStep.nil_inv hsrc
    have hnil : d.execProgramM ([] : Program) = some D := hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hnil
    exact hnil ▸ hok
  | cons c cs ih =>
    intro pre hP sd src hpre hsrc n i d D hok hrun
    obtain ⟨sd', hstep, hrest⟩ := ProgramStep.cons_inv hsrc
    rw [encodeCmds_cons_fst] at hrun
    obtain ⟨d₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
    exact ih (pre ++ [c]) (by rw [List.append_assoc]; exact hP)
      (hpre.append (ProgramStep.cons hstep ProgramStep.nil)) hrest _ _
      (hok.stepCmd hdom hhead hact hwlP hP hpre hstep hblock) hafter


/-! ## The prelude, and the base case

`encodePrelude` is declarations and rules and nothing else, so the state it leaves holds no
term, no row and no equation, and its environment is still empty. That makes almost every
field of `FDatabase.EncOk` free there: `FDatabase.Inv` is vacuous at empty data,
`FDatabase.SoundTerms` is vacuous at an empty term list, and `Database.GlobalsAgree` is
vacuous at the empty source. What is *not* free is the pair of legality conditions the
signature has to be checked for, which is why they are named obligations below. -/

/-- A prelude command: a declaration or a rule, the two that write no data. -/
def Cmd.DeclOrRule : Cmd → Prop
  | .decl _ _ => True
  | .rule _ => True
  | _ => False

theorem declOrRule_encodePrelude (P : Program) : ∀ c ∈ encodePrelude P, c.DeclOrRule := by
  have hproof : ∀ (rs : List Rule) (i : Nat), ∀ c ∈ ruleProofDecls rs i, Cmd.DeclOrRule c := by
    intro rs
    induction rs with
    | nil => intro i c hc; simp [ruleProofDecls] at hc
    | cons r rs ih =>
      intro i c hc
      rw [ruleProofDecls, List.mem_cons] at hc
      rcases hc with rfl | hc
      · trivial
      · exact ih (i + 1) c hc
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
      · exact hproof _ _ c h₂
    · rcases List.mem_cons.mp h₁ with rfl | h₂
      · trivial
      · obtain ⟨fk, -, h₃⟩ := List.mem_flatMap.mp h₂
        have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
        rcases h₄ with rfl | rfl | rfl <;> trivial
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
    trivial

/-- Every rule a prelude command registers is a maintenance rule. -/
theorem mem_maintenanceRules_of_encodePrelude {P : Program} {r : Rule}
    (h : Cmd.rule r ∈ encodePrelude P) : r ∈ maintenanceRules P := by
  have hproof : ∀ (rs : List Rule) (i : Nat), Cmd.rule r ∉ ruleProofDecls rs i := by
    intro rs
    induction rs with
    | nil => intro i hc; simp [ruleProofDecls] at hc
    | cons s rs ih =>
      intro i hc
      rw [ruleProofDecls, List.mem_cons] at hc
      rcases hc with hc | hc
      · exact absurd hc (by simp)
      · exact ih (i + 1) hc
  rw [encodePrelude] at h
  rcases List.mem_append.mp h with h₁ | h₁
  · exfalso
    rcases List.mem_append.mp h₁ with h₂ | h₂
    · rw [proofDecls] at h₂
      rcases List.mem_append.mp h₂ with h₃ | h₃
      · rcases List.mem_append.mp h₃ with h₄ | h₄
        · revert h₄; simp
        · obtain ⟨k, -, hk⟩ := List.mem_map.mp h₄
          exact absurd hk (by simp)
      · exact hproof _ _ h₃
    · rcases List.mem_cons.mp h₂ with h₃ | h₃
      · exact absurd h₃ (by simp)
      · obtain ⟨fk, -, h₄⟩ := List.mem_flatMap.mp h₃
        revert h₄; simp
  · obtain ⟨s, hs, hse⟩ := List.mem_map.mp h₁
    obtain rfl : s = r := by injection hse
    exact hs

/-- **`FDatabase.Inv` is vacuous at empty data**, whatever the signature and rules are. -/
theorem FDatabase.Inv.of_empty_data {d : FDatabase} (ht : d.terms = []) (hr : d.rows = [])
    (he : d.eqs = []) (hv : d.env = []) : d.Inv where
  wf := by
    have hterms : ∀ t, t ∉ d.toDatabase.terms := by
      intro t hmem
      rw [FDatabase.toDatabase_terms, ht] at hmem
      exact absurd hmem (by simp)
    exact ⟨fun t hmem => absurd hmem (hterms t), fun t hmem => absurd hmem (hterms t),
      fun b hb => absurd (by rw [FDatabase.toDatabase_env, hv] at hb; exact hb) (by simp),
      by
        intro q hq _
        rcases FDatabase.mem_toDatabase_eqs.mp hq with ⟨hqe, -⟩ | ⟨hqm, -, -⟩
        · exact hqe
        · rw [he] at hqm; exact absurd hqm (by simp)⟩
  eqs := by intro p hp; rw [he] at hp; exact absurd hp (by simp)
  index := ⟨fun r hrm => absurd (by rw [hr] at hrm; exact hrm) (by simp),
    fun r hrm => absurd (by rw [hr] at hrm; exact hrm) (by simp),
    fun r hrm => absurd (by rw [hr] at hrm; exact hrm) (by simp)⟩

/-- A declaration or a rule writes no data. -/
theorem execCmdM_data_of_declOrRule {d d' : FDatabase} {c : Cmd} (hc : c.DeclOrRule)
    (hs : d.execCmdM c = some d') :
    d'.terms = d.terms ∧ d'.rows = d.rows ∧ d'.eqs = d.eqs ∧ d'.env = d.env := by
  cases c with
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact ⟨by rw [← hs], by rw [← hs], by rw [← hs], by rw [← hs]⟩
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact ⟨by rw [← hs], by rw [← hs], by rw [← hs], by rw [← hs]⟩
  | action a => exact (hc : False).elim
  | run R => exact (hc : False).elim
  | saturate R => exact (hc : False).elim

@[inherit_doc execCmdM_data_of_declOrRule]
theorem execProgramM_data_of_declOrRule {p : Program} (hp : ∀ c ∈ p, c.DeclOrRule) :
    ∀ {d d' : FDatabase}, d.execProgramM p = some d' →
      d'.terms = d.terms ∧ d'.rows = d.rows ∧ d'.eqs = d.eqs ∧ d'.env = d.env := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact ⟨by rw [← hs], by rw [← hs], by rw [← hs], by rw [← hs]⟩
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨t₁, r₁, e₁, v₁⟩ := execCmdM_data_of_declOrRule (hp c List.mem_cons_self) h₁
    obtain ⟨t₂, r₂, e₂, v₂⟩ := ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) h₂
    exact ⟨t₂.trans t₁, r₂.trans r₁, e₂.trans e₁, v₂.trans v₁⟩

/-- Every rule the state after a prelude-shaped run holds is one of the run's own. -/
theorem execProgramM_rules_of_declOrRule {p : Program} :
    ∀ {d d' : FDatabase}, d.execProgramM p = some d' →
      ∀ r ∈ d'.rules, Cmd.rule r ∈ p ∨ r ∈ d.rules := by
  induction p with
  | nil =>
    intro d d' hs r hr
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact Or.inr (by rw [← hs] at hr; exact hr)
  | cons c cs ih =>
    intro d d' hs r hr
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rcases ih h₂ r hr with hc | hc
    · exact Or.inl (List.mem_cons_of_mem c hc)
    · cases c with
      | rule s =>
        rw [FDatabase.execCmdM, Option.some.injEq] at h₁
        rcases List.mem_cons.mp (show r ∈ s :: d.rules by rw [← h₁] at hc; exact hc) with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h
      | decl f dc =>
        rw [FDatabase.execCmdM, Option.some.injEq] at h₁
        exact Or.inr (by rw [← h₁] at hc; exact hc)
      | action a =>
        rw [FDatabase.execCmdM] at h₁
        obtain ⟨d₀, ha, hm⟩ := Option.bind_eq_some_iff.mp h₁
        rw [(FDatabase.mergeSaturateF_fields hm).2.2, FDatabase.execAction_rules ha] at hc
        exact Or.inr hc
      | run R =>
        rw [FDatabase.execCmdM] at h₁
        rw [(FDatabase.runRoundM_fields h₁).2.2] at hc
        exact Or.inr hc
      | saturate R =>
        rw [FDatabase.execCmdM] at h₁
        rw [(FDatabase.runSaturateM_fields runFuel h₁).2.2] at hc
        exact Or.inr hc


/-- **The signature `encodePrelude` installs.** `encodeCmds` emits no declaration
(`noDecl_encodeCmd`), so this is the signature of *every* state the aligned run passes
through, which is what lets the two legality conditions below be stated once. -/
def encodeSig (P : Program) : Signature :=
  (encodePrelude P).foldl (fun sig c => c.sigBind sig) (fun _ => none)

theorem FDatabase.execProgramM_sig {p : Program} : ∀ {d d' : FDatabase},
    d.execProgramM p = some d' → d'.sig = p.foldl (fun sig c => c.sigBind sig) d.sig := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ rfl
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [ih h₂, execCmdM_sig h₁]
    rfl

/-- **The base case.** Everything but the two legality conditions is free at the state the
prelude leaves: it holds no term, no row and no equation, and the source has not run. -/
theorem preludeState_encOk {P : Program} {d₀ : FDatabase}
    (hmerges : Signature.MergesLegal (encodeSig P))
    (hmaint : ∀ r ∈ maintenanceRules P, Actions.WriteLegal r.actions (encodeSig P))
    (hprel : FDatabase.empty.execProgramM (encodePrelude P) = some d₀) :
    d₀.EncOk P (encodeSig P) Database.empty := by
  have hsig : d₀.sig = encodeSig P := FDatabase.execProgramM_sig hprel
  obtain ⟨ht, hrw, he, hv⟩ :=
    execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  refine ⟨⟨hsig, ?_, ?_, hmerges, FDatabase.Inv.of_empty_data ht hrw he hv,
      execProgramM_noUnions (Program.unionFree_of_mem (encodePrelude_unionFree P))
        empty_noUnions hprel, ?_⟩, ?_, ?_, ?_⟩
  · exact FDatabase.execProgramM_rulesEncoded (rulesEncodedOk_encodePrelude P)
      (fun r hr => absurd hr (by simp [FDatabase.empty])) hprel
  · rw [← hsig]
    exact FDatabase.execProgramM_mergeShape (mergeShapeOk_encodePrelude P)
      Signature.mergeShape_empty hprel
  · intro r hr
    rcases execProgramM_rules_of_declOrRule hprel r hr with hc | hc
    · exact hmaint r (mem_maintenanceRules_of_encodePrelude hc)
    · exact absurd hc (by simp [FDatabase.empty])
  · intro v t hv'
    rw [show Database.empty.env = [] from rfl] at hv'
    exact absurd hv' (by simp)
  · refine ⟨fun f cs e pf hm => ?_, fun t p pf hm => ?_⟩ <;>
      rw [ht, show FDatabase.empty.terms = ([] : List Term) from rfl] at hm <;>
      exact absurd hm (by simp)
  · intro r hr
    rcases execProgramM_rules_of_declOrRule hprel r hr with hc | hc
    · exact Or.inr (mem_maintenanceRules_of_encodePrelude hc)
    · exact absurd hc (by simp [FDatabase.empty])

/-! ## The prelude's `@UF` declaration, and the merge bodies' legality

`Signature.MergesLegal` at the encoded signature is a consequence of `Signature.MergeShape`
plus one fact the shape does not carry: what `@UF` is declared as. Both merge bodies are
`mergeBody`, whose single `set` writes `@UF` at one key column and two value columns, so the
condition is `ufDecl`'s own widths. -/

/-- **A term relation is never the union-find table**, by the last character. -/
theorem termName_ne_ufName {f : FnName} : termName f ≠ ufName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [termName, ufName, String.toList_append, List.reverse_append] at h2

/-- `Signature.MergeShape` along the fold a program's declarations perform. -/
theorem mergeShape_foldl {p : Program} (hp : ∀ c ∈ p, c.MergeShapeOk) :
    ∀ {sig : Signature}, sig.MergeShape →
      Signature.MergeShape (p.foldl (fun s c => c.sigBind s) sig) := by
  induction p with
  | nil => intro sig h; exact h
  | cons c cs ih =>
    intro sig h
    refine ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) ?_
    cases c with
    | decl f dc => exact h.update (hp _ List.mem_cons_self)
    | _ => exact h

theorem encodeSig_mergeShape (P : Program) : Signature.MergeShape (encodeSig P) :=
  mergeShape_foldl (mergeShapeOk_encodePrelude P) Signature.mergeShape_empty

/-- A source constructor is not `@UF`: it is a source name, and no source name is in the
generated namespace. -/
theorem ctor_ne_ufName {P : Program} (hdom : P.EncodeDomain) {fk : FnName × Nat}
    (h : fk ∈ P.ctors) : fk.1 ≠ ufName := by
  intro hc
  refine hdom.noAt fk.1 ?_ ?_
  · rw [Program.names]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨fk, h, rfl⟩))))
  · -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
    rw [hc]
    exact (by decide +kernel : "@".isPrefixOf ufName = true)

/-- **The prelude declares `@UF` and nothing after it redeclares the name.** The three
declarations that follow are a source constructor, a view and a term relation, and none of
them is `@UF`. -/
theorem encodeSig_ufName {P : Program} (hdom : P.EncodeDomain) :
    encodeSig P ufName = some ufDecl := by
  have hfold : ∀ (p : Program), (∀ c ∈ p, ∀ f dc, c = Cmd.decl f dc → f ≠ ufName) →
      ∀ (sig : Signature), sig ufName = some ufDecl →
        (p.foldl (fun s c => c.sigBind s) sig) ufName = some ufDecl := by
    intro p
    induction p with
    | nil => intro _ sig h; exact h
    | cons c cs ih =>
      intro hp sig h
      refine ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) _ ?_
      cases c with
      | decl f dc =>
        change Function.update sig f (some dc) ufName = some ufDecl
        rw [Function.update_of_ne (fun hc => hp _ List.mem_cons_self f dc rfl hc.symm)]
        exact h
      | _ => exact h
  rw [encodeSig, encodePrelude, List.foldl_append, List.foldl_append, List.foldl_cons]
  refine hfold _ ?_ _ (hfold _ ?_ _ ?_)
  · intro c hc f dc hcd
    obtain ⟨r, -, hr⟩ := List.mem_map.mp hc
    rw [← hr] at hcd
    exact absurd hcd (by simp)
  · intro c hc f dc hcd
    obtain ⟨fk, hfk, h₃⟩ := List.mem_flatMap.mp hc
    have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
        c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
        c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
    subst hcd
    rcases h₄ with h₅ | h₅ | h₅
    · injection h₅ with h₆
      rw [h₆]; exact ctor_ne_ufName hdom hfk
    · injection h₅ with h₆
      rw [h₆]; exact viewName_ne_ufName
    · injection h₅ with h₆
      rw [h₆]; exact termName_ne_ufName
  · simp [Cmd.sigBind]

/-- **The merge bodies are legal writes.** `Signature.MergeShape` pins both bodies to
`mergeBody`, and `mergeBody`'s one `set` writes `@UF` at `ufDecl`'s own widths. -/
theorem encodeSig_mergesLegal {P : Program} (hdom : P.EncodeDomain) :
    Signature.MergesLegal (encodeSig P) := by
  have huf := encodeSig_ufName hdom
  intro g dc body res hg hm
  obtain ⟨-, rfl, rfl, hout, -, -⟩ := encodeSig_mergeShape P g dc hg body res hm
  refine ⟨⟨⟨?_, trivial⟩, ⟨?_, trivial⟩⟩, by rw [hout]; rfl⟩
  · change (encodeSig P).mergeOf ufName ≠ none
    rw [Signature.mergeOf, huf]
    exact fun hc => absurd hc (by simp [ufDecl])
  · intro dc' hdc'
    obtain rfl : dc' = ufDecl := Option.some.inj (hdc'.symm.trans huf)
    exact ⟨rfl, rfl⟩

/-- **The residue, reduced.** `execM_soundTerms` is this theorem at four obligations, and
the reduction itself is proved: the per-command induction, the merge phase, the firing fold,
the three maintenance families and the rebuild rounds are all discharged here.

`hwlP` and `hmaint` are the two legality conditions and they are **not** consequences of
`Program.EncodeDomain`: see `Program.AritiesAgree` below. The third,
`Signature.MergesLegal`, is one, and `encodeSig_mergesLegal` is it discharged. -/
theorem execM_soundTerms_of_obligations {P : Program} (hdom : P.EncodeDomain)
    (hhead : EncodedHeadSound P (encodeSig P)) (hact : EncodedActionSound P (encodeSig P))
    (hwlP : EncodedWriteLegal P (encodeSig P))
    (hmaint : ∀ r ∈ maintenanceRules P, Actions.WriteLegal r.actions (encodeSig P))
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  exact (FDatabase.EncOk.stepCmds hdom hhead hact hwlP P [] rfl ProgramStep.nil hsrc 0 0
    (preludeState_encOk (encodeSig_mergesLegal hdom) hmaint hprel) hcmds).sound

/-- **A clause `Program.EncodeDomain` does not have, and the two legality obligations need.**

`Program.ctors` is read off the *syntax* — `Expr.ctors` records `(f, args.length)` at every
application and `Cmd.ctors` records `(f, dc.arity)` at every declaration — so a program that
applies one name at two arities contributes two entries, `encodePrelude` emits **two** table
triples for it, and the later declaration wins. The rebuild rules of the losing arity then
`set` a view at the wrong key width, which is exactly what `Actions.SetWidthOk` forbids and
`FDatabase.IndexOk.width` records.

Nothing in `Program.EncodeDomain` excludes it: `Expr.Evaluable` quantifies over
`Expr.fns`, a list of *names* that has lost the argument counts, and `Spec/Scope.lean`'s
`Action.WidthOk` — which does say it — is not among the clauses. `EncodeDomain.headsDeclared`
asks that a head's names be declared, not that they be applied at their declared arity.

**Reported, not added.** It is decidable, it costs the corpus nothing — every generated case
applies each name at its declared arity — and it is what `execM_soundTerms` still needs. It
may also be weakenable: the losing arity's rebuild rules can never *match*, since
`patternHolds` compares key tuples of different lengths, so the rows a run actually writes
are all of the surviving width; what fails is `Actions.WriteLegal`, which
`FDatabase.Inv.execCmdM` asks of every rule the state holds whether it fires or not. -/
def Program.AritiesAgree (P : Program) : Prop :=
  ∀ fk ∈ P.ctors, ∀ gl ∈ P.ctors, fk.1 = gl.1 → fk.2 = gl.2

/-! ### The clause, and the notion the tree already had

`Program.EncodeDomain.aritiesAgree` is stated over `Tests/Egg.lean`'s
`Program.arityConflicts` — the notion `Impl/Check.lean` and `Encoding/Encode.lean` already
cite as egglog's "Function already bound" — and `Program.AritiesAgree` is the form the
legality proofs consume, over `Program.ctors`. The two are the same list read two ways:
`Expr.ctors` *is* `Expr.fnArities`, and `Cmd.ctors` is contained in `Cmd.fnArities` at every
command (a `Pattern.values` head and a `:merge` body are the two entries only the latter
records, and the domain has neither). `EncodeDomain.noPrim` is what pays for the primitive
filter. -/

mutual

/-- The two readings of an expression's applied names are one. -/
theorem Expr.ctors_eq_fnArities : ∀ (e : Expr), e.ctors = e.fnArities
  | .lit _ => rfl
  | .var _ => rfl
  | .app f args => by
      rw [Expr.ctors, Expr.fnArities, Expr.ctorsList_eq_fnAritiesL args]

@[inherit_doc Expr.ctors_eq_fnArities]
theorem Expr.ctorsList_eq_fnAritiesL : ∀ (es : List Expr),
    Expr.ctorsList es = Expr.fnAritiesL es
  | [] => rfl
  | e :: es => by
      rw [Expr.ctorsList, Expr.fnAritiesL, Expr.ctors_eq_fnArities e,
        Expr.ctorsList_eq_fnAritiesL es]

end

@[inherit_doc Expr.ctors_eq_fnArities]
theorem Action.ctors_eq_fnArities (a : Action) : a.ctors = a.fnArities := by
  cases a <;>
    simp [Action.ctors, Action.fnArities, Expr.ctors_eq_fnArities,
      Expr.ctorsList_eq_fnAritiesL]

/-- A read's own head is the one entry `Program.ctors` does not record and `fnArities`
does. -/
theorem Pattern.mem_fnArities_of_mem_ctors {p : Pattern} {fk : FnName × Nat}
    (h : fk ∈ p.ctors) : fk ∈ p.fnArities := by
  cases p <;>
    simp only [Pattern.ctors, Pattern.fnArities, Expr.ctors_eq_fnArities,
      Expr.ctorsList_eq_fnAritiesL, List.cons_append, List.mem_cons, List.mem_append] at h ⊢ <;>
    tauto

@[inherit_doc Pattern.mem_fnArities_of_mem_ctors]
theorem Cmd.mem_fnArities_of_mem_ctors {c : Cmd} {fk : FnName × Nat}
    (h : fk ∈ c.ctors) : fk ∈ c.fnArities := by
  cases c with
  | action a => rw [Cmd.ctors, Action.ctors_eq_fnArities] at h; exact h
  | rule r =>
      rw [Cmd.ctors] at h
      rw [Cmd.fnArities]
      rcases List.mem_append.mp h with h' | h'
      · obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp h'
        exact List.mem_append_left _
          (List.mem_flatMap.mpr ⟨p, hp, Pattern.mem_fnArities_of_mem_ctors hf⟩)
      · obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp h'
        exact List.mem_append_right _
          (List.mem_flatMap.mpr ⟨a, ha, Action.ctors_eq_fnArities a ▸ hf⟩)
  | run R => exact absurd h (by simp [Cmd.ctors])
  | saturate R => exact absurd h (by simp [Cmd.ctors])
  | decl f dc =>
      rw [Cmd.ctors] at h
      obtain rfl : fk = (f, dc.arity) := by simpa using h
      rw [Cmd.fnArities]
      exact List.mem_cons_self

/-- A list of at most one element has at most one element. -/
private theorem eq_of_length_le_one {α : Type} {l : List α} (h : l.length ≤ 1) :
    ∀ a ∈ l, ∀ b ∈ l, a = b := by
  match l with
  | [] => intro a ha; exact absurd ha (by simp)
  | [x] => intro a ha b hb; rw [List.mem_singleton] at ha hb; rw [ha, hb]
  | x :: y :: t => exact absurd h (by simp)

/-- **The domain's clause, in the form the legality proofs consume.** -/
theorem Program.EncodeDomain.aritiesAgree' {P : Program} (h : P.EncodeDomain) :
    P.AritiesAgree := by
  have hsub : ∀ fk ∈ P.ctors, fk ∈ P.fnArities := by
    intro fk hfk
    obtain ⟨c, hc, hfc⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hfk)
    refine List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_flatMap.mpr
      ⟨c, hc, Cmd.mem_fnArities_of_mem_ctors hfc⟩, ?_⟩)
    rw [h.noPrim fk hfk]; rfl
  intro fk hfk gl hgl hname
  by_contra hne
  have hfa : fk ∈ P.fnArities := hsub fk hfk
  have hga : gl ∈ P.fnArities := hsub gl hgl
  have hlen : (P.fnArities.filter fun fa => fa.1 == fk.1).length ≤ 1 := by
    by_contra hc
    refine absurd h.aritiesAgree (fun hz => ?_)
    rw [Program.arityConflicts, List.dedup_eq_nil, List.filter_eq_nil_iff] at hz
    exact absurd (hz fk.1 (List.mem_map_of_mem hfa)) (by simpa using Nat.lt_of_not_le hc)
  refine hne ?_
  have := eq_of_length_le_one hlen fk (List.mem_filter.mpr ⟨hfa, by simp⟩)
    gl (List.mem_filter.mpr ⟨hga, by simp [hname]⟩)
  rw [this]



/-! ## The prelude's table triples, read back

`FDatabase.Inv.execCmdM` asks `Actions.WriteLegal` of every rule the state holds, so the
whole of `EncodeDomain`'s remaining bill is what the prelude declared each name as. The
declarations are the three per entry of `Program.ctors`, and a name that occurs there twice
is declared twice — which is exactly what `Program.AritiesAgree` rules out. -/

theorem isPrefixOf_at_viewName (f : FnName) : "@".isPrefixOf (viewName f) = true := by
  simp [viewName, String.isPrefixOf]

theorem isPrefixOf_at_termName (f : FnName) : "@".isPrefixOf (termName f) = true := by
  simp [termName, String.isPrefixOf]

/-- A fold over commands none of which declares `g` leaves `g` where it was. -/
theorem foldl_sigBind_of_ne {g : FnName} : ∀ (p : Program),
    (∀ c ∈ p, ∀ f dc, c = Cmd.decl f dc → f ≠ g) →
    ∀ (sig : Signature), (p.foldl (fun s c => c.sigBind s) sig) g = sig g := by
  intro p
  induction p with
  | nil => intro _ sig; rfl
  | cons c cs ih =>
    intro hp sig
    rw [List.foldl_cons, ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))]
    cases c with
    | decl f dc =>
      change Function.update sig f (some dc) g = sig g
      rw [Function.update_of_ne (fun hc => hp _ List.mem_cons_self f dc rfl hc.symm)]
    | _ => rfl

/-- The three declarations `encodePrelude` emits per entry of `Program.ctors`. -/
def ctorTriple (fk : FnName × Nat) : Program :=
  [.decl fk.1 (skolemDecl fk.2), .decl (viewName fk.1) (viewDecl fk.2),
   .decl (termName fk.1) (termDecl fk.2)]

theorem ctorTriples_eq (P : Program) :
    (P.ctors.flatMap fun fk =>
        [Cmd.decl fk.1 (skolemDecl fk.2), Cmd.decl (viewName fk.1) (viewDecl fk.2),
         Cmd.decl (termName fk.1) (termDecl fk.2)])
      = P.ctors.flatMap ctorTriple := rfl

/-- One entry's triple, at that entry's own view name and at another's. -/
theorem foldl_ctorTriple_view {f : FnName} (fk : FnName × Nat)
    (hat : ¬ "@".isPrefixOf fk.1) (sig : Signature) :
    ((ctorTriple fk).foldl (fun s c => c.sigBind s) sig) (viewName f)
      = if fk.1 = f then some (viewDecl fk.2) else sig (viewName f) := by
  have hs : ((ctorTriple fk).foldl (fun s c => c.sigBind s) sig)
      = Function.update (Function.update (Function.update sig
          fk.1 (some (skolemDecl fk.2))) (viewName fk.1) (some (viewDecl fk.2)))
          (termName fk.1) (some (termDecl fk.2)) := rfl
  have h1 : viewName f ≠ termName fk.1 := viewName_ne_termName
  rw [hs, Function.update_of_ne h1]
  by_cases hfk : fk.1 = f
  · subst hfk
    rw [Function.update_self, if_pos rfl]
  · have h2 : viewName f ≠ viewName fk.1 := fun hc => hfk (viewName_inj hc).symm
    have h3 : viewName f ≠ fk.1 := fun hc => hat (hc ▸ isPrefixOf_at_viewName f)
    rw [Function.update_of_ne h2, Function.update_of_ne h3, if_neg hfk]

@[inherit_doc foldl_ctorTriple_view]
theorem foldl_ctorTriple_term {f : FnName} (fk : FnName × Nat)
    (hat : ¬ "@".isPrefixOf fk.1) (sig : Signature) :
    ((ctorTriple fk).foldl (fun s c => c.sigBind s) sig) (termName f)
      = if fk.1 = f then some (termDecl fk.2) else sig (termName f) := by
  have hs : ((ctorTriple fk).foldl (fun s c => c.sigBind s) sig)
      = Function.update (Function.update (Function.update sig
          fk.1 (some (skolemDecl fk.2))) (viewName fk.1) (some (viewDecl fk.2)))
          (termName fk.1) (some (termDecl fk.2)) := rfl
  rw [hs]
  by_cases hfk : fk.1 = f
  · subst hfk
    rw [Function.update_self, if_pos rfl]
  · have h1 : termName f ≠ termName fk.1 := by
      intro hc
      refine hfk ?_
      have h2 := congrArg String.toList hc
      rw [termName, termName, String.toList_append, String.toList_append,
        String.toList_append, String.toList_append] at h2
      exact (String.toList_inj.mp (List.append_cancel_left (List.append_cancel_right h2))).symm
    have h3 : termName f ≠ viewName fk.1 := fun hc => viewName_ne_termName hc.symm
    have h4 : termName f ≠ fk.1 := fun hc => hat (hc ▸ isPrefixOf_at_termName f)
    rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h4,
      if_neg hfk]

/-- **Later triples do not disturb the answer**, where the arities agree: another entry of
the same name declares the same triple. -/
theorem foldl_ctorTriples_preserve : ∀ (l : List (FnName × Nat)) {f : FnName} {k : Nat},
    (∀ gl ∈ l, gl.1 = f → gl.2 = k) → (∀ gl ∈ l, ¬ "@".isPrefixOf gl.1) →
    ∀ {sig : Signature}, sig (viewName f) = some (viewDecl k) →
      sig (termName f) = some (termDecl k) →
      ((l.flatMap ctorTriple).foldl (fun s c => c.sigBind s) sig) (viewName f)
          = some (viewDecl k) ∧
        ((l.flatMap ctorTriple).foldl (fun s c => c.sigBind s) sig) (termName f)
          = some (termDecl k) := by
  intro l
  induction l with
  | nil => intro _ _ _ _ sig hv ht; exact ⟨hv, ht⟩
  | cons gl l ih =>
    intro f k hag hat sig hv ht
    rw [List.flatMap_cons, List.foldl_append]
    refine ih (fun x hx => hag x (List.mem_cons_of_mem gl hx))
      (fun x hx => hat x (List.mem_cons_of_mem gl hx)) ?_ ?_
    · rw [foldl_ctorTriple_view gl (hat gl List.mem_cons_self)]
      by_cases hg : gl.1 = f
      · rw [if_pos hg, hag gl List.mem_cons_self hg]
      · rw [if_neg hg]; exact hv
    · rw [foldl_ctorTriple_term gl (hat gl List.mem_cons_self)]
      by_cases hg : gl.1 = f
      · rw [if_pos hg, hag gl List.mem_cons_self hg]
      · rw [if_neg hg]; exact ht

/-- **The triple of the entry that is there.** -/
theorem foldl_ctorTriples_found : ∀ (l : List (FnName × Nat)) {f : FnName} {k : Nat},
    (f, k) ∈ l → (∀ gl ∈ l, gl.1 = f → gl.2 = k) → (∀ gl ∈ l, ¬ "@".isPrefixOf gl.1) →
    ∀ (sig : Signature),
      ((l.flatMap ctorTriple).foldl (fun s c => c.sigBind s) sig) (viewName f)
          = some (viewDecl k) ∧
        ((l.flatMap ctorTriple).foldl (fun s c => c.sigBind s) sig) (termName f)
          = some (termDecl k) := by
  intro l
  induction l with
  | nil => intro _ _ hm; exact absurd hm (by simp)
  | cons gl l ih =>
    intro f k hm hag hat sig
    rw [List.flatMap_cons, List.foldl_append]
    rcases List.mem_cons.mp hm with rfl | hm'
    · refine foldl_ctorTriples_preserve l (fun x hx => hag x (List.mem_cons_of_mem _ hx))
        (fun x hx => hat x (List.mem_cons_of_mem _ hx)) ?_ ?_
      · rw [foldl_ctorTriple_view (f, k) (hat _ List.mem_cons_self), if_pos rfl]
      · rw [foldl_ctorTriple_term (f, k) (hat _ List.mem_cons_self), if_pos rfl]
    · exact ih hm' (fun x hx => hag x (List.mem_cons_of_mem gl hx))
        (fun x hx => hat x (List.mem_cons_of_mem gl hx)) _

/-- A source name is not in the generated namespace. -/
theorem noAt_of_mem_ctors {P : Program} (hdom : P.EncodeDomain) {fk : FnName × Nat}
    (h : fk ∈ P.ctors) : ¬ "@".isPrefixOf fk.1 :=
  hdom.noAt fk.1 (by
    rw [Program.names]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨fk, h, rfl⟩)))))

/-- **The view and term declarations the prelude installs**, at each entry of
`Program.ctors`. `Program.AritiesAgree` is what makes the answer that entry's own arity: a
name occurring twice is declared twice and the second declaration wins. -/
theorem encodeSig_tables {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {f : FnName} {k : Nat} (h : (f, k) ∈ P.ctors) :
    encodeSig P (viewName f) = some (viewDecl k) ∧
      encodeSig P (termName f) = some (termDecl k) := by
  have hrules : ∀ c ∈ (maintenanceRules P).map Cmd.rule, ∀ g dc, c = Cmd.decl g dc → g ≠ g := by
    intro c hc g dc hcd
    obtain ⟨r, -, hr⟩ := List.mem_map.mp hc
    rw [← hr] at hcd
    exact absurd hcd (by simp)
  constructor <;>
  · rw [encodeSig, encodePrelude, List.foldl_append, List.foldl_append, List.foldl_cons,
      foldl_sigBind_of_ne _ (fun c hc g dc hcd => by
        obtain ⟨r, -, hr⟩ := List.mem_map.mp hc
        rw [← hr] at hcd
        exact absurd hcd (by simp)), ctorTriples_eq]
    first
    | exact (foldl_ctorTriples_found P.ctors h
        (fun gl hgl hg => (hag (f, k) h gl hgl hg.symm).symm)
        (fun gl hgl => noAt_of_mem_ctors hdom hgl) _).1
    | exact (foldl_ctorTriples_found P.ctors h
        (fun gl hgl hg => (hag (f, k) h gl hgl hg.symm).symm)
        (fun gl hgl => noAt_of_mem_ctors hdom hgl) _).2


/-! ## `EncodedWriteLegal` and its maintenance counterpart, under the missing clause

Every `set` the encoding emits writes `@UF` or a view, at the widths the prelude declared —
provided the prelude declared each name once, which is `Program.AritiesAgree`. -/

/-- One `set`, at a declaration that carries a `:merge` and whose widths it matches. -/
theorem writeLegal_set {sig : Signature} {g : FnName} {dc : FnDecl}
    (hsig : sig g = some dc) (hm : dc.merge ≠ none) {args out : List Expr}
    (ha : args.length = dc.arity) (ho : out.length = dc.outArity) :
    Actions.WriteLegal [Action.set g args out] sig := by
  refine ⟨⟨?_, trivial⟩, ?_, trivial⟩
  · change sig.mergeOf g ≠ none
    rw [Signature.mergeOf, hsig]
    exact fun hc => hm (by simpa using hc)
  · intro dc' hdc'
    obtain rfl : dc' = dc := Option.some.inj (hdc'.symm.trans hsig)
    exact ⟨ha, ho⟩

theorem Actions.WriteLegal.append {sig : Signature} : ∀ {as bs : List Action},
    Actions.WriteLegal as sig → Actions.WriteLegal bs sig →
      Actions.WriteLegal (as ++ bs) sig
  | [], _, _, hb => hb
  | _ :: as, _, ha, hb =>
      ⟨⟨ha.1.1, (Actions.WriteLegal.append (as := as) ⟨ha.1.2, ha.2.2⟩ hb).1⟩,
        ha.2.1, (Actions.WriteLegal.append (as := as) ⟨ha.1.2, ha.2.2⟩ hb).2⟩

/-- An action that is not a `set` writes legally, whatever the signature. -/
theorem writeLegal_of_noSet {sig : Signature} {a : Action} (h : a.NoSet) :
    Actions.WriteLegal [a] sig := by
  cases a with
  | set f args out => exact (h : False).elim
  | _ => exact ⟨⟨trivial, trivial⟩, trivial, trivial⟩

mutual

/-- **A build block writes legally.** Each application emits its term row and its view entry,
at the widths the prelude declared for that name and arity. -/
theorem writeLegal_encodeBuild {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree) :
    ∀ (e : Expr) (m : Nat), (∀ fk ∈ e.ctors, fk ∈ P.ctors) →
      Actions.WriteLegal (encodeBuild e m).2.1 (encodeSig P)
  | .lit _, _, _ => ⟨trivial, trivial⟩
  | .var _, _, _ => ⟨trivial, trivial⟩
  | .app f args, m, hc => by
      have hfk : (f, args.length) ∈ P.ctors := hc _ (by rw [Expr.ctors]; exact List.mem_cons_self)
      obtain ⟨hview, hterm⟩ := encodeSig_tables hdom hag hfk
      rw [encodeBuild_app_actions_eq]
      refine Actions.WriteLegal.append
        (writeLegal_encodeBuildArgs hdom hag args m
          (fun fk hfk' => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hfk'))) ?_
      exact Actions.WriteLegal.append
        (writeLegal_set hterm (by simp [termDecl]) (by simp [termDecl]) (by simp [termDecl]))
        (writeLegal_set hview (by simp [viewDecl]) rfl rfl)

@[inherit_doc writeLegal_encodeBuild]
theorem writeLegal_encodeBuildArgs {P : Program} (hdom : P.EncodeDomain)
    (hag : P.AritiesAgree) :
    ∀ (es : List Expr) (m : Nat), (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) →
      Actions.WriteLegal (encodeBuildArgs es m).2.1 (encodeSig P)
  | [], _, _ => ⟨trivial, trivial⟩
  | e :: es, m, hc => by
      rw [encodeBuildArgs_cons_actions]
      exact Actions.WriteLegal.append
        (writeLegal_encodeBuild hdom hag e m
          (fun fk h => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ h)))
        (writeLegal_encodeBuildArgs hdom hag es _
          (fun fk h => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ h)))

end

/-- **One head action's block writes legally.** A source `set` is out of the fragment
(`EncodeDomain.setLegal` under `ctorsOnly`), which is why it is excluded rather than
encoded. -/
theorem writeLegal_encodeAction {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    (pf : Expr) : ∀ (a : Action) (m : Nat), a.NoSet → (∀ fk ∈ a.ctors, fk ∈ P.ctors) →
      Actions.WriteLegal (encodeAction pf a m).1 (encodeSig P) := by
  rintro (e | ⟨v, e⟩ | ⟨e₁, e₂⟩ | ⟨f, args, out⟩) m hns hc
  · rw [encodeAction_expr_actions]
    exact writeLegal_encodeBuild hdom hag e m hc
  · rw [encodeAction_letBind_actions]
    exact Actions.WriteLegal.append (writeLegal_encodeBuild hdom hag e m hc)
      (writeLegal_of_noSet trivial)
  · rw [encodeAction_union_actions]
    refine Actions.WriteLegal.append (Actions.WriteLegal.append
      (writeLegal_encodeBuild hdom hag e₁ m
        (fun fk h => hc fk (by rw [Action.ctors]; exact List.mem_append_left _ h)))
      (writeLegal_encodeBuild hdom hag e₂ _
        (fun fk h => hc fk (by rw [Action.ctors]; exact List.mem_append_right _ h)))) ?_
    exact writeLegal_set (encodeSig_ufName hdom) (by simp [ufDecl]) rfl rfl
  · exact (hns : False).elim

@[inherit_doc writeLegal_encodeAction]
theorem writeLegal_encodeActions {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    (pf : Expr) : ∀ (as : List Action) (m : Nat), (∀ a ∈ as, a.NoSet) →
      (∀ a ∈ as, ∀ fk ∈ a.ctors, fk ∈ P.ctors) →
      Actions.WriteLegal (encodeActions pf as m).1 (encodeSig P)
  | [], _, _, _ => ⟨trivial, trivial⟩
  | a :: as, m, hns, hc => by
      rw [encodeActions_cons_actions]
      exact Actions.WriteLegal.append
        (writeLegal_encodeAction hdom hag pf a m (hns a List.mem_cons_self)
          (hc a List.mem_cons_self))
        (writeLegal_encodeActions hdom hag pf as _
          (fun b hb => hns b (List.mem_cons_of_mem a hb))
          (fun b hb => hc b (List.mem_cons_of_mem a hb)))

/-- Every `(name, arity)` pair a source command mentions is one the prelude declared. -/
theorem mem_ctors_of_cmd {P : Program} {c : Cmd} (hc : c ∈ P) {fk : FnName × Nat}
    (h : fk ∈ c.ctors) : fk ∈ P.ctors :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨c, hc, h⟩)

/-- **`EncodedWriteLegal`, under the missing clause.** -/
theorem encodedWriteLegal {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree) :
    EncodedWriteLegal P (encodeSig P) := by
  have hnoset : ∀ c ∈ P, c.NoSet :=
    (Program.setLegal_iff_noSet (fun _ => rfl) hdom.ctorsOnly).mp hdom.setLegal
  intro c hcP n i c' hc'
  have hns := hnoset c hcP
  have hct : ∀ fk ∈ c.ctors, fk ∈ P.ctors := fun fk hfk => mem_ctors_of_cmd hcP hfk
  cases c with
  | decl f dc =>
    have h : c' ∈ ([] : Program) := hc'
    simp at h
  | run R =>
    have h : c' ∈ [Cmd.run R, Cmd.saturate rebuildRuleset] := hc'
    have h2 : c' = Cmd.run R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
    rcases h2 with rfl | rfl <;> trivial
  | saturate R =>
    have h : c' ∈ [Cmd.saturate R, Cmd.saturate rebuildRuleset] := hc'
    have h2 : c' = Cmd.saturate R ∨ c' = Cmd.saturate rebuildRuleset := by simpa using h
    rcases h2 with rfl | rfl <;> trivial
  | action a =>
    have h : c' ∈ (encodeAction fiatE a n).1.map Cmd.action ++ [Cmd.saturate rebuildRuleset] :=
      hc'
    rcases List.mem_append.mp h with h₁ | h₁
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₁
      have hall := writeLegal_encodeAction hdom hag fiatE a n hns hct
      have : ∀ (bs : List Action), Actions.WriteLegal bs (encodeSig P) →
          ∀ b ∈ bs, Actions.WriteLegal [b] (encodeSig P) := by
        intro bs
        induction bs with
        | nil => intro _ b hb; exact absurd hb (by simp)
        | cons x xs ih =>
          intro hx b hb
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ⟨⟨hx.1.1, trivial⟩, hx.2.1, trivial⟩
          · exact ih ⟨hx.1.2, hx.2.2⟩ b hb'
      exact ⟨(this _ hall b hb).1.1, (this _ hall b hb).2.1⟩
    · obtain rfl : c' = Cmd.saturate rebuildRuleset := by simpa using h₁
      trivial
  | rule r =>
    have h : c' ∈ [Cmd.rule (encodeRule i r n).1] := hc'
    obtain rfl : c' = Cmd.rule (encodeRule i r n).1 := by simpa using h
    exact writeLegal_encodeActions hdom hag _ r.actions _ hns
      (fun a ha fk hfk => hct fk (by
        rw [Cmd.ctors]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hfk⟩)))

/-- **The maintenance rules write legally too**, under the same clause: each rebuild rule
keys its view at the arity of the entry it came from. -/
theorem maintenance_writeLegal {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree) :
    ∀ r ∈ maintenanceRules P, Actions.WriteLegal r.actions (encodeSig P) := by
  intro r hr
  rw [maintenanceRules, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact writeLegal_set (encodeSig_ufName hdom) (by simp [ufDecl]) rfl rfl
  · obtain ⟨fk, hfk, hmem⟩ := List.mem_flatMap.mp hr
    have hview : encodeSig P (viewName fk.1) = some (viewDecl fk.2) :=
      (encodeSig_tables hdom hag (by simpa using hfk)).1
    rw [rebuildRules, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact writeLegal_set hview (by simp [viewDecl])
        (by simp [rebuildVars, viewDecl]) rfl
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hmem
      exact writeLegal_set hview (by simp [viewDecl])
        (by simp [rebuildVars, viewDecl]) rfl


/-- **The residue, reduced to two firings and one missing clause.**

`execM_soundTerms_of_obligations` with its two legality conditions discharged, so what is
left of the completeness half is exactly:

* `EncodedHeadSound` — one firing of one encoded **source rule**, which is
  `entrySound_headBuild_post` and `cong_headUnion_post` at the writes `encodeActions` emits,
  with `Rule.HeadScoped` and `hlet` the two conditions still to be arranged;
* `EncodedActionSound` — one **top-level** action's block, which is `entrySound_build` and
  `cong_of_eqs` at the same writes, over the source's own `evalAction`. **Proved** below,
  as `encodedActionSound`; `execM_soundTerms_of_head` is this theorem with it discharged;
* `Program.AritiesAgree` — a clause `Program.EncodeDomain` does not have, whose necessity
  `adProgram_not_maintenance_writeLegal` records.

Everything else — the per-command induction, the merge phase, the firing fold, the three
maintenance families, the rebuild rounds, the saturating case and both legality
conditions — is proved, and this theorem is `sorryAx`-free. -/
theorem execM_soundTerms_of_firings {P : Program} (hdom : P.EncodeDomain)
    (hag : P.AritiesAgree) (hhead : EncodedHeadSound P (encodeSig P))
    (hact : EncodedActionSound P (encodeSig P))
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src :=
  execM_soundTerms_of_obligations hdom hhead hact (encodedWriteLegal hdom hag)
    (maintenance_writeLegal hdom hag) hsrc htgt


/-! ## A block of `set`s, against the invariant

Both remaining obligations are about the same thing: the block `encodeActions` emits, run
either as a rule head (`execLocalActions` *is* `execActions`) or as a run of top-level
`Cmd.action`s. A build's block is `set`s only (`encodeBuild_isSet`), so neither the signature
nor the environment moves inside it and every one of its writes evaluates its operands in the
state the block started from — which is what makes the obligations a fixed list, one per
application the built expression applies. -/

/-- **What one block of `set`s owes the invariant**, at the values it computes in the state
the block starts from: the recorded-subterm clause at each column, `EntrySound` where the
write is a view entry, and `Cong` where it is an `@UF` edge. -/
def WritesJustified (src : Database) (d₀ : FDatabase) (bs : List Action) : Prop :=
  ∀ g args out, Action.set g args out ∈ bs → ∀ is vs,
    Expr.evalList d₀.sig args d₀.env = some is →
    Expr.evalList d₀.sig out d₀.env = some vs →
    (∀ c ∈ is ++ vs, ∀ s ∈ c.subtermList, s.EntryShaped → s ∈ d₀.terms) ∧
    (∀ f cs x pf, Term.app g (is ++ vs) = Term.app (viewName f) (cs ++ [x, pf]) →
      EntrySound src f cs x) ∧
    (∀ x p pf, Term.app g (is ++ vs) = Term.app ufName [x, p, pf] → Cong src x p)

theorem WritesJustified.append {src : Database} {d₀ : FDatabase} {as bs : List Action}
    (ha : WritesJustified src d₀ as) (hb : WritesJustified src d₀ bs) :
    WritesJustified src d₀ (as ++ bs) := by
  intro g args out hmem
  rcases List.mem_append.mp hmem with h | h
  · exact ha g args out h
  · exact hb g args out h

theorem WritesJustified.mono {src : Database} {d₀ : FDatabase} {as bs : List Action}
    (hsub : ∀ b ∈ as, b ∈ bs) (h : WritesJustified src d₀ bs) : WritesJustified src d₀ as :=
  fun g args out hmem => h g args out (hsub _ hmem)

/-- **A block of `set`s preserves the invariant**, given that each write is justified at the
values it computes in the state the block starts from. The recorded-subterm clause is paid
once per column by `entryShaped_mem_of_columns`. -/
theorem execActions_soundTerms_of_sets {src : Database} {d₀ : FDatabase} :
    ∀ (bs : List Action), (∀ b ∈ bs, b.IsSet) → WritesJustified src d₀ bs →
      ∀ {d d' : FDatabase}, d.sig = d₀.sig → d.env = d₀.env →
        (∀ t ∈ d₀.terms, t ∈ d.terms) → d.SoundTerms src →
        execActions d bs = some d' → d'.SoundTerms src := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ d d' _ _ _ hs hrun
    rw [execActions, Option.some.injEq] at hrun
    exact hrun ▸ hs
  | cons b bs ih =>
    intro hset hjust d d' hsig henv hmono hs hrun
    cases hb : execAction d b with
    | none => rw [execActions, hb] at hrun; simp at hrun
    | some d₁ =>
      rw [execActions, hb, Option.bind_some] at hrun
      have hbset : b.IsSet := hset b List.mem_cons_self
      obtain ⟨g, args, out, rfl⟩ : ∃ g args out, b = Action.set g args out := by
        cases b with
        | set g args out => exact ⟨g, args, out, rfl⟩
        | _ => exact (hbset : False).elim
      obtain ⟨is, vs, has, hvs, rfl⟩ := execAction_set hb
      rw [hsig, henv] at has hvs
      obtain ⟨hsub, hview, huf⟩ := hjust g args out List.mem_cons_self is vs has hvs
      refine ih (fun b' hb' => hset b' (List.mem_cons_of_mem _ hb'))
        (fun g' a' o' h' => hjust g' a' o' (List.mem_cons_of_mem _ h'))
        (d := FDatabase.addRow g is vs d) hsig henv
        (fun t ht => FDatabase.mem_addRow_terms.mpr (Or.inr (hmono t ht)))
        (hs.addRow_top (entryShaped_mem_of_columns
          (fun c hc s hsm hshaped => hmono s (hsub c hc s hsm hshaped))) hview huf) hrun

/-! ### What a build's block writes

One term row and one view entry per application, keyed on the arguments' own naming
expressions — which `encodeBuild_fst` says are the arguments themselves. -/

mutual

/-- **Every action a build emits is one of its applications' two `set`s.** -/
theorem mem_encodeBuild_actions : ∀ (e : Expr) (m : Nat), ∀ b ∈ (encodeBuild e m).2.1,
    ∃ f args, (f, args) ∈ e.apps ∧
      (b = Action.set (termName f) (args ++ [.app f args]) [] ∨
        b = Action.set (viewName f) args [.app f args, fiatE])
  | .lit _, _, _, hb => absurd hb (by simp [encodeBuild])
  | .var _, _, _, hb => absurd hb (by simp [encodeBuild])
  | .app f args, m, b, hb => by
      rw [encodeBuild_app_actions_eq] at hb
      rcases List.mem_append.mp hb with h | h
      · obtain ⟨g, gargs, hga, hb'⟩ := mem_encodeBuildArgs_actions args m b h
        exact ⟨g, gargs, by rw [Expr.apps]; exact List.mem_cons_of_mem _ hga, hb'⟩
      · have h2 : b = Action.set (termName f) (args ++ [.app f args]) [] ∨
            b = Action.set (viewName f) args [.app f args, fiatE] := by simpa using h
        exact ⟨f, args, by rw [Expr.apps]; exact List.mem_cons_self, h2⟩

@[inherit_doc mem_encodeBuild_actions]
theorem mem_encodeBuildArgs_actions : ∀ (es : List Expr) (m : Nat),
    ∀ b ∈ (encodeBuildArgs es m).2.1,
      ∃ f args, (f, args) ∈ Expr.appsList es ∧
        (b = Action.set (termName f) (args ++ [.app f args]) [] ∨
          b = Action.set (viewName f) args [.app f args, fiatE])
  | [], _, _, hb => absurd hb (by simp [encodeBuildArgs])
  | e :: es, m, b, hb => by
      rw [encodeBuildArgs_cons_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · obtain ⟨g, gargs, hga, hb'⟩ := mem_encodeBuild_actions e m b h
        exact ⟨g, gargs, by rw [Expr.appsList]; exact List.mem_append_left _ hga, hb'⟩
      · obtain ⟨g, gargs, hga, hb'⟩ := mem_encodeBuildArgs_actions es _ b h
        exact ⟨g, gargs, by rw [Expr.appsList]; exact List.mem_append_right _ hga, hb'⟩

end


mutual

/-- An application a build emits actions for is one whose names the expression applies. -/
theorem fns_of_mem_apps : ∀ (e : Expr) {f : FnName} {args : List Expr},
    (f, args) ∈ e.apps → f ∈ e.fns ∧ ∀ g ∈ Expr.fnsList args, g ∈ e.fns
  | .lit _, _, _, h => absurd h (by simp [Expr.apps])
  | .var _, _, _, h => absurd h (by simp [Expr.apps])
  | .app g gargs, f, args, h => by
      rw [Expr.apps, List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ : f = g ∧ args = gargs := by
          exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
        exact ⟨by rw [Expr.fns]; exact List.mem_cons_self,
          fun x hx => by rw [Expr.fns]; exact List.mem_cons_of_mem _ hx⟩
      · obtain ⟨h₁, h₂⟩ := fnsList_of_mem_appsList gargs h
        exact ⟨by rw [Expr.fns]; exact List.mem_cons_of_mem _ h₁,
          fun x hx => by rw [Expr.fns]; exact List.mem_cons_of_mem _ (h₂ x hx)⟩

@[inherit_doc fns_of_mem_apps]
theorem fnsList_of_mem_appsList : ∀ (es : List Expr) {f : FnName} {args : List Expr},
    (f, args) ∈ Expr.appsList es →
      f ∈ Expr.fnsList es ∧ ∀ g ∈ Expr.fnsList args, g ∈ Expr.fnsList es
  | [], _, _, h => absurd h (by simp [Expr.appsList])
  | e :: es, f, args, h => by
      rw [Expr.appsList] at h
      rcases List.mem_append.mp h with h' | h'
      · obtain ⟨h₁, h₂⟩ := fns_of_mem_apps e h'
        exact ⟨by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inl h₁),
          fun x hx => by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inl (h₂ x hx))⟩
      · obtain ⟨h₁, h₂⟩ := fnsList_of_mem_appsList es h'
        exact ⟨by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inr h₁),
          fun x hx => by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inr (h₂ x hx))⟩

end

/-- **One build's block, against the invariant.** Its `set`s are one term row and one view
entry per application, so the whole of what the block owes is `EntrySound` at each
application's own value — and `entrySound_build` makes that "the source holds it", which is
`hheld` and the only place either remaining obligation differs.

`hne` and `hprim` are `Program.EncodeDomain.noAt` and `.noPrim` at the built expression: a
head in the generated namespace could mint a view entry the invariant would then have to
justify twice, and a head shadowing a primitive would make the value column the primitive's
result rather than the application. -/
theorem encodeBuild_writesJustified {src : Database} (hw : src.WF) {d₀ : FDatabase}
    (hsc : d₀.SubtermClosed) (henvm : ∀ b ∈ d₀.env, b.2 ∈ d₀.terms) (e : Expr) (m : Nat)
    (hne : ∀ g ∈ e.fns, NotEntryHead g) (hprim : ∀ g ∈ e.fns, Prim.ofName g = none)
    (hheld : ∀ (f : FnName) (args : List Expr), (f, args) ∈ e.apps → ∀ is,
      Expr.evalList d₀.sig args d₀.env = some is → Term.app f is ∈ src.terms) :
    WritesJustified src d₀ (encodeBuild e m).2.1 := by
  have hbind : ∀ (v : Var), ∀ u, Env.lookup v d₀.env = some u →
      ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d₀.terms :=
    fun v u hu => entryShaped_mem_of_held hsc (henvm (v, u) (Env.mem_of_lookup hu))
  intro g args out hmem is vs has hvs
  obtain ⟨f, fargs, hfa, hshape⟩ := mem_encodeBuild_actions e m _ hmem
  obtain ⟨hfmem, hfargs⟩ := fns_of_mem_apps e hfa
  have hevArgs : ∀ {fis : List Term}, Expr.evalList d₀.sig fargs d₀.env = some fis →
      ∀ u ∈ fis, ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d₀.terms := by
    intro fis hfis
    exact entryShaped_mem_of_evalList fargs (fun x hx => hne x (hfargs x hx))
      (fun v _ => hbind v) hfis
  have hevApp : ∀ {v : Term}, (Expr.app f fargs).eval d₀.sig d₀.env = some v →
      ∀ s ∈ v.subtermList, s.EntryShaped → s ∈ d₀.terms := by
    intro v hv
    refine entryShaped_mem_of_eval (Expr.app f fargs) (fun x hx => ?_) (fun w _ => hbind w) hv
    rw [Expr.fns, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hne x hfmem
    · exact hne x (hfargs x hx)
  rcases hshape with h | h
  · -- the term row: of neither shape, so only the recorded-subterm clause is live
    injection h with hg ha ho
    subst hg; subst ha; subst ho
    obtain ⟨fis, vs', hfis, hvs', rfl⟩ := Expr.evalList_append has
    obtain ⟨v, hv, rfl⟩ := Expr.evalList_single hvs'
    obtain rfl : vs = [] := by
      rw [Expr.evalList, Option.some.injEq] at hvs; exact hvs.symm
    refine ⟨fun c hc s hsm hshaped => ?_, fun f' cs x pf hq => ?_, fun x p pf hq => ?_⟩
    · rw [List.append_nil, List.mem_append] at hc
      rcases hc with hc | hc
      · exact hevArgs hfis c hc s hsm hshaped
      · obtain rfl : c = v := by simpa using hc
        exact hevApp hv s hsm hshaped
    · exact absurd (Term.app.inj hq).1 (fun hz => viewName_ne_termName hz.symm)
    · exact absurd (Term.app.inj hq).1 termName_ne_ufName
  · -- the view entry: `entrySound_build` at the application's own value
    injection h with hg ha ho
    subst hg; subst ha; subst ho
    obtain ⟨v, pfv, hv, hpf, rfl⟩ := Expr.evalList_pair hvs
    obtain ⟨fis, hfis, hveq⟩ := Expr.eval_app_of_noPrim (hprim f hfmem) hv
    have hfeq : fis = is := Option.some.inj (hfis.symm.trans has)
    subst hfeq
    subst hveq
    refine ⟨fun c hc s hsm hshaped => ?_, fun f' cs x pf hq => ?_, fun x p pf hq => ?_⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact hevArgs hfis c hc s hsm hshaped
      · have hc2 : c = Term.app f fis ∨ c = pfv := by simpa using hc
        rcases hc2 with rfl | rfl
        · exact hevApp hv s hsm hshaped
        · refine entryShaped_mem_of_eval fiatE (fun x hx => ?_) (fun w _ => hbind w) hpf
            s hsm hshaped
          obtain rfl : x = fiatName := by simpa [fiatE, Expr.fns, Expr.fnsList] using hx
          exact notEntryHead_fiatName
    · obtain ⟨hfname, hcols⟩ := Term.app.inj hq
      have hff : f' = f := viewName_inj hfname.symm
      obtain ⟨hcs, hlast⟩ := List.append_inj' hcols rfl
      have hxe : Term.app f fis = x := (List.cons.inj hlast).1
      rw [hff, ← hcs, ← hxe]
      exact entrySound_build hw (hheld f args hfa fis hfis)
    · exact absurd (Term.app.inj hq).1 viewName_ne_ufName


/-! ### What the source's own evaluation delivers

A top-level action's block is justified against the source's `evalAction`, and three facts
about a successful `Expr.eval` are the whole of what that gives: every variable it reads is
bound, every name it applies is a declared constructor, and every *sub*application's value is
a subterm of the value — which is what `Database.addTerm` then records. -/

mutual

/-- A successful evaluation binds every variable and declares every applied name. -/
theorem bound_ctor_of_eval {sig : Signature} {ρ : Env} :
    ∀ (e : Expr), (∀ g ∈ e.fns, Prim.ofName g = none) → ∀ {t : Term}, e.eval sig ρ = some t →
      (∀ v ∈ e.vars, (Env.lookup v ρ).isSome) ∧ ∀ g ∈ e.fns, sig.IsCtor g
  | .lit _, _, _, _ => ⟨fun v hv => absurd hv (by simp [Expr.vars]),
      fun g hg => absurd hg (by simp [Expr.fns])⟩
  | .var w, _, t, h => by
      rw [Expr.eval] at h
      refine ⟨fun v hv => ?_, fun g hg => absurd hg (by simp [Expr.fns])⟩
      obtain rfl : v = w := by simpa [Expr.vars] using hv
      rw [h]; rfl
  | .app f args, hp, t, h => by
      have hpf : Prim.ofName f = none := hp f (by rw [Expr.fns]; exact List.mem_cons_self)
      have hpl : ∀ g ∈ Expr.fnsList args, Prim.ofName g = none :=
        fun g hg => hp g (by rw [Expr.fns]; exact List.mem_cons_of_mem _ hg)
      simp only [Expr.eval, hpf] at h
      split at h
      · next hct =>
        obtain ⟨is, his, -⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hv, hc⟩ := boundList_ctorList_of_evalList args hpl his
        refine ⟨fun v hvv => hv v (by rwa [Expr.vars] at hvv), fun g hg => ?_⟩
        rw [Expr.fns, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact hct
        · exact hc g hg
      · exact absurd h (by simp)

@[inherit_doc bound_ctor_of_eval]
theorem boundList_ctorList_of_evalList {sig : Signature} {ρ : Env} :
    ∀ (es : List Expr), (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
      ∀ {ts : List Term}, Expr.evalList sig es ρ = some ts →
        (∀ v ∈ Expr.varsList es, (Env.lookup v ρ).isSome) ∧
          ∀ g ∈ Expr.fnsList es, sig.IsCtor g
  | [], _, _, _ => ⟨fun v hv => absurd hv (by simp [Expr.varsList]),
      fun g hg => absurd hg (by simp [Expr.fnsList])⟩
  | e :: es, hp, ts, h => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp h'
      obtain ⟨hv₁, hc₁⟩ := bound_ctor_of_eval e
        (fun g hg => hp g (by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inl hg))) ht
      obtain ⟨hv₂, hc₂⟩ := boundList_ctorList_of_evalList es
        (fun g hg => hp g (by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inr hg))) hus
      refine ⟨fun v hvv => ?_, fun g hg => ?_⟩
      · rw [Expr.varsList] at hvv
        rcases List.mem_union_iff.mp hvv with hvv | hvv
        · exact hv₁ v hvv
        · exact hv₂ v hvv
      · rw [Expr.fnsList] at hg
        rcases List.mem_union_iff.mp hg with hg | hg
        · exact hc₁ g hg
        · exact hc₂ g hg

end

mutual

/-- **Every subapplication's value is a subterm of the value.** -/
theorem exists_subterm_of_mem_apps {sig : Signature} {ρ : Env} :
    ∀ (e : Expr), (∀ g ∈ e.fns, Prim.ofName g = none) → ∀ {t : Term}, e.eval sig ρ = some t →
      ∀ (f : FnName) (args : List Expr), (f, args) ∈ e.apps →
        ∃ is, Expr.evalList sig args ρ = some is ∧ Term.app f is ∈ t.subterms
  | .lit _, _, _, _, _, _, hm => absurd hm (by simp [Expr.apps])
  | .var _, _, _, _, _, _, hm => absurd hm (by simp [Expr.apps])
  | .app g gargs, hp, t, h, f, args, hm => by
      have hpf : Prim.ofName g = none := hp g (by rw [Expr.fns]; exact List.mem_cons_self)
      obtain ⟨gis, hgis, rfl⟩ := Expr.eval_app_of_noPrim hpf h
      rw [Expr.apps, List.mem_cons] at hm
      rcases hm with hm | hm
      · obtain ⟨rfl, rfl⟩ : f = g ∧ args = gargs := ⟨(Prod.mk.inj hm).1, (Prod.mk.inj hm).2⟩
        exact ⟨gis, hgis, Term.self_mem_subterms _⟩
      · obtain ⟨is, his, u, hu, hsub⟩ := exists_subterm_of_mem_appsList gargs
          (fun x hx => hp x (by rw [Expr.fns]; exact List.mem_cons_of_mem _ hx)) hgis f args hm
        exact ⟨is, his, Term.arg_subterms hu hsub⟩

@[inherit_doc exists_subterm_of_mem_apps]
theorem exists_subterm_of_mem_appsList {sig : Signature} {ρ : Env} :
    ∀ (es : List Expr), (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
      ∀ {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ (f : FnName) (args : List Expr), (f, args) ∈ Expr.appsList es →
        ∃ is, Expr.evalList sig args ρ = some is ∧ ∃ u ∈ ts, Term.app f is ∈ u.subterms
  | [], _, _, _, _, _, hm => absurd hm (by simp [Expr.appsList])
  | e :: es, hp, ts, h, f, args, hm => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
      rw [Expr.appsList] at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨is, his, hsub⟩ := exists_subterm_of_mem_apps e
          (fun x hx => hp x (by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inl hx)))
          ht f args hm
        exact ⟨is, his, t, List.mem_cons_self, hsub⟩
      · obtain ⟨is, his, u, hu, hsub⟩ := exists_subterm_of_mem_appsList es
          (fun x hx => hp x (by rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inr hx)))
          hus f args hm
        exact ⟨is, his, u, List.mem_cons_of_mem _ hu, hsub⟩

end


mutual

/-- A name an expression applies is one `Expr.ctors` records, at that occurrence's arity. -/
theorem exists_ctor_of_mem_fns : ∀ (e : Expr) {g : FnName}, g ∈ e.fns → ∃ k, (g, k) ∈ e.ctors
  | .lit _, _, h => absurd h (by simp [Expr.fns])
  | .var _, _, h => absurd h (by simp [Expr.fns])
  | .app f args, g, h => by
      rw [Expr.fns, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨args.length, by rw [Expr.ctors]; exact List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := exists_ctor_of_mem_fnsList args h
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk⟩

@[inherit_doc exists_ctor_of_mem_fns]
theorem exists_ctor_of_mem_fnsList : ∀ (es : List Expr) {g : FnName},
    g ∈ Expr.fnsList es → ∃ k, (g, k) ∈ Expr.ctorsList es
  | [], _, h => absurd h (by simp [Expr.fnsList])
  | e :: es, g, h => by
      rw [Expr.fnsList] at h
      rcases List.mem_union_iff.mp h with h | h
      · obtain ⟨k, hk⟩ := exists_ctor_of_mem_fns e h
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := exists_ctor_of_mem_fnsList es h
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_right _ hk⟩

end

mutual

/-- The variables a subapplication reads are the expression's own. -/
theorem vars_of_mem_apps : ∀ (e : Expr) {f : FnName} {args : List Expr},
    (f, args) ∈ e.apps → ∀ v ∈ Expr.varsList args, v ∈ e.vars
  | .lit _, _, _, h => absurd h (by simp [Expr.apps])
  | .var _, _, _, h => absurd h (by simp [Expr.apps])
  | .app g gargs, f, args, h => by
      rw [Expr.apps, List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ : f = g ∧ args = gargs := ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
        exact fun v hv => by rw [Expr.vars]; exact hv
      · exact fun v hv => by rw [Expr.vars]; exact varsList_of_mem_appsList gargs h v hv

@[inherit_doc vars_of_mem_apps]
theorem varsList_of_mem_appsList : ∀ (es : List Expr) {f : FnName} {args : List Expr},
    (f, args) ∈ Expr.appsList es → ∀ v ∈ Expr.varsList args, v ∈ Expr.varsList es
  | [], _, _, h => absurd h (by simp [Expr.appsList])
  | e :: es, f, args, h => by
      rw [Expr.appsList] at h
      rcases List.mem_append.mp h with h' | h'
      · exact fun v hv => by
          rw [Expr.varsList]; exact List.mem_union_iff.mpr (Or.inl (vars_of_mem_apps e h' v hv))
      · exact fun v hv => by
          rw [Expr.varsList]
          exact List.mem_union_iff.mpr (Or.inr (varsList_of_mem_appsList es h' v hv))

end

/-! ### The block a top-level action runs, merge phases included

`FDatabase.execCmdM` runs a merge phase after **each** top-level action, so the block is not
one `execActions` run but a chain of them — which costs nothing, since
`mergeSaturateF_soundTerms` is proved and neither the signature nor the environment moves
across a `set`. -/

/-- **A block of `Cmd.action`s whose actions are `set`s.** -/
theorem execProgramM_sets_soundTerms {P : Program} {sg : Signature} {src : Database}
    {d₀ : FDatabase} :
    ∀ (bs : List Action), (∀ b ∈ bs, b.IsSet) → (∀ b ∈ bs, b.UnionFree) →
      (∀ b ∈ bs, Actions.WriteLegal [b] sg) → WritesJustified src d₀ bs →
      ∀ {d D : FDatabase}, d.EncBase P sg → d.sig = d₀.sig → d.env = d₀.env →
        (∀ t ∈ d₀.terms, t ∈ d.terms) → d.SoundTerms src →
        d.execProgramM (bs.map Cmd.action) = some D →
        D.EncBase P sg ∧ D.SoundTerms src ∧ D.env = d.env ∧ (∀ t ∈ d.terms, t ∈ D.terms) := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ _ _ d D hb _ _ _ hs hrun
    rw [List.map_nil, FDatabase.execProgramM, Option.some.injEq] at hrun
    exact ⟨hrun ▸ hb, hrun ▸ hs, by rw [← hrun], fun t ht => by rw [← hrun]; exact ht⟩
  | cons b bs ih =>
    intro hset huf hwl hjust d D hb hsig henv hmono hs hrun
    rw [List.map_cons, FDatabase.execProgramM] at hrun
    obtain ⟨d₂, h₂, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    have h₂c : d.execCmdM (Cmd.action b) = some d₂ := h₂
    rw [FDatabase.execCmdM] at h₂
    obtain ⟨d₁, hact, hmerge⟩ := Option.bind_eq_some_iff.mp h₂
    have hbset : b.IsSet := hset b List.mem_cons_self
    have hwlb : b.WriteLegal d.sig := by
      rw [hb.sig]; exact ⟨(hwl b List.mem_cons_self).1.1, (hwl b List.mem_cons_self).2.1⟩
    have hs₁ : d₁.SoundTerms src :=
      execActions_soundTerms_of_sets [b] (fun _ hb' => by
          obtain rfl : _ = b := by simpa using hb'
          exact hbset)
        (hjust.mono (fun x hx => by
          obtain rfl : x = b := by simpa using hx
          exact List.mem_cons_self)) hsig henv hmono hs
        (by rw [execActions, hact, Option.bind_some]; rfl)
    have hinv₁ : d₁.Inv := hb.inv.execAction hwlb hact
    have hsig₁ : d₁.sig = sg := by rw [FDatabase.execAction_sig hact]; exact hb.sig
    have hs₂ : d₂.SoundTerms src :=
      mergeSaturateF_soundTerms mergeFuel (by rw [hsig₁]; exact hb.shape)
        (by rw [hsig₁]; exact hb.merges) hinv₁
        (execAction_noUnions (huf b List.mem_cons_self) hb.nounions hact) hs₁ hmerge
    have hb₂ : d₂.EncBase P sg :=
      hb.execCmdM (c := Cmd.action b) trivial (huf b List.mem_cons_self) trivial
        ⟨(hwl b List.mem_cons_self).1.1, (hwl b List.mem_cons_self).2.1⟩ h₂c
    have henv₂ : d₂.env = d.env := FDatabase.execCmdM_env h₂c hbset
    have hsig₂ : d₂.sig = d.sig :=
      FDatabase.execCmdM_sig_of_noDecl (c := Cmd.action b) h₂c trivial
    have hmono₂ : ∀ t ∈ d.terms, t ∈ d₂.terms := FDatabase.execCmdM_terms h₂c
    obtain ⟨hbD, hsD, henvD, hmonoD⟩ :=
      ih (fun x hx => hset x (List.mem_cons_of_mem _ hx))
        (fun x hx => huf x (List.mem_cons_of_mem _ hx))
        (fun x hx => hwl x (List.mem_cons_of_mem _ hx))
        (hjust.mono (fun x hx => List.mem_cons_of_mem _ hx)) hb₂
        (hsig₂.trans hsig) (henv₂.trans henv) (fun t ht => hmono₂ t (hmono t ht)) hs₂ hrest
    exact ⟨hbD, hsD, henvD.trans henv₂, fun t ht => hmonoD t (hmono₂ t ht)⟩


/-- A source name is no entry head: it is not in the generated namespace. -/
theorem notEntryHead_of_mem_ctors {P : Program} (hdom : P.EncodeDomain) {fk : FnName × Nat}
    (h : fk ∈ P.ctors) : NotEntryHead fk.1 :=
  ⟨fun g hg => noAt_of_mem_ctors hdom h (hg ▸ isPrefixOf_at_viewName g),
    fun hg => noAt_of_mem_ctors hdom h
      (hg ▸ (by decide +kernel : "@".isPrefixOf ufName = true))⟩

/-- The two conditions `encodeBuild_writesJustified` asks of an expression's heads, from the
domain. -/
theorem head_conditions_of_ctors {P : Program} (hdom : P.EncodeDomain) {e : Expr}
    (hc : ∀ fk ∈ e.ctors, fk ∈ P.ctors) :
    (∀ g ∈ e.fns, NotEntryHead g) ∧ ∀ g ∈ e.fns, Prim.ofName g = none := by
  constructor <;>
  · intro g hg
    obtain ⟨k, hk⟩ := exists_ctor_of_mem_fns e hg
    first
    | exact notEntryHead_of_mem_ctors (fk := (g, k)) hdom (hc _ hk)
    | exact hdom.noPrim (g, k) (hc _ hk)

/-- **`hheld` for a top-level action.** The source's own evaluation built the value, and
`Database.addTerm` recorded every subterm, so each subapplication's value is one the
post-state holds. The target computes the same values: `encodeBuild_fst` says the encoded
expression *is* the source expression, and `Database.GlobalsAgree` plus the source's own
success make the two environments agree on everything it reads. -/
theorem held_of_evalAction {P : Program} (hdom : P.EncodeDomain) {sd sd' : Database}
    {d : FDatabase} (hwf' : sd'.WF) (e : Expr)
    (hglob : ∀ v ∈ e.vars, ∀ u, Env.lookup v sd.env = some u → Env.lookup v d.env = some u)
    (hc : ∀ fk ∈ e.ctors, fk ∈ P.ctors)
    {t : Term} (hev : e.eval sd.sig sd.env = some t) (hmem : t ∈ sd'.terms) :
    ∀ (f : FnName) (args : List Expr), (f, args) ∈ e.apps → ∀ is,
      Expr.evalList d.sig args d.env = some is → Term.app f is ∈ sd'.terms := by
  obtain ⟨-, hprim⟩ := head_conditions_of_ctors hdom hc
  obtain ⟨hbound, hctor⟩ := bound_ctor_of_eval e hprim hev
  intro f args hfa is histgt
  have hfns : ∀ g ∈ Expr.fnsList args, g ∈ e.fns := (fns_of_mem_apps e hfa).2
  have hlk : ∀ v ∈ Expr.varsList args, Env.lookup v d.env = Env.lookup v sd.env := by
    intro v hv
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hbound v (vars_of_mem_apps e hfa v hv))
    rw [hu, hglob v (vars_of_mem_apps e hfa v hv) u hu]
  have hsrcList : Expr.evalList sd.sig args sd.env = some is :=
    Expr.evalList_transport args (fun g hg _ => hctor g (hfns g hg)) hlk histgt
  obtain ⟨is', his', hsub⟩ := exists_subterm_of_mem_apps e hprim hev f args hfa
  obtain rfl : is' = is := Option.some.inj (his'.symm.trans hsrcList)
  exact hwf'.subtermClosed t hmem hsub

/-- **The target evaluates a source expression to the source's own value.** `encodeBuild`
hands the expression back unchanged, so the only gap is the two environments, and
`Database.GlobalsAgree` closes it wherever the source's evaluation succeeded. -/
theorem eval_target_of_source {P : Program} (hdom : P.EncodeDomain) {sd : Database}
    {d : FDatabase} (e : Expr)
    (hglob : ∀ v ∈ e.vars, ∀ u, Env.lookup v sd.env = some u → Env.lookup v d.env = some u)
    (hc : ∀ fk ∈ e.ctors, fk ∈ P.ctors) {t t' : Term}
    (hsrc : e.eval sd.sig sd.env = some t) (htgt : e.eval d.sig d.env = some t') : t = t' := by
  obtain ⟨-, hprim⟩ := head_conditions_of_ctors hdom hc
  obtain ⟨hbound, hctor⟩ := bound_ctor_of_eval e hprim hsrc
  have hlk : ∀ v ∈ e.vars, Env.lookup v d.env = Env.lookup v sd.env := by
    intro v hv
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hbound v hv)
    rw [hu, hglob v hv u hu]
  exact Option.some.inj (hsrc.symm.trans
    (Expr.eval_transport e (fun g hg _ => hctor g hg) hlk htgt))


/-! ### The top-level action case, discharged

`encodeAction` has three shapes to answer for at top level — a build, a build with a `let`
after it, and two builds with an `@UF` edge after them. A source `set` is out of the fragment
(`EncodeDomain.setLegal` under `ctorsOnly`). The build's own writes are
`encodeBuild_writesJustified`; the `let` writes a term whose entry-shaped subterms the block
already recorded, and re-establishes the globals; the edge is `cong_of_eqs` at the pair the
source's own `union` asserted, in whichever order `ordering-max` picked. -/

/-- One action of an encoded block, on its own. -/
private theorem writeLegal_singleton {sg : Signature} : ∀ (bs : List Action),
    Actions.WriteLegal bs sg → ∀ x ∈ bs, Actions.WriteLegal [x] sg
  | [], _, _, hx => absurd hx (by simp)
  | y :: ys, hy, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨⟨hy.1.1, trivial⟩, hy.2.1, trivial⟩
      · exact writeLegal_singleton ys ⟨hy.1.2, hy.2.2⟩ x hx'

/-- **`EncodedActionSound`, proved.** -/
theorem encodedActionSound {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree) :
    EncodedActionSound P (encodeSig P) := by
  intro pre q a hP sd sd' hpre hstep n d D hok hblock hbD
  have hcP : Cmd.action a ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
  have hctors : ∀ fk ∈ a.ctors, fk ∈ P.ctors := fun fk hfk => mem_ctors_of_cmd hcP hfk
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  have hev : evalAction sd a = some sd' := cmdStep_action_eq hstate.sig hstep
  have hwf' : sd'.WF := hstep.wf hstate.wf
  have hsc : d.SubtermClosed := hok.base.subtermClosed
  have henvm : ∀ b ∈ d.env, b.2 ∈ d.terms := fun b hb =>
    FDatabase.mem_toDatabase_terms.mp (hok.base.inv.wf.envInTerms b hb)
  have hnoset : ∀ c ∈ P, c.NoSet :=
    (Program.setLegal_iff_noSet (fun _ => rfl) hdom.ctorsOnly).mp hdom.setLegal
  have hufb : ∀ b ∈ (encodeAction fiatE a n).1, b.UnionFree :=
    fun b hb => encodeAction_unionFree fiatE a n b hb
  have hwlb : ∀ b ∈ (encodeAction fiatE a n).1, Actions.WriteLegal [b] (encodeSig P) :=
    writeLegal_singleton _ (writeLegal_encodeAction hdom hag fiatE a n (hnoset _ hcP) hctors)
  have hsound' : d.SoundTerms sd' := hok.sound.mono_src (CmdStep.contained hstep).eqs
  have hDsrc : ∀ r ∈ D.rules,
      (∃ (s : Rule) (i n : Nat), Cmd.rule s ∈ P ∧ s ∈ sd'.rules ∧ r = (encodeRule i s n).1) ∨
        r ∈ maintenanceRules P := by
    intro r hr
    refine (hok.srcRules r ((execProgramM_rules_of_declOrRule hblock r hr).resolve_left ?_)).imp
      (fun ⟨s, i, m, hm, hs, he⟩ => ⟨s, i, m, hm, cmdStep_rules_subset hstep s hs, he⟩) id
    intro hc
    obtain ⟨b, -, hb⟩ := List.mem_map.mp hc
    exact absurd hb (by simp)
  rcases evalAction_eq_some hev with ⟨e, t, rfl, hsrcev, hsd'⟩ | ⟨v, e, t, rfl, hsrcev, hsd'⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, hsrc₁, hsrc₂, -, hsd'⟩ | ⟨f, args, out, as, vs, rfl, -, -, -⟩
  · -- `.expr e`
    obtain ⟨hne, hprim⟩ := head_conditions_of_ctors hdom hctors
    have hmemt : t ∈ sd'.terms := by
      rw [hsd', Database.addTerm_terms]; exact Or.inr (Term.self_mem_subterms t)
    have hjust := encodeBuild_writesJustified hwf' hsc henvm e n hne hprim
      (held_of_evalAction hdom hwf' e (fun v _ u hu => hok.glob v u hu) hctors hsrcev hmemt)
    obtain ⟨-, hsD, henvD, -⟩ :=
      execProgramM_sets_soundTerms (encodeBuild e n).2.1 (encodeBuild_isSet e n) hufb hwlb
        hjust hok.base rfl rfl (fun _ ht => ht) hsound' hblock
    refine ⟨hbD, fun w u hu => ?_, hsD, hDsrc⟩
    rw [henvD]
    exact hok.glob w u (by rw [hsd'] at hu; exact hu)
  · -- `.letBind v e`
    obtain ⟨hne, hprim⟩ := head_conditions_of_ctors hdom hctors
    have hmemt : t ∈ sd'.terms := by
      rw [hsd', Database.terms_setEnvRules, Database.addTerm_terms]
      exact Or.inr (Term.self_mem_subterms t)
    have hjust := encodeBuild_writesJustified hwf' hsc henvm e n hne hprim
      (held_of_evalAction hdom hwf' e (fun v _ u hu => hok.glob v u hu) hctors hsrcev hmemt)
    have hsplit : ((encodeAction fiatE (Action.letBind v e) n).1).map Cmd.action
        = ((encodeBuild e n).2.1).map Cmd.action ++ [Cmd.action (.letBind v e)] := by
      rw [encodeAction_letBind_actions, encodeBuild_fst, List.map_append, List.map_cons,
        List.map_nil]
    rw [hsplit] at hblock
    obtain ⟨D₁, hb₁, hafter⟩ := FDatabase.execProgramM_append hblock
    obtain ⟨hbD₁, hsD₁, henvD₁, hmonoD₁⟩ :=
      execProgramM_sets_soundTerms (encodeBuild e n).2.1 (encodeBuild_isSet e n)
        (fun b hb => hufb b (by rw [encodeAction_letBind_actions]; exact List.mem_append_left _ hb))
        (fun b hb => hwlb b (by
          rw [encodeAction_letBind_actions]; exact List.mem_append_left _ hb))
        hjust hok.base rfl rfl (fun _ ht => ht) hsound' hb₁
    have hlast : D₁.execCmdM (Cmd.action (.letBind v e)) = some D := execProgramM_single hafter
    rw [FDatabase.execCmdM] at hlast
    obtain ⟨D₂, hact, hmerge⟩ := Option.bind_eq_some_iff.mp hlast
    obtain ⟨t', htgtev, hD₂⟩ : ∃ t', e.eval D₁.sig D₁.env = some t' ∧
        D₂ = { D₁.addTerm t' with env := (v, t') :: D₁.env } := by
      rw [execAction] at hact
      obtain ⟨t', ht', hD₂'⟩ := Option.map_eq_some_iff.mp hact
      exact ⟨t', ht', hD₂'.symm⟩
    obtain rfl : t = t' := eval_target_of_source hdom e
      (fun w _ u hu => by rw [henvD₁]; exact hok.glob w u hu) hctors hsrcev htgtev
    have hent : ∀ s ∈ t.subtermList, s.EntryShaped → s ∈ D₁.terms :=
      entryShaped_mem_of_eval e hne (fun w _ u hu =>
        entryShaped_mem_of_held hbD₁.subtermClosed (FDatabase.mem_toDatabase_terms.mp
          (hbD₁.inv.wf.envInTerms (w, u) (Env.mem_of_lookup hu)))) htgtev
    have hs₂ : D₂.SoundTerms sd' := by
      rw [hD₂]
      refine FDatabase.SoundTerms.mono_terms (fun x hx => hx)
        (hsD₁.addTerm (fun g cs x pf hm => ?_) (fun x p pf hm => ?_))
      · exact hsD₁.1 g cs x pf (hent _ hm (Or.inl ⟨g, cs, x, pf, rfl⟩))
      · exact hsD₁.2 x p pf (hent _ hm (Or.inr ⟨x, p, pf, rfl⟩))
    have hinv₂ : D₂.Inv :=
      hbD₁.inv.execAction (a := Action.letBind v e)
        (by rw [hbD₁.sig]; exact ⟨trivial, trivial⟩) hact
    have hsig₂ : D₂.sig = encodeSig P := by
      rw [FDatabase.execAction_sig hact]; exact hbD₁.sig
    have hsD : D.SoundTerms sd' :=
      mergeSaturateF_soundTerms mergeFuel (by rw [hsig₂]; exact hbD₁.shape)
        (by rw [hsig₂]; exact hbD₁.merges) hinv₂
        (execAction_noUnions (a := Action.letBind v e) trivial hbD₁.nounions hact) hs₂ hmerge
    refine ⟨hbD, ?_, hsD, hDsrc⟩
    intro w u hu
    rw [(FDatabase.mergeSaturateF_fields hmerge).2.1, hD₂]
    change Env.lookup w ((v, t) :: D₁.env) = some u
    rw [henvD₁]
    have hu' : Env.lookup w ((v, t) :: sd.env) = some u := by rw [hsd'] at hu; exact hu
    rw [Env.lookup_cons] at hu'
    rw [Env.lookup_cons]
    by_cases hwv : w = v
    · rw [if_pos hwv] at hu' ⊢; exact hu'
    · rw [if_neg hwv] at hu' ⊢; exact hok.glob w u hu'
  · -- `.union e₁ e₂`
    have hc₁ : ∀ fk ∈ e₁.ctors, fk ∈ P.ctors :=
      fun fk hfk => hctors fk (by rw [Action.ctors]; exact List.mem_append_left _ hfk)
    have hc₂ : ∀ fk ∈ e₂.ctors, fk ∈ P.ctors :=
      fun fk hfk => hctors fk (by rw [Action.ctors]; exact List.mem_append_right _ hfk)
    obtain ⟨hne₁, hprim₁⟩ := head_conditions_of_ctors hdom hc₁
    obtain ⟨hne₂, hprim₂⟩ := head_conditions_of_ctors hdom hc₂
    have hm₁ : t₁ ∈ sd'.terms := by
      rw [hsd', Database.addEq_terms]; exact Or.inl (Or.inr (Term.self_mem_subterms t₁))
    have hm₂ : t₂ ∈ sd'.terms := by
      rw [hsd', Database.addEq_terms]; exact Or.inr (Term.self_mem_subterms t₂)
    have heq : (t₁, t₂) ∈ sd'.eqs := by
      rw [hsd', Database.addEq_eqs]; exact Set.mem_insert _ _
    have hbind : ∀ (w : Var), ∀ u, Env.lookup w d.env = some u →
        ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms :=
      fun w u hu => entryShaped_mem_of_held hsc (henvm (w, u) (Env.mem_of_lookup hu))
    have hjust₁ := encodeBuild_writesJustified hwf' hsc henvm e₁ n hne₁ hprim₁
      (held_of_evalAction hdom hwf' e₁ (fun v _ u hu => hok.glob v u hu) hc₁ hsrc₁ hm₁)
    have hjust₂ := encodeBuild_writesJustified hwf' hsc henvm e₂ (encodeBuild e₁ n).2.2
      hne₂ hprim₂ (held_of_evalAction hdom hwf' e₂ (fun v _ u hu => hok.glob v u hu) hc₂ hsrc₂ hm₂)
    have hjust₃ : WritesJustified sd' d
        [Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]] := by
      intro g args out hmem is vs has hvs
      have hme : Action.set g args out
          = Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE] := by simpa using hmem
      injection hme with hg ha ho
      subst hg; subst ha; subst ho
      obtain ⟨mx, hmx, rfl⟩ := Expr.evalList_single has
      obtain ⟨mn, pfv, hmn, hpf, rfl⟩ := Expr.evalList_pair hvs
      have hval : ∀ {z : Term}, e₁.eval d.sig d.env = some z ∨ e₂.eval d.sig d.env = some z →
          z = t₁ ∨ z = t₂ := by
        rintro z (hz | hz)
        · exact Or.inl (eval_target_of_source hdom e₁
            (fun w _ u hu => hok.glob w u hu) hc₁ hsrc₁ hz).symm
        · exact Or.inr (eval_target_of_source hdom e₂
            (fun w _ u hu => hok.glob w u hu) hc₂ hsrc₂ hz).symm
      have hsubx : ∀ {z : Term},
          e₁.eval d.sig d.env = some z ∨ e₂.eval d.sig d.env = some z →
          ∀ s ∈ z.subtermList, s.EntryShaped → s ∈ d.terms := by
        rintro z (hz | hz)
        · exact entryShaped_mem_of_eval e₁ hne₁ (fun w _ => hbind w) hz
        · exact entryShaped_mem_of_eval e₂ hne₂ (fun w _ => hbind w) hz
      refine ⟨fun c hc s hsm hshaped => ?_, fun f' cs x pf hq => ?_, fun x p pf hq => ?_⟩
      · have hc2 : c = mx ∨ c = mn ∨ c = pfv := by simpa using hc
        rcases hc2 with rfl | rfl | rfl
        · exact hsubx (eval_ifGt_inv hmx) s hsm hshaped
        · exact hsubx (Or.symm (eval_ifGt_inv hmn)) s hsm hshaped
        · refine entryShaped_mem_of_eval fiatE (fun y hy => ?_) (fun w _ => hbind w) hpf
            s hsm hshaped
          obtain rfl : y = fiatName := by simpa [fiatE, Expr.fns, Expr.fnsList] using hy
          exact notEntryHead_fiatName
      · exact absurd (Term.app.inj hq).1 (fun hz => viewName_ne_ufName hz.symm)
      · obtain ⟨-, hcols⟩ := Term.app.inj hq
        have h3 : [mx, mn, pfv] = [x, p, pf] := hcols
        obtain rfl : mx = x := (List.cons.inj h3).1
        obtain rfl : mn = p := (List.cons.inj (List.cons.inj h3).2).1
        rcases hval (eval_ifGt_inv hmx) with rfl | rfl <;>
          rcases hval (Or.symm (eval_ifGt_inv hmn)) with rfl | rfl
        · exact Cong.assert (hwf'.eqsRefl _ hm₁)
        · exact Cong.assert heq
        · exact (Cong.assert heq).symm
        · exact Cong.assert (hwf'.eqsRefl _ hm₂)
    have hjust : WritesJustified sd' d (encodeAction fiatE (.union e₁ e₂) n).1 := by
      rw [encodeAction_union_actions, encodeBuild_fst, encodeBuild_fst]
      exact (hjust₁.append hjust₂).append hjust₃
    have hset : ∀ b ∈ (encodeAction fiatE (.union e₁ e₂) n).1, b.IsSet := by
      intro b hb
      rw [encodeAction_union_actions] at hb
      rcases List.mem_append.mp hb with hb' | hb'
      · rcases List.mem_append.mp hb' with hb'' | hb''
        · exact encodeBuild_isSet e₁ n b hb''
        · exact encodeBuild_isSet e₂ _ b hb''
      · obtain rfl : b = Action.set ufName [maxE (encodeBuild e₁ n).1
            (encodeBuild e₂ (encodeBuild e₁ n).2.2).1]
            [minE (encodeBuild e₁ n).1 (encodeBuild e₂ (encodeBuild e₁ n).2.2).1, fiatE] := by
          simpa using hb'
        trivial
    obtain ⟨-, hsD, henvD, -⟩ :=
      execProgramM_sets_soundTerms _ hset hufb hwlb hjust hok.base rfl rfl (fun _ ht => ht)
        hsound' hblock
    refine ⟨hbD, fun w u hu => ?_, hsD, hDsrc⟩
    rw [henvD]
    exact hok.glob w u (by rw [hsd'] at hu; exact hu)
  · -- a source `set` is out of the fragment
    exact absurd (hnoset _ hcP) (fun h => (h : False))


/-- **The residue, reduced to one firing and one missing clause.**

`execM_soundTerms_of_firings` with `EncodedActionSound` discharged, so what is left of the
completeness half is:

* `EncodedHeadSound` — one firing of one encoded **source rule**, which is
  `entrySound_headBuild_post` and `cong_headUnion_post` at the writes `encodeActions` emits.
  The block read-back it needs is here already (`encodeBuild_writesJustified`,
  `execActions_soundTerms_of_sets`) and so is the substitution
  (`validQuerySubst_of_mem_matchQuery_diag`); what is missing is the source-side reading at
  a rule's *nested* applications — `entrySound_headBuild_post` fixes the reading τ per
  application and a head's subapplications have to share it — together with `Rule.HeadScoped`
  and `hlet`.
* `Program.AritiesAgree` — a clause `Program.EncodeDomain` does not have, whose necessity
  `adProgram_not_maintenance_writeLegal` records.

Everything else is proved. -/
theorem execM_soundTerms_of_head {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    (hhead : EncodedHeadSound P (encodeSig P))
    {src : Database} (hsrc : ProgramStep Database.empty P src)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src :=
  execM_soundTerms_of_firings hdom hag hhead (encodedActionSound hdom hag) hsrc htgt


/-- **`FDatabase.EncOk` is inhabited**, at the state the prelude of any in-domain program
whose arities agree leaves. Both legality conditions are discharged here, so this asks
nothing beyond the domain and the missing clause. -/
theorem encOk_preludeState {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {d₀ : FDatabase} (hprel : FDatabase.empty.execProgramM (encodePrelude P) = some d₀) :
    d₀.EncOk P (encodeSig P) Database.empty :=
  preludeState_encOk (encodeSig_mergesLegal hdom) (maintenance_writeLegal hdom hag) hprel

/-! ### And at a program, concretely

`ENCODING.md`'s discipline for the bundle the induction carries: `wProgram` is
`Encoding/Match.lean`'s witness program, its prelude **runs in the kernel** — it is
declarations and rules, so none of the irreducible machinery is reached — and the state it
leaves satisfies every field. -/

/-- The state `encode wProgram`'s prelude leaves. -/
def wPreludeState : FDatabase :=
  (FDatabase.empty.execProgramM (encodePrelude wProgram)).getD FDatabase.empty

theorem wPreludeState_eq :
    FDatabase.empty.execProgramM (encodePrelude wProgram) = some wPreludeState := rfl

/-- `wProgram` mentions `F` at one arity and `A` at one arity. -/
theorem wProgram_aritiesAgree : wProgram.AritiesAgree := by
  change ∀ fk ∈ wProgram.ctors, ∀ gl ∈ wProgram.ctors, fk.1 = gl.1 → fk.2 = gl.2
  decide +kernel

/-- **The bundle, at a state a real encoded program reaches.** -/
theorem wPreludeState_encOk :
    wPreludeState.EncOk wProgram (encodeSig wProgram) Database.empty :=
  encOk_preludeState wProgram_encodeDomain wProgram_aritiesAgree wPreludeState_eq

/-! ### The clause is needed, at a program every *other* clause admits

`ENCODING.md`'s discipline for a clause as much as for a lemma: a condition that nothing
violates is not a condition. `adProgram` is two commands, it satisfies every other clause of
`Program.EncodeDomain`, and it applies `F` at **two** arities — the declaration's nullary one
and the unary one its own action uses. `Program.ctors` records both, `encodePrelude` emits two
table triples for `F`, and the later one wins: `@FView` ends up declared **nullary** while the
rebuild rules of the unary entry key it at one column. `Actions.SetWidthOk` refuses that, and
it is what `FDatabase.Inv.execCmdM` asks of every rule the state holds. -/

/-- Two commands, in the domain, applying `F` at two arities. -/
def adProgram : Program :=
  [.decl "F" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.app "F" [.app "F" []]))]

/-- The rebuild rule the widths part company at: the e-class rule of `F`'s **unary** entry,
whose key is one column wide. -/
def adBadRule : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName "F") (rebuildVars 1),
              .values [.var "@x", .var "@q"] ufName [.var "@e"]],
    actions := [.set (viewName "F") (rebuildVars 1)
      [.var "@x", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

theorem adBadRule_mem : adBadRule ∈ maintenanceRules adProgram := by
  have h : maintenanceRules adProgram
      = pathCompressRule :: (rebuildRules "F" 1 ++ rebuildRules "F" 0) := rfl
  rw [h]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)

/-- **`aritiesAgree` is the clause it fails**, and it is the only one. -/
theorem adProgram_not_aritiesAgree : ¬ adProgram.AritiesAgree := by
  intro h
  have h1 : (("F", 1) : FnName × Nat) ∈ adProgram.ctors := by decide
  have h2 : (("F", 0) : FnName × Nat) ∈ adProgram.ctors := by decide
  exact absurd (h _ h1 _ h2 rfl) (by decide)

theorem adProgram_not_encodeDomain : ¬ adProgram.EncodeDomain :=
  fun h => adProgram_not_aritiesAgree h.aritiesAgree'

/-- **And every other clause holds of it**, which is what says the new clause is not
decoration: it is the only thing standing between the domain and the false obligation
below. -/
theorem adProgram_encodeDomain_but_arities :
    adProgram.CtorDecls ∧ Program.SetLegal adProgram (fun _ => none) ∧
      (∀ fk ∈ adProgram.ctors, Prim.ofName fk.1 = none) ∧
      (∀ n ∈ adProgram.names, ¬ "@".isPrefixOf n) ∧
      (∀ c ∈ adProgram, c.QueryEncodable) ∧
      (∀ c ∈ adProgram, c.ruleUnionFreeB = true) ∧
      Program.HeadsDeclared adProgram (fun _ => none) ∧ adProgram.HeadsScoped := by
  refine ⟨?_, by decide, by decide, by decide +kernel, ?_, by decide, by decide, by decide⟩
  · intro c hc
    simp only [adProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  · intro c hc
    simp only [adProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | h
    · trivial
    · trivial
    · exact absurd h (by simp)

/-- **The obligation is false there.** `encodeSig adProgram (viewName "F")` is `viewDecl 0`
and the rule keys at one column, so `Actions.SetWidthOk` fails — and with it
`FDatabase.EncBase`'s `wl`, hence `FDatabase.Inv` at every state after the rebuild.

Compiled, and with no `sorry` anywhere under it: this is why `EncodeDomain.aritiesAgree` is
a clause. -/
theorem adProgram_not_maintenance_writeLegal :
    ¬ ∀ r ∈ maintenanceRules adProgram, Actions.WriteLegal r.actions (encodeSig adProgram) := by
  intro h
  have hsig : encodeSig adProgram (viewName "F") = some (viewDecl 0) := rfl
  have hone := ((h adBadRule adBadRule_mem).2.1 (viewDecl 0) hsig).1
  simp [rebuildVars, viewDecl] at hone

/-! ## `Database.TermsBuild` along the source run

`entrySound_headBuild_post` asks it of the state a firing reads at, and nothing established
it. It is **spec-side** work — an induction through `evalAction`, `RunRules` and
`ProgramStep`, with no `encode` in it — but it cannot live in `Proofs/`: `Database.TermsBuild`
is declared in `Encoding/Match.lean` and the primitive case needs
`Encoding/Correspond.lean`'s `prim_apply_cases`, so `Proofs/` cannot even state it. It is
here rather than in `Encoding/Match.lean` because this is its only consumer.

The shape is `Database.NoLits`': one term-level notion, one lemma per writer, one per
command, one for the run. It is *cheaper* than that one, because no clause on the program's
text is needed: a **primitive** answers with a literal or with one of its own operands
(`prim_apply_cases`), so a head applying one adds no application the invariant has to
account for. What is needed is `Program.CtorDecls`, because a `:merge` declaration would take
`Signature.IsCtor` away at a name the state's terms already apply. -/

/-- Every application in `t` is a declared constructor's, applied. The term-level form of
`Database.TermsBuild`. -/
def Term.CtorApps (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → Prim.ofName f = none ∧ sig.IsCtor f

theorem Term.CtorApps.lit {sig : Signature} {l : Lit} : Term.CtorApps sig (.lit l) := by
  intro f as h
  rw [Term.subterms_lit, Set.mem_singleton_iff] at h
  exact absurd h (by simp)

theorem Term.ctorApps_app {sig : Signature} {f : FnName} {args : List Term}
    (hf : Prim.ofName f = none) (hc : sig.IsCtor f) (ha : ∀ a ∈ args, Term.CtorApps sig a) :
    Term.CtorApps sig (.app f args) := by
  intro g as h
  rw [Term.subterms_app, Set.mem_insert_iff] at h
  rcases h with h | h
  · obtain ⟨rfl, -⟩ := Term.app.inj h
    exact ⟨hf, hc⟩
  · obtain ⟨a, ha', hs⟩ := by simpa using h
    exact ha a ha' g as hs

/-- Declaring a constructor keeps every application a constructor's. -/
theorem Term.CtorApps.update {sig : Signature} {f : FnName} {dc : FnDecl} (hd : dc.merge = none)
    {t : Term} (h : Term.CtorApps sig t) :
    Term.CtorApps (Function.update sig f (some dc)) t :=
  fun g as hg => ⟨(h g as hg).1, Signature.IsCtor.update hd (h g as hg).2⟩

mutual

/-- **A successful evaluation builds a term whose applications are all constructors'**, in
an environment whose bindings are. The primitive branch costs nothing: `prim_apply_cases`
says the answer is a literal or one of the operands. -/
theorem Expr.eval_ctorApps {sig : Signature} {ρ : Env}
    (hρ : ∀ v u, Env.lookup v ρ = some u → Term.CtorApps sig u) :
    ∀ (e : Expr) {t : Term}, e.eval sig ρ = some t → Term.CtorApps sig t
  | .lit _, _, h => by
      obtain rfl : _ = _ := Option.some.inj h
      exact Term.CtorApps.lit
  | .var v, t, h => hρ v t h
  | .app f args, t, h => by
      cases hp : Prim.ofName f with
      | some p =>
          rw [Expr.eval_app_prim hp, Option.bind_eq_some_iff] at h
          obtain ⟨ts, hts, hap⟩ := h
          have hall := Expr.evalList_ctorApps hρ args hts
          rcases prim_apply_cases hap with ⟨l, rfl⟩ | hmem
          · exact Term.CtorApps.lit
          · exact hall t hmem
      | none =>
          have hct : sig.IsCtor f := by
            by_contra hc
            rw [Expr.eval_app_not_ctor hp hc] at h
            exact absurd h (by simp)
          rw [Expr.eval_app_ctor hp hct] at h
          obtain ⟨is, his, rfl⟩ := Option.map_eq_some_iff.mp h
          exact Term.ctorApps_app hp hct (Expr.evalList_ctorApps hρ args his)

@[inherit_doc Expr.eval_ctorApps]
theorem Expr.evalList_ctorApps {sig : Signature} {ρ : Env}
    (hρ : ∀ v u, Env.lookup v ρ = some u → Term.CtorApps sig u) :
    ∀ (es : List Expr) {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ t ∈ ts, Term.CtorApps sig t
  | [], _, h => by
      obtain rfl : _ = _ := Option.some.inj h
      simp
  | e :: es, ts, h => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, hrest⟩ := h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_ctorApps hρ e hu
      · exact Expr.evalList_ctorApps hρ es hus t ht'

end

/-- The state's own terms, read at the term level. -/
theorem Database.TermsBuild.term {db : Database} (hw : db.WF) (h : db.TermsBuild) {t : Term}
    (ht : t ∈ db.terms) : Term.CtorApps db.sig t :=
  fun f as hs => h f as (hw.subtermClosed t ht hs)

theorem Database.TermsBuild.lookup {db : Database} (hw : db.WF) (h : db.TermsBuild) :
    ∀ v t, Env.lookup v db.env = some t → Term.CtorApps db.sig t := fun v t hv =>
  h.term hw (hw.envInTerms (v, t) (Env.mem_of_lookup hv))

theorem Database.empty_termsBuild : Database.empty.TermsBuild := by
  intro f as h; exact absurd h (by simp)

/-- Any state whose terms are all `Term.CtorApps` satisfies the clause. -/
theorem Database.termsBuild_of_terms {db : Database}
    (h : ∀ t ∈ db.terms, Term.CtorApps db.sig t) : db.TermsBuild :=
  fun f as hm => h _ hm f as (Term.self_mem_subterms _)

/-- **One `set`-free action keeps it.** Every writer is then an `addTerm` or an `addEq` of a
value `Expr.eval_ctorApps` covers. A `set` is the one action that writes an application of a
name the signature does **not** make a constructor — that is what an entry term is — and it
is out of the fragment (`EncodeDomain.setLegal` under `ctorsOnly`). -/
theorem evalAction_termsBuild {db db' : Database} (hw : db.WF) (h : db.TermsBuild)
    {a : Action} (hns : a.NoSet) (hv : evalAction db a = some db') : db'.TermsBuild := by
  have hlk := h.lookup hw
  have hbase : ∀ t ∈ db.terms, Term.CtorApps db.sig t := fun t ht => h.term hw ht
  rcases evalAction_eq_some hv with ⟨e, t, rfl, he, rfl⟩ | ⟨v, e, t, rfl, he, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, he₁, he₂, -, rfl⟩ | ⟨f, args, out, as, vs, rfl, -, -, -⟩
  · refine Database.termsBuild_of_terms fun s hs => ?_
    rw [Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact hbase s hs'
    · exact fun g gs hg => Expr.eval_ctorApps hlk e he g gs (Term.subterms_subset_of_mem hs' hg)
  · refine Database.termsBuild_of_terms fun s hs => ?_
    rw [Database.terms_setEnv, Database.addTerm_terms] at hs
    rcases hs with hs' | hs'
    · exact hbase s hs'
    · exact fun g gs hg => Expr.eval_ctorApps hlk e he g gs (Term.subterms_subset_of_mem hs' hg)
  · refine Database.termsBuild_of_terms fun s hs => ?_
    rw [Database.addEq_terms] at hs
    rcases hs with hs' | hs'
    · rcases hs' with hs'' | hs''
      · exact hbase s hs''
      · exact fun g gs hg =>
          Expr.eval_ctorApps hlk e₁ he₁ g gs (Term.subterms_subset_of_mem hs'' hg)
    · exact fun g gs hg =>
        Expr.eval_ctorApps hlk e₂ he₂ g gs (Term.subterms_subset_of_mem hs' hg)
  · exact absurd hns (fun hc => (hc : False))

theorem evalActions_termsBuild {db db' : Database} (hw : db.WF) (h : db.TermsBuild)
    {as : List Action} (hns : ∀ a ∈ as, a.NoSet)
    (hv : evalActions db as = some db') : db'.TermsBuild := by
  induction as generalizing db with
  | nil =>
      rw [evalActions_nil, Option.some_inj] at hv
      exact hv ▸ h
  | cons a as ih =>
      rw [evalActions_cons, Option.bind_eq_some_iff] at hv
      obtain ⟨d, hd, hrest⟩ := hv
      exact ih (evalAction_wf hw hd)
        (evalAction_termsBuild hw h (hns a List.mem_cons_self) hd)
        (fun b hb => hns b (List.mem_cons_of_mem _ hb)) hrest

theorem evalLocalActions_termsBuild {db db' : Database} (hw : db.WF) (h : db.TermsBuild)
    {as : List Action} (hns : ∀ a ∈ as, a.NoSet) {σ : Env} (hσ : ∀ b ∈ σ, b.2 ∈ db.terms)
    (hv : evalLocalActions db as σ = some db') : db'.TermsBuild := by
  obtain ⟨d, hd, rfl⟩ := evalLocalActions_eq_some hv
  have hlf : ({ db with env := db.env ++ σ } : Database).TermsBuild := by
    intro f q ht; exact h f q (Database.terms_setEnv ▸ ht)
  intro f q ht
  rw [Database.terms_setEnvRules] at ht
  exact evalActions_termsBuild (hw.appendEnv hσ) hlf hns hd f q ht

/-- **The invariant a run carries**: the data clause, and the head clause the rule-firing
case needs — a firing runs a head the *state* holds, not one the command names. The shape is
`Database.NoLits`'. -/
structure Database.TermsBuilds (db : Database) : Prop where
  /-- Every application the state holds is a declared constructor's. -/
  terms : db.TermsBuild
  /-- No rule the state holds writes an entry. -/
  heads : ∀ r ∈ db.rules, ∀ a ∈ r.actions, a.NoSet

theorem Database.empty_termsBuilds : Database.empty.TermsBuilds where
  terms := Database.empty_termsBuild
  heads := by intro r hr; exact absurd hr (by simp [Database.empty])

/-- **A round keeps it.** `RunRules` is a `Database.sUnion` over the firings, each of which is
an `evalLocalActions` of a head the state carries. -/
theorem Database.TermsBuilds.runRules {R : RulesetName} {db : Database} (hw : db.WF)
    (h : db.TermsBuilds) : (RunRules R db).TermsBuilds := by
  refine ⟨?_, ?_⟩
  · intro f q ht
    rw [RunRules.sig]
    rw [RunRules, Database.sUnion_terms] at ht
    rcases ht with ht' | ht'
    · exact h.terms f q ht'
    · obtain ⟨d, hd, ht''⟩ := Set.mem_iUnion₂.mp ht'
      obtain ⟨r, hr, -, σ, hq, hfire⟩ := hd
      have := evalLocalActions_termsBuild hw h.terms (h.heads r hr) hq.mem_terms hfire f q ht''
      rwa [evalLocalActions_sig hfire] at this
  · rw [RunRules, Database.sUnion_rules]; exact h.heads

theorem cmdStep_termsBuilds {db db' : Database} (hc : db.CtorState) (h : db.TermsBuilds)
    {c : Cmd} (hns : c.NoSet) (hdecl : c.CtorDecl) (hstep : CmdStep db c db') :
    db'.TermsBuilds := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  cases c with
  | action a =>
      have hv : evalAction db a = some d := hreach
      obtain rfl : db' = d :=
        hcl.eq_of_allConstructors (by rw [evalAction_sig hv]; exact hc.sig)
      exact ⟨evalAction_termsBuild hc.wf h.terms hns hv,
        by rw [evalAction_rules hv]; exact h.heads⟩
  | rule r =>
      have hv : some { db with rules := insert r db.rules } = some d := hreach
      obtain rfl : d = { db with rules := insert r db.rules } := (Option.some.inj hv).symm
      obtain rfl : db' = { db with rules := insert r db.rules } :=
        hcl.eq_of_allConstructors hc.sig
      refine ⟨fun f q ht => h.terms f q (Database.terms_setRules ▸ ht), ?_⟩
      intro r' hr'
      rcases Set.mem_insert_iff.mp hr' with rfl | hr''
      · exact hns
      · exact h.heads r' hr''
  | run R =>
      have hv : some (RunRules R db) = some d := hreach
      obtain rfl : d = RunRules R db := (Option.some.inj hv).symm
      obtain rfl : db' = RunRules R db :=
        hcl.eq_of_allConstructors (by rw [RunRules.sig]; exact hc.sig)
      exact h.runRules hc.wf
  | saturate R =>
      have hsat : SaturateReach R db db' := cmdStep_saturate_iff.mp ⟨d, hreach, hcl⟩
      refine (RunReach.induction (P := fun x => x.CtorState ∧ x.TermsBuilds) ?_ hsat.1
        ⟨hc, h⟩).2
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
      refine ⟨fun g q ht => ?_, h.heads⟩
      exact ⟨(h.terms g q (Database.terms_setSig ▸ ht)).1,
        Signature.IsCtor.update hdecl (h.terms g q (Database.terms_setSig ▸ ht)).2⟩

/-- **`Database.TermsBuild` at every state a run reaches.** Applied to a *prefix* of the
source program it is the invariant at the state a firing command reads its rows at, which is
where `entrySound_headBuild_post` spends it. -/
theorem programStep_termsBuilds {db db' : Database} (hc : db.CtorState) (h : db.TermsBuilds)
    {p : Program} (hns : ∀ c ∈ p, c.NoSet) (hdecl : p.CtorDecls)
    (hstep : ProgramStep db p db') : db'.TermsBuilds := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hstep _ ih =>
      exact ih (hstep.ctorState hc (hdecl c List.mem_cons_self))
        (cmdStep_termsBuilds hc h (hns c List.mem_cons_self) (hdecl c List.mem_cons_self) hstep)
        (fun c' hc' => hns c' (List.mem_cons_of_mem c hc'))
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-- **And from the domain**, at the state a prefix of an in-domain program reaches. -/
theorem termsBuild_of_programStep {P : Program} (hdom : P.EncodeDomain) {p q : Program}
    (hP : P = p ++ q) {sd : Database} (hstep : ProgramStep Database.empty p sd) :
    sd.TermsBuild :=
  (programStep_termsBuilds Database.CtorState.empty Database.empty_termsBuilds
    (fun c hc => (Program.setLegal_iff_noSet (fun _ => rfl) hdom.ctorsOnly).mp hdom.setLegal c
      (by rw [hP]; exact List.mem_append_left _ hc))
    (fun c hc => hdom.ctorsOnly c (by rw [hP]; exact List.mem_append_left _ hc)) hstep).terms

/-! ## One rule head, on both sides at once

`encodeActions` maps a source head action to a block of `set`s — plus, for a `let`, the same
`let` — so the encoded head is not one `execActions` of `set`s but a **chain** of chunks, one
per source action, and the `let`s move the environment inside it. The two lemmas below run the
two blocks in lockstep, one source action at a time, and that is what carries the shared `let`
prefix: the source's `let` binds `v` to the value of `e` and the encoded one to the value of
`(encodeBuild e m).1`, which *is* `e` (`encodeBuild_fst`), so the two environments extend by
the same binding and the link between them survives the step.

Nothing here is `hlet`. `mem_terms_of_headBuild`'s `hlet` exists because that lemma reads the
head at the block's **initial** environment and an action after a `letBind` runs at an extended
one; here each action is read at the environment it actually ran under. What replaces it is
`Actions.Scoped` — `Rule.HeadScoped` — which says the scope the link is carried on covers what
each action reads. -/

/-- A rule's justification is no entry head, so the proof column it writes costs the invariant
nothing. Mirrors `viewName_ne_congrName`: the fixed part of `@Rule_i` carries no `'w'`, and
`Nat.isDigit_of_mem_toDigits` says the index carries none either. -/
theorem viewName_ne_ruleName {f : FnName} {i : Nat} : viewName f ≠ ruleName i := by
  intro h
  have hw : 'w' ∈ (viewName f).toList := by
    rw [viewName, String.toList_append]
    exact List.mem_append_right _ (by decide)
  rw [h, ruleName, String.toList_append] at hw
  rcases List.mem_append.mp hw with h1 | h1
  · exact absurd h1 (by decide)
  · have hd := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
      (show 'w' ∈ Nat.toDigits 10 i by rw [Nat.toString_eq_repr, Nat.toList_repr] at h1; exact h1)
    simp at hd

@[inherit_doc viewName_ne_ruleName]
theorem ufName_ne_ruleName {i : Nat} : ufName ≠ ruleName i := by
  intro h
  have hw : 'U' ∈ ufName.toList := by rw [ufName]; decide
  rw [h, ruleName, String.toList_append] at hw
  rcases List.mem_append.mp hw with h1 | h1
  · exact absurd h1 (by decide)
  · have hd := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
      (show 'U' ∈ Nat.toDigits 10 i by rw [Nat.toString_eq_repr, Nat.toList_repr] at h1; exact h1)
    simp at hd

@[inherit_doc viewName_ne_ruleName]
theorem notEntryHead_ruleName {i : Nat} : NotEntryHead (ruleName i) :=
  ⟨fun _ h => viewName_ne_ruleName h.symm, fun h => ufName_ne_ruleName h.symm⟩


/-! ### The justification a firing writes is `@Rule_i` over variables

`encodeAction`'s `union` writes the firing's own proof into the `@UF` entry's proof column, so
the invariant has to know that column is of neither entry shape. `@Rule_i` is not, and its
arguments are the premise proofs the encoded query binds — **variables**, because every read
`encodeQueryExpr` emits binds two fresh ones. -/

/-- Every value column a read binds is a variable. Vacuous at any other pattern. -/
def Pattern.ValueVars : Pattern → Prop
  | .values vs _ _ => ∀ x ∈ vs, ∃ v, x = Expr.var v
  | _ => True

mutual

/-- The reads one source expression flattens to bind two fresh variables each. -/
theorem encodeQueryExpr_valueVars : ∀ (e : Expr) (n : Nat),
    ∀ p ∈ (encodeQueryExpr e n).2.1, p.ValueVars
  | .lit _, _, _, hp => absurd hp (by simp [encodeQueryExpr])
  | .var _, _, _, hp => absurd hp (by simp [encodeQueryExpr])
  | .app f args, n, p, hp => by
      rw [encodeQueryExpr_app_atoms] at hp
      rcases List.mem_append.mp hp with h | h
      · exact encodeQueryArgs_valueVars args n p h
      · obtain rfl : p = Pattern.values
            [.var (freshVar (encodeQueryArgs args n).2.2),
              .var (freshVar ((encodeQueryArgs args n).2.2 + 1))] (viewName f)
            (encodeQueryArgs args n).1 := by simpa using h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨_, rfl⟩
        · obtain rfl : x = Expr.var (freshVar ((encodeQueryArgs args n).2.2 + 1)) := by
            simpa using hx'
          exact ⟨_, rfl⟩

@[inherit_doc encodeQueryExpr_valueVars]
theorem encodeQueryArgs_valueVars : ∀ (es : List Expr) (n : Nat),
    ∀ p ∈ (encodeQueryArgs es n).2.1, p.ValueVars
  | [], _, _, hp => absurd hp (by simp [encodeQueryArgs])
  | e :: es, n, p, hp => by
      rw [encodeQueryArgs_cons_atoms] at hp
      rcases List.mem_append.mp hp with h | h
      · exact encodeQueryExpr_valueVars e n p h
      · exact encodeQueryArgs_valueVars es _ p h

end

@[inherit_doc encodeQueryExpr_valueVars]
theorem encodePattern_valueVars {p : Pattern} (hnv : p.NoValues) (n : Nat) :
    ∀ a ∈ (encodePattern p n).1, a.ValueVars := by
  cases p with
  | values vs f as => exact absurd hnv id
  | expr e =>
      rw [encodePattern_expr_atoms]
      exact encodeQueryExpr_valueVars e n
  | eq e₁ e₂ =>
      rw [encodePattern_eq_atoms]
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact encodeQueryExpr_valueVars e₁ n a h'
        · exact encodeQueryExpr_valueVars e₂ _ a h'
      · obtain rfl : a = Pattern.eq (encodeQueryExpr e₁ n).1
            (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1 := by simpa using h
        trivial

@[inherit_doc encodeQueryExpr_valueVars]
theorem encodeQuery_valueVars : ∀ (q : Query), (∀ p ∈ q, p.NoValues) → ∀ (n : Nat),
    ∀ a ∈ (encodeQuery q n).1, a.ValueVars
  | [], _, _, _, ha => absurd ha (by simp [encodeQuery])
  | p :: ps, hnv, n, a, ha => by
      rw [encodeQuery_cons_atoms] at ha
      rcases List.mem_append.mp ha with h | h
      · exact encodePattern_valueVars (hnv p List.mem_cons_self) n a h
      · exact encodeQuery_valueVars ps (fun p' hp' => hnv p' (List.mem_cons_of_mem _ hp')) _ a h

/-- **So the premise proofs are variables.** -/
theorem queryProofs_var {q : Query} (h : ∀ p ∈ q, p.ValueVars) :
    ∀ e ∈ queryProofs q, ∃ v, e = Expr.var v := by
  intro e he
  rw [queryProofs, List.mem_filterMap] at he
  obtain ⟨p, hp, hpe⟩ := he
  match p, hp, hpe with
  | .values [x, y] f as, hp, hpe =>
      obtain rfl : y = e := Option.some.inj hpe
      exact h _ hp _ (by simp)
  | .values [] _ _, _, hpe => exact absurd hpe (by simp)
  | .values [_] _ _, _, hpe => exact absurd hpe (by simp)
  | .values (_ :: _ :: _ :: _) _ _, _, hpe => exact absurd hpe (by simp)
  | .expr _, _, hpe => exact absurd hpe (by simp)
  | .eq _ _, _, hpe => exact absurd hpe (by simp)

/-- And `@Rule_i` over variables applies no entry head. -/
theorem notEntryHead_ruleE {i : Nat} {ps : List Expr}
    (hv : ∀ e ∈ ps, ∃ v, e = Expr.var v) : ∀ g ∈ (ruleE i ps).fns, NotEntryHead g := by
  have hnil : ∀ (es : List Expr), (∀ e ∈ es, ∃ v, e = Expr.var v) →
      Expr.fnsList es = [] := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e es ih =>
      intro hall
      obtain ⟨w, rfl⟩ := hall e List.mem_cons_self
      rw [Expr.fnsList, Expr.fns, ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
      rfl
  intro g hg
  rw [ruleE, Expr.fns, hnil ps hv, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact notEntryHead_ruleName
  · exact absurd hg (by simp)

/-- **One source head action, on both sides.** The chunk `encodeAction` emits for it preserves
the invariant, and the two environments still agree on the scope the action leaves.

`hterms₁`/`heqs₁` are what a firing's writes reaching the round's post-state buys — the source
state *after this action* is contained in the block's result and so in `sd'` — and they are the
only thing the source contributes. -/
theorem headAction_step {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {sd' : Database} (hwf' : sd'.WF) {pf : Expr} (hpfne : ∀ g ∈ pf.fns, NotEntryHead g)
    {a : Action} {Γ : Scope} {m : Nat} {ss ss₁ : Database} {dk dk₁ : FDatabase}
    (hca : ∀ fk ∈ a.ctors, fk ∈ P.ctors) (hnsa : a.NoSet) (hsca : a.Scoped Γ)
    (hlink : ∀ v ∈ Γ, Env.lookup v dk.env = Env.lookup v ss.env)
    (hsig : dk.sig = encodeSig P) (hinv : dk.Inv) (hsound : dk.SoundTerms sd')
    (hs₁ : evalAction ss a = some ss₁)
    (hterms₁ : ∀ t ∈ ss₁.terms, t ∈ sd'.terms) (heqs₁ : ∀ p ∈ ss₁.eqs, p ∈ sd'.eqs)
    (h₁ : execActions dk (encodeAction pf a m).1 = some dk₁) :
    dk₁.SoundTerms sd' ∧ ∀ v ∈ a.bind Γ, Env.lookup v dk₁.env = Env.lookup v ss₁.env := by
  have hsc : dk.SubtermClosed := FDatabase.SubtermClosed.of_wf hinv.wf
  have henvm : ∀ b ∈ dk.env, b.2 ∈ dk.terms := fun b hb =>
    FDatabase.mem_toDatabase_terms.mp (hinv.wf.envInTerms b hb)
  have hbind : ∀ (w : Var), ∀ u, Env.lookup w dk.env = some u →
      ∀ x ∈ u.subtermList, x.EntryShaped → x ∈ dk.terms :=
    fun w u hu => entryShaped_mem_of_held hsc (henvm (w, u) (Env.mem_of_lookup hu))
  rcases evalAction_eq_some hs₁ with ⟨e, t, rfl, hev, rfl⟩ | ⟨v, e, t, rfl, hev, rfl⟩ |
      ⟨e₁, e₂, t₁, t₂, rfl, hev₁, hev₂, -, rfl⟩ | ⟨f, args, out, cs, vs, rfl, -, -, -⟩
  · -- `.expr e`: the build's own block, all `set`s
    have hce : ∀ fk ∈ e.ctors, fk ∈ P.ctors := hca
    obtain ⟨hne, hprim⟩ := head_conditions_of_ctors hdom hce
    have hglob : ∀ w ∈ e.vars, ∀ u, Env.lookup w ss.env = some u →
        Env.lookup w dk.env = some u := fun w hw u hu => by rw [hlink w (hsca.2 w hw)]; exact hu
    have hmemt : t ∈ sd'.terms := by
      refine hterms₁ t ?_
      rw [Database.addTerm_terms]
      exact Or.inr (Term.self_mem_subterms t)
    have hjust := encodeBuild_writesJustified hwf' hsc henvm e m hne hprim
      (held_of_evalAction hdom hwf' e hglob hce hev hmemt)
    have hblock : execActions dk (encodeBuild e m).2.1 = some dk₁ := h₁
    refine ⟨execActions_soundTerms_of_sets (encodeBuild e m).2.1 (encodeBuild_isSet e m)
      hjust rfl rfl (fun _ ht => ht) hsound hblock, fun w hw => ?_⟩
    rw [execActions_env_of_isSet (encodeBuild_isSet e m) hblock]
    exact hlink w hw
  · -- `.letBind v e`: the block, then the same `let` on both sides
    have hce : ∀ fk ∈ e.ctors, fk ∈ P.ctors := hca
    obtain ⟨hne, hprim⟩ := head_conditions_of_ctors hdom hce
    have hglob : ∀ w ∈ e.vars, ∀ u, Env.lookup w ss.env = some u →
        Env.lookup w dk.env = some u := fun w hw u hu => by rw [hlink w (hsca w hw)]; exact hu
    have hmemt : t ∈ sd'.terms := by
      refine hterms₁ t ?_
      rw [Database.terms_setEnv, Database.addTerm_terms]
      exact Or.inr (Term.self_mem_subterms t)
    have hjust := encodeBuild_writesJustified hwf' hsc henvm e m hne hprim
      (held_of_evalAction hdom hwf' e hglob hce hev hmemt)
    rw [encodeAction_letBind_actions, encodeBuild_fst] at h₁
    obtain ⟨dkA, hA, hB⟩ := execActions_append h₁
    have hsA : dkA.SoundTerms sd' :=
      execActions_soundTerms_of_sets (encodeBuild e m).2.1 (encodeBuild_isSet e m)
        hjust rfl rfl (fun _ ht => ht) hsound hA
    have henvA : dkA.env = dk.env := execActions_env_of_isSet (encodeBuild_isSet e m) hA
    have hsigA : dkA.sig = dk.sig := FDatabase.execActions_sig hA
    have hwlA : Actions.WriteLegal (encodeBuild e m).2.1 dk.sig := by
      rw [hsig]; exact writeLegal_encodeBuild hdom hag e m hce
    have hinvA : dkA.Inv := FDatabase.Inv.execActions hinv hwlA hA
    have hlast : execAction dkA (Action.letBind v e) = some dk₁ := by
      rw [execActions] at hB
      obtain ⟨d₂, hd₂, hrest⟩ := Option.bind_eq_some_iff.mp hB
      rw [execActions, Option.some.injEq] at hrest
      exact hrest ▸ hd₂
    obtain ⟨t', htgtev, hdk₁⟩ : ∃ t', e.eval dkA.sig dkA.env = some t' ∧
        dk₁ = { dkA.addTerm t' with env := (v, t') :: dkA.env } := by
      rw [execAction] at hlast
      obtain ⟨t', ht', h'⟩ := Option.map_eq_some_iff.mp hlast
      exact ⟨t', ht', h'.symm⟩
    obtain rfl : t = t' :=
      eval_target_of_source hdom e (fun w hw u hu => by rw [henvA]; exact hglob w hw u hu)
        hce hev htgtev
    have hentA : ∀ x ∈ t.subtermList, x.EntryShaped → x ∈ dkA.terms :=
      entryShaped_mem_of_eval e hne (fun w _ u hu =>
        entryShaped_mem_of_held (FDatabase.SubtermClosed.of_wf hinvA.wf)
          (FDatabase.mem_toDatabase_terms.mp
            (hinvA.wf.envInTerms (w, u) (Env.mem_of_lookup hu)))) htgtev
    refine ⟨?_, fun w hw => ?_⟩
    · rw [hdk₁]
      refine FDatabase.SoundTerms.mono_terms (fun x hx => hx)
        (hsA.addTerm (fun g cs y pfx hm => ?_) (fun y z pfx hm => ?_))
      · exact hsA.1 g cs y pfx (hentA _ hm (Or.inl ⟨g, cs, y, pfx, rfl⟩))
      · exact hsA.2 y z pfx (hentA _ hm (Or.inr ⟨y, z, pfx, rfl⟩))
    · rw [hdk₁]
      change Env.lookup w ((v, t) :: dkA.env) = Env.lookup w ((v, t) :: ss.env)
      rw [Env.lookup_cons, Env.lookup_cons, henvA]
      by_cases hwv : w = v
      · rw [if_pos hwv, if_pos hwv]
      · rw [if_neg hwv, if_neg hwv]
        refine hlink w ?_
        have : w ∈ Action.bind (Action.letBind v e) Γ := hw
        rw [Action.bind, List.mem_cons] at this
        exact this.resolve_left hwv
  · -- `.union e₁ e₂`: two blocks and one `@UF` edge
    have hc₁ : ∀ fk ∈ e₁.ctors, fk ∈ P.ctors :=
      fun fk hfk => hca fk (by rw [Action.ctors]; exact List.mem_append_left _ hfk)
    have hc₂ : ∀ fk ∈ e₂.ctors, fk ∈ P.ctors :=
      fun fk hfk => hca fk (by rw [Action.ctors]; exact List.mem_append_right _ hfk)
    obtain ⟨hne₁, hprim₁⟩ := head_conditions_of_ctors hdom hc₁
    obtain ⟨hne₂, hprim₂⟩ := head_conditions_of_ctors hdom hc₂
    have hg₁ : ∀ w ∈ e₁.vars, ∀ u, Env.lookup w ss.env = some u →
        Env.lookup w dk.env = some u := fun w hw u hu => by
      rw [hlink w (hsca.1 w hw)]; exact hu
    have hg₂ : ∀ w ∈ e₂.vars, ∀ u, Env.lookup w ss.env = some u →
        Env.lookup w dk.env = some u := fun w hw u hu => by
      rw [hlink w (hsca.2 w hw)]; exact hu
    have hm₁ : t₁ ∈ sd'.terms := by
      refine hterms₁ t₁ ?_
      rw [Database.addEq_terms]
      exact Or.inl (Or.inr (Term.self_mem_subterms t₁))
    have hm₂ : t₂ ∈ sd'.terms := by
      refine hterms₁ t₂ ?_
      rw [Database.addEq_terms]
      exact Or.inr (Term.self_mem_subterms t₂)
    have heq : (t₁, t₂) ∈ sd'.eqs := by
      refine heqs₁ (t₁, t₂) ?_
      rw [Database.addEq_eqs]
      exact Set.mem_insert _ _
    have hjust₁ := encodeBuild_writesJustified hwf' hsc henvm e₁ m hne₁ hprim₁
      (held_of_evalAction hdom hwf' e₁ hg₁ hc₁ hev₁ hm₁)
    have hjust₂ := encodeBuild_writesJustified hwf' hsc henvm e₂ (encodeBuild e₁ m).2.2
      hne₂ hprim₂ (held_of_evalAction hdom hwf' e₂ hg₂ hc₂ hev₂ hm₂)
    have hval : ∀ {z : Term}, e₁.eval dk.sig dk.env = some z ∨ e₂.eval dk.sig dk.env = some z →
        z = t₁ ∨ z = t₂ := by
      rintro z (hz | hz)
      · exact Or.inl (eval_target_of_source hdom e₁ hg₁ hc₁ hev₁ hz).symm
      · exact Or.inr (eval_target_of_source hdom e₂ hg₂ hc₂ hev₂ hz).symm
    have hsubx : ∀ {z : Term},
        e₁.eval dk.sig dk.env = some z ∨ e₂.eval dk.sig dk.env = some z →
        ∀ x ∈ z.subtermList, x.EntryShaped → x ∈ dk.terms := by
      rintro z (hz | hz)
      · exact entryShaped_mem_of_eval e₁ hne₁ (fun w _ => hbind w) hz
      · exact entryShaped_mem_of_eval e₂ hne₂ (fun w _ => hbind w) hz
    have hjust₃ : WritesJustified sd' dk
        [Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, pf]] := by
      intro g gargs out hmem is vs has hvs
      have hme : Action.set g gargs out
          = Action.set ufName [maxE e₁ e₂] [minE e₁ e₂, pf] := by simpa using hmem
      injection hme with hg ha ho
      subst hg; subst ha; subst ho
      obtain ⟨mx, hmx, rfl⟩ := Expr.evalList_single has
      obtain ⟨mn, pfv, hmn, hpfv, rfl⟩ := Expr.evalList_pair hvs
      refine ⟨fun c hc x hxm hshaped => ?_, fun f' q x pfx hq => ?_, fun x q pfx hq => ?_⟩
      · have hc2 : c = mx ∨ c = mn ∨ c = pfv := by simpa using hc
        rcases hc2 with rfl | rfl | rfl
        · exact hsubx (eval_ifGt_inv hmx) x hxm hshaped
        · exact hsubx (Or.symm (eval_ifGt_inv hmn)) x hxm hshaped
        · exact entryShaped_mem_of_eval pf hpfne (fun w _ => hbind w) hpfv x hxm hshaped
      · exact absurd (Term.app.inj hq).1 (fun hz => viewName_ne_ufName hz.symm)
      · obtain ⟨-, hcols⟩ := Term.app.inj hq
        have h3 : [mx, mn, pfv] = [x, q, pfx] := hcols
        obtain rfl : mx = x := (List.cons.inj h3).1
        obtain rfl : mn = q := (List.cons.inj (List.cons.inj h3).2).1
        rcases hval (eval_ifGt_inv hmx) with rfl | rfl <;>
          rcases hval (Or.symm (eval_ifGt_inv hmn)) with rfl | rfl
        · exact Cong.assert (hwf'.eqsRefl _ hm₁)
        · exact Cong.assert heq
        · exact (Cong.assert heq).symm
        · exact Cong.assert (hwf'.eqsRefl _ hm₂)
    have hjust : WritesJustified sd' dk (encodeAction pf (.union e₁ e₂) m).1 := by
      rw [encodeAction_union_actions, encodeBuild_fst, encodeBuild_fst]
      exact (hjust₁.append hjust₂).append hjust₃
    have hset : ∀ b ∈ (encodeAction pf (.union e₁ e₂) m).1, b.IsSet := by
      intro b hb
      rw [encodeAction_union_actions] at hb
      rcases List.mem_append.mp hb with hb' | hb'
      · rcases List.mem_append.mp hb' with hb'' | hb''
        · exact encodeBuild_isSet e₁ m b hb''
        · exact encodeBuild_isSet e₂ _ b hb''
      · obtain rfl : b = Action.set ufName [maxE (encodeBuild e₁ m).1
            (encodeBuild e₂ (encodeBuild e₁ m).2.2).1]
            [minE (encodeBuild e₁ m).1 (encodeBuild e₂ (encodeBuild e₁ m).2.2).1, pf] := by
          simpa using hb'
        trivial
    exact ⟨execActions_soundTerms_of_sets _ hset hjust rfl rfl (fun _ ht => ht) hsound h₁,
      fun w hw => by rw [execActions_env_of_isSet hset h₁]; exact hlink w hw⟩
  · exact absurd hnsa (fun hc => (hc : False))

/-- **The whole head, by induction over the source's own actions.** `Γ` is the scope the two
environments are linked on: `Rule.HeadScoped`'s at the block's start, extended by the block's
own `let`s after that. -/
theorem headActions_soundTerms {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {sd' : Database} (hwf' : sd'.WF) {pf : Expr} (hpfne : ∀ g ∈ pf.fns, NotEntryHead g) :
    ∀ (as : List Action) (Γ : Scope) (m : Nat) {ss ss' : Database} {dk dk' : FDatabase},
      (∀ a ∈ as, ∀ fk ∈ a.ctors, fk ∈ P.ctors) → (∀ a ∈ as, a.NoSet) →
      Actions.Scoped as Γ →
      (∀ v ∈ Γ, Env.lookup v dk.env = Env.lookup v ss.env) →
      dk.sig = encodeSig P → dk.Inv → dk.SoundTerms sd' →
      evalActions ss as = some ss' →
      (∀ t ∈ ss'.terms, t ∈ sd'.terms) → (∀ p ∈ ss'.eqs, p ∈ sd'.eqs) →
      execActions dk (encodeActions pf as m).1 = some dk' →
      dk'.SoundTerms sd' := by
  intro as
  induction as with
  | nil =>
    intro Γ m ss ss' dk dk' _ _ _ _ _ _ hsound _ _ _ htgt
    rw [show (encodeActions pf ([] : List Action) m).1 = [] from rfl, execActions,
      Option.some.injEq] at htgt
    exact htgt ▸ hsound
  | cons a as ih =>
    intro Γ m ss ss' dk dk' hctors hns hscoped hlink hsig hinv hsound hsrc hterms heqs htgt
    rw [encodeActions_cons_actions] at htgt
    obtain ⟨dk₁, h₁, h₂⟩ := execActions_append htgt
    rw [evalActions_cons, Option.bind_eq_some_iff] at hsrc
    obtain ⟨ss₁, hs₁, hs₂⟩ := hsrc
    have hcont := evalActions_contained hs₂
    have hca : ∀ fk ∈ a.ctors, fk ∈ P.ctors := hctors a List.mem_cons_self
    have hnsa : a.NoSet := hns a List.mem_cons_self
    obtain ⟨hsound₁, hlink₁⟩ := headAction_step hdom hag hwf' hpfne hca hnsa hscoped.1 hlink
      hsig hinv hsound hs₁ (fun t ht => hterms t (hcont.terms ht))
      (fun q hq => heqs q (hcont.eqs hq)) h₁
    refine ih (a.bind Γ) (encodeAction pf a m).2
      (fun b hb => hctors b (List.mem_cons_of_mem _ hb))
      (fun b hb => hns b (List.mem_cons_of_mem _ hb)) hscoped.2 hlink₁ ?_ ?_ hsound₁ hs₂
      hterms heqs h₂
    · rw [FDatabase.execActions_sig h₁]; exact hsig
    · exact FDatabase.Inv.execActions hinv
        (by rw [hsig]; exact writeLegal_encodeAction hdom hag pf a m hnsa hca) h₁



/-! ### `EncodedHeadSound`, discharged

The four things it needed. `Rule.HeadScoped` is a **case split** and not an assumption: the
scoped branch is the lemmas above, and where the source head is not scoped the encoded head is
stuck too, so that firing writes on neither side. `hlet` is gone — `headActions_soundTerms`
reads each action at the environment it ran under. `Database.TermsBuild` is the source-run
invariant proved above. And the reading `τ` is taken **once**, before the induction, so a
head's nested applications all read at the same one; `held_of_evalAction` composed with
`exists_subterm_of_mem_apps` is what answers a subapplication there. -/

/-- The static facts a source rule of an in-domain program has at a state its prefix
reaches. -/
theorem head_facts_of_domain {P : Program} (hdom : P.EncodeDomain) {p q : Program}
    (hP : P = p ++ q) {sd : Database} (hpre : ProgramStep Database.empty p sd) {s : Rule}
    (hmem : Cmd.rule s ∈ P) (hsrule : s ∈ sd.rules) :
    Actions.Builds s.actions sd.sig ∧ Actions.UnionRunnable s.actions sd := by
  refine ⟨headsBuild_of_programStep hdom hP hpre s hsrule, ?_⟩
  rcases hdom.noLitUnion with huf | hlit
  · exact Or.inl ((Cmd.ruleUnionFreeB_iff s).mp (huf _ hmem))
  · exact Or.inr ⟨(noLits_of_programStep hdom hlit
      (fun c' hc' => by rw [hP]; exact List.mem_append_left _ hc') hpre).terms,
      Cmd.NoLits.of_domain hdom hlit hmem⟩

/-- **`EncodedHeadSound`, proved — under `Program.HeadsScoped`.**

Every other hypothesis is the domain's. `Program.HeadsScoped` is **not** a domain clause and
is not derivable from one: `bare_build_invents_equality` below refutes
`encode_corresponds_complete` itself at a program the domain admits and this excludes. -/
theorem encodedHeadSound {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    (hhs : P.HeadsScoped) : EncodedHeadSound P (encodeSig P) := by
  intro pre q hP sd sd' hpre R c hc hstep d hok s i n hmem hsrule hrs hrd σ hσ e he
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  have hwf' : sd'.WF := hstep.wf hstate.wf
  obtain ⟨hgr, hnv, hk⟩ := hdom.queryEncodable_of_mem hmem
  obtain ⟨hbld, hun⟩ := head_facts_of_domain hdom hP hpre hmem hsrule
  have hscoped : s.HeadScoped sd := hhs.headScoped hmem sd
  have htb : sd.TermsBuild := termsBuild_of_programStep hdom hP hpre
  have hvs : d.toDatabase.ViewsSound sd :=
    (viewsSound_of_soundTerms hok.base.eqsRefl hok.sound).1
  obtain ⟨τ', hmatch, hagree⟩ := validQuerySubst_of_mem_matchQuery_diag hok.base.inv.eqs
    hok.base.eqsRefl hok.base.inv.index hσ
  have hglobτ : sd.GlobalsAgree (d.toDatabase.env ++ τ') := hok.glob.append
  have hread : ∀ p ∈ s.query, PatternRead d.toDatabase (d.toDatabase.env ++ τ') p :=
    patternReads_of_encodeQuery hok.base.diag hok.base.subterms hnv hk hmatch
  obtain ⟨τ, hqτ, hτ⟩ := exists_validQuerySubst_at_ids htb hvs hglobτ hgr hk hread
  obtain ⟨D, hD, hlocal⟩ := evalLocalActions_isSome_of_builds (Scope.Models.dom sd.env)
    hstate.wf hscoped hbld hun hqτ
  -- the target's block
  rw [execLocalActions, encodeRule_actions] at he
  obtain ⟨e₀, he₀, hee⟩ := Option.map_eq_some_iff.mp he
  have hgoal : e₀.SoundTerms sd' := by
    refine headActions_soundTerms (dk := { d with env := d.env ++ σ })
      (ss := { sd with env := sd.env ++ τ }) hdom hag hwf'
      (notEntryHead_ruleE (queryProofs_var (encodeQuery_valueVars s.query hnv n)))
      s.actions (Query.bind s.query (Env.dom sd.env)) (encodeQuery s.query n).2
      (fun a ha fk hfk => mem_ctors_of_cmd hmem (by
        rw [Cmd.ctors]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hfk⟩)))
      ((Program.setLegal_iff_noSet (fun _ => rfl) hdom.ctorsOnly).mp hdom.setLegal _ hmem)
      hscoped ?_ hok.base.sig (hok.base.inv.setEnvMatch hσ)
      (hok.sound.mono_src (CmdStep.contained hstep).eqs) hD ?_ ?_ he₀
    · intro v hv
      have hv' : v ∈ Query.vars s.query ∨ (Env.lookup v sd.env).isSome := by
        rcases List.mem_union_iff.mp hv with hv' | hv'
        · exact Or.inr (Env.lookup_isSome_iff_mem_dom.mpr hv')
        · exact Or.inl hv'
      change Env.lookup v (d.env ++ σ) = Env.lookup v (sd.env ++ τ)
      rw [← Env.Agree.append_left d.env hagree v]
      exact lookup_eq_of_at_ids hvs hglobτ hk hread hτ hv'
    · intro t ht
      exact mem_terms_of_ruleFired hc hstep hsrule hrs hqτ hlocal
        (Database.terms_setEnvRules ▸ ht)
    · intro pr hpr
      exact mem_eqs_of_ruleFired hc hstep hsrule hrs hqτ hlocal hpr
  rw [← hee]
  exact hgoal


/-! ## What the head obligation closes

`execM_soundTerms_of_head` with `EncodedHeadSound` discharged is the whole of the
completeness half **under `Program.HeadsScoped`**, and the three theorems below are it,
carried up to the statement `encode_corresponds` is one half of. The clause is
`EncodeDomain.headsScoped`, so these three are the domain's own statements with it spelled
out — the form that says what the domain is buying, and `bare_build_invents_equality` is what
says it has to buy it. -/

/-- **The invariant, at the state `execM` returned** — with the clause spelled out.
`execM_soundTerms` is this at `hdom.headsScoped`. -/
theorem execM_soundTerms_of_scoped {P : Program} (hdom : P.EncodeDomain)
    (hhs : P.HeadsScoped) {src : Database} (hsrc : ProgramStep Database.empty P src)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src :=
  execM_soundTerms_of_head hdom hdom.aritiesAgree'
    (encodedHeadSound hdom hdom.aritiesAgree' hhs) hsrc htgt

@[inherit_doc execM_soundTerms_of_scoped]
theorem execM_viewsSound_of_scoped {P : Program} (hdom : P.EncodeDomain)
    (hhs : P.HeadsScoped) {src : Database} (hsrc : ProgramStep Database.empty P src)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) :
    tgt.toDatabase.ViewsSound src ∧ tgt.toDatabase.EdgesSound src :=
  viewsSound_of_soundTerms (execM_encode_eqsRefl htgt)
    (execM_soundTerms_of_scoped hdom hhs hsrc htgt)

/-- **The completeness half, with the clause spelled out.** `encode_corresponds_complete` is
this theorem at `hdom.headsScoped`; dropping the clause from the domain is what
`bare_build_invents_equality` refutes. -/
theorem encode_corresponds_complete_of_scoped {P : Program} (hdom : P.EncodeDomain)
    (hhs : P.HeadsScoped) {src : Database}
    (hsrc : ProgramStep Database.empty P src) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) {a b : Term} (ha : a ∈ src.terms) (hb : b ∈ src.terms)
    (h : SameClass tgt.toDatabase a b) : Cong src a b :=
  sameClass_cong_of_state (hsrc.wf Database.WF.empty)
    (execM_viewsSound_of_scoped hdom hhs hsrc htgt).1 ha hb h

/-! ### And the clause is not vacuous

`ENCODING.md`'s discipline at a hypothesis as much as at a lemma: `Program.HeadsScoped` has to
hold of a program with a rule that really fires, or `EncodeDomain.headsScoped` would empty the
domain of the cases the statement is about. `ncProgram` is the one the forward half's two
refuted clauses are pinned at — a unary constructor, a `union` between two nullary ones, and a
rule that fires once per class member — and `vuProgram` is the `union`-head one, whose head
unions a **variable** with an application and so takes `noLitUnion`'s second arm. Both are
head-scoped, and `ncProgram`'s source run is compiled. The corpus measurement is
`DiffTest.lean`'s census: 70 of 166 in domain, the same 70 as before the clause. -/

/-- `ncRule`'s head reads only `x`, which its query binds. -/
theorem ncProgram_headsScoped : ncProgram.HeadsScoped := by decide

@[inherit_doc ncProgram_headsScoped]
theorem vuProgram_headsScoped : vuProgram.HeadsScoped := by decide

/-- **Every hypothesis of `execM_soundTerms_of_scoped` holding together**, at a program whose
rule fires: the source run is compiled (`ncProgram_programStep`) and only the encoded run is a
hypothesis, for the reason every other target-side witness here takes one. -/
theorem execM_soundTerms_of_scoped_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) : tgt.SoundTerms ncSrc.toDatabase :=
  execM_soundTerms_of_scoped ncProgram_encodeDomain ncProgram_headsScoped
    ncProgram_programStep htgt

/-- `ncProgram` builds `(F (A))`, and its rule builds `(F (B))` off the `union`. -/
theorem ncSrc_mem_FA' : ncFA ∈ ncSrc.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms, ncSrc_terms_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

@[inherit_doc ncSrc_mem_FA']
theorem ncSrc_mem_FB' : ncFB ∈ ncSrc.toDatabase.terms := by
  rw [FDatabase.toDatabase_terms]; exact ncSrc_mem_FB

@[inherit_doc execM_soundTerms_of_scoped_witness]
theorem encode_corresponds_complete_of_scoped_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) {a b : Term}
    (ha : a ∈ ncSrc.toDatabase.terms) (hb : b ∈ ncSrc.toDatabase.terms)
    (h : SameClass tgt.toDatabase a b) : Cong ncSrc.toDatabase a b :=
  encode_corresponds_complete_of_scoped ncProgram_encodeDomain ncProgram_headsScoped
    ncProgram_programStep htgt ha hb h

/-- **The completeness half's invariant. Proved.**

`Program.EncodeDomain` carries `headsScoped`, so this is `execM_soundTerms_of_scoped` at
`hdom.headsScoped` and there is no residue left. Everything this file proves is spent there.

**It was false, three times over, and the domain excludes all three.** A source rule head that
gets *stuck* contributes nothing — `RuleResults` asks `evalLocalActions` for a `some` — and its
encoding's head, which is `.set`s, writes anyway. `Encoding/Correspond.lean`'s
`execM_soundTerms_false` is a head applying a constructor nobody declared, its
`encode_corresponds_unions_literals` is a head unioning two literals, and its
`bare_build_invents_equality` is a head *building* a variable nothing binds — which
`encodeBuild` emits no action at all for, so the encoded block skips it and runs on where the
source block stops. The last two refute not this residue but `encode_corresponds_complete`
**itself**, at a pair of terms the source holds and the two membership hypotheses are
satisfied at. So `EncodeDomain.noLitUnion`, `EncodeDomain.headsDeclared` and
`EncodeDomain.headsScoped` are load-bearing for the conclusion and not only for the proof, and
everything below is stated under them.

`Database.ViewsSound` and `Database.EdgesSound` at the state `execM` returned, in the term-list
form the run can carry (`viewsSound_of_soundTerms` is the step back). Every *per-entry*
obligation is discharged, one per writer `encode` emits — `entrySound_build`,
`EntrySound.eclass`, `EntrySound.column`, `EntrySound.select`, `cong_of_entrySound_collide`,
`cong_of_eqs`, `cong_of_pathCompress` here, and `entrySound_headBuild`/`cong_headUnion` in
`Encoding/Match.lean` for the two writers a rule head has — so what is missing is the
*induction that applies them*, and what that still needs.

* **The interpreter's writers, enumerated. The merge phase and the rule-firing fold are both
  done; the source rule's *head* is not.** `unionsInv_step`'s five closed cases only ever need
  the terms a block of `set`s wrote,
  which `holdsBuild_of_execProgramM` reads back off `execActions`. This invariant owes *every*
  term the run adds, and every command `encodeCmd` emits for a writing source command ends in
  `Cmd.saturate rebuildRuleset` — so no case closes without "every term `execRunRules` and
  `FDatabase.mergeRound` add is one of these `set`s'". What the fold has to compose was already
  settled: `FDatabase.SoundTerms.addTerm`, `.addRow` and `.union` are the three writers of
  `terms` there are, `FDatabase.empty_soundTerms` is the base case, and
  `FDatabase.SoundTerms.mono_src` carries a clause proved at a command's pre-state onto the
  source the whole run finishes at.

  **The double fold over row pairs is now proved**: `mergeSaturateF_soundTerms`, out of
  `mergeRound_soundTerms` and `mergeOneOriented_soundTerms`, and it asks nothing of a merge
  firing beyond the state. The two obstacles that stood in front of it are gone.
  `Signature.MergeShape` is the sig-shape invariant — only `@UF` and the views carry a
  `:merge`, both carry `mergeBody`, and both are two columns wide — and
  `execM_encode_mergeShape` establishes it at the target, out of the prelude's declarations
  and the fact that `encodeCmds` emits none. `eq_of_congrKeys` is the other: a pass compares
  keys against a **diagonal** closure, so congruent keys are equal keys, which is what makes
  the two colliding rows two entries at *one* key and hence
  `cong_of_entrySound_collide`/`EntrySound.select`'s hypothesis. The body itself is read back
  by `execActions_mergeBody_inv` and `evalList_mergeResult_inv`, whose content is that each of
  the four selectors answers with one of the two columns it chose between
  (`mergeSelector_cases`) — which is all either write needs, and is why the tie-break never
  enters. The two rows are turned into entry terms by `mem_terms_of_indexOk`, which is
  `FDatabase.IndexOk.entry` read at a diagonal state. `cxPre_mergeOneOriented_writes` is the
  firing happening at a state a program reaches, writing an edge the state did not hold.

  **The fold over rule firings is now proved too, and so are the three maintenance
  families.** `execRunRules` is a fold of `fireRule` over the ruleset's rules and `fireRule` a
  fold of `fireInto` over the matches, *all read off the round's pre-state* — so what a round
  owes is one obligation per firing at that one state, which is `FDatabase.FiringsSound`, and
  `fireInto_soundTerms`, `fireRule_soundTerms`, `execRunRules_soundTerms` and
  `runRoundM_soundTerms` are the fold and the merge phase after it. The **rule invariant** it
  needed is `execM_encode_rules`: every rule a target holds is `(encodeRule i s n).1` for a
  source rule `s` of `P`, or one of `maintenanceRules P` (`Rule.EncodedIn`,
  `FDatabase.RulesEncoded`), established at the prelude and carried because `encodeCmd` emits a
  rule only for a source `.rule` — `mergeShapeOk_encodePrelude`'s shape one level up. And the
  **maintenance side of the split is discharged**: `maintenance_soundTerms`, out of
  `pathCompressRule_soundTerms` (`cong_of_pathCompress`), `eclassRule_soundTerms`
  (`EntrySound.eclass`) and `columnRule_soundTerms` (`EntrySound.column`). Three things paid
  for those. `mem_terms_of_patternHolds_values` reads a matched row atom back as an entry term
  at **either** of `patternHolds`' branches — the index one through
  `FDatabase.IndexOk.entry`, the constructor one off `terms` — so the two never have to be told
  apart. `Expr.eval_of_refines` moves a reading from the substitution the *pattern* was checked
  at (`Env.canon` of the pattern's own free variables) to the one the *head* runs under.
  And `entryShaped_mem_of_eval` is what makes a minted proof column cost nothing: no head the
  encoding applies inside a proof is a view or `@UF` — `viewName_ne_congrName` is the last
  separation that was missing, and `Nat.isDigit_of_mem_toDigits` is what pays for it — while a
  *primitive* answers with a literal or with one of its own operands (`prim_apply_cases`), so
  the clause under a proof node is answered by the columns the match bound.

  **`firingsSound_of_rulesEncoded` is the factorisation those leave, and the per-command
  induction over it is now proved.** `FDatabase.EncOk.stepCmds` is the alignment
  `encodeCmds` sets up, carried command by command: `FDatabase.EncOk` bundles the structural
  invariants the fold and the merge phase want with the two source-relative clauses, stated
  at the **contemporaneous** source state, and `FDatabase.SoundTerms.mono_src` reaches the
  run's final source only at the last step. `FDatabase.EncBase.execCmdM` is the structural
  half through one command — `FDatabase.Inv.execCmdM`, `execCmdM_noUnions`,
  `FDatabase.execCmdM_mergeShape` and `FDatabase.execCmdM_rulesEncoded` composed — and
  `preludeState_encOk` is the base case, free because `encodePrelude` is declarations and
  rules and so leaves the data empty (`FDatabase.Inv.of_empty_data`).

  **The `.saturate` case is closed too, and by two separate mechanisms.** A round of
  `@rebuild` fires **no** source rule: `encodeRule` keeps a source rule's own ruleset and
  `EncodeDomain.noAt` keeps every source name out of the generated namespace
  (`ruleset_ne_rebuild`), so `FDatabase.FiringsSoundIn` — `FiringsSound` restricted to the
  rules a round actually runs — is what those rounds need, and `maintenance_soundTerms` is
  the whole of their discharge (`firingsSoundIn_rebuild`, `runRoundM_soundTerms_in`). A
  saturating run of the **source's** ruleset needs the head obligation at every round it
  passes through, not only the first, and gets it because the source's own post-state is a
  `RunRules` fixpoint (`RunSaturated`) and so steps to itself: `cmdStep_saturate_iff` turns
  that into a `CmdStep sd' (.saturate R) sd'`, and every target round then reads and
  concludes there (`FDatabase.EncOk.saturate_src`). `runSaturateM_closed` is the iteration.

  **`EncodedHeadSound` is discharged too, and the clause it wanted is the domain's.**
  `execM_soundTerms_of_obligations` is the reduction and it is `sorryAx`-free;
  `execM_soundTerms_of_head` is it with the two legality conditions
  (`encodedWriteLegal`, `maintenance_writeLegal`) and the top-level action case
  (`encodedActionSound`) all discharged; `encodedHeadSound` is the head case, under
  `Program.HeadsScoped`. Neither clause it asked for is missing now: `Program.AritiesAgree` is
  `EncodeDomain.aritiesAgree` over `Program.arityConflicts`, and `Program.HeadsScoped` is
  `EncodeDomain.headsScoped`. Neither follows from the others —
  `adProgram_not_maintenance_writeLegal` and `bare_build_invents_equality` are the two
  necessities, each at a program every *other* clause admits.
* **The row-to-entry direction, which is the one that is *not* refuted, and it is proved.** A
  rule fires off `d.rows` (`patternHolds`), and turning a matched row into a `Database.Out` is
  `FDatabase.IndexOk.entry` — a row is an entry term. That is the direction soundness needs,
  and `mem_terms_of_patternHolds_values` is it.
  `FDatabase.IndexCurrent` is its converse, and `cxTgt_not_indexCurrent` refutes *that*; so the
  refutation that blocks `execM_viewJoined` does not block this residue, which is why the
  two are separate holes. `patternHolds_values_of_mem_rows` is the *converse* of the reading —
  a row makes its own atom hold, at the values its own columns are — and it is what says the
  three families are not vacuous: `cxRb_mem_matchQuery` is a maintenance rule's query really
  matching at a state two `set`s leave, **proved rather than decided**, since `matchQuery`
  computes a closure and `closureF` does not reduce in the kernel. `cxRb_eclassRule_writes` is
  the head writing an entry the state did not hold — it is `cxPre`'s third `set`, so the
  merge-phase witness above is the state this firing produced — and
  `cxRb_eclassRule_soundTerms` is every hypothesis of `eclassRule_soundTerms` holding together
  there, over a source (`cxRbSrc`) that really derives the equation the matched edge carries.
* **`hfired` was where the falsity was, and it is now discharged.**
  `entrySound_headBuild` and `cong_headUnion` ask that the *source* rule fired at the
  substitution the correspondence returns, and `RuleResults` makes a firing a valid
  substitution **plus a block that evaluates**. `exists_validQuerySubst_of_encodeQuery`
  delivers the substitution and nothing more; a valid substitution is therefore *not* a
  firing, and the two refutations above are exactly the gap. Three parts, all three **proved**,
  and `mem_terms_of_headBuild_of_domain`/`mem_eqs_of_headUnion_of_domain` are the two shapes
  composed:
  * *A firing's writes reach the post-state.* `mem_terms_of_ruleFired` and
    `mem_eqs_of_ruleFired`, off `runRules_eqs_subset_of_cmdStep`. `RunRules` is a
    `Database.sUnion` over the results and `MergeClosure` only grows `eqs`.
  * *Two states, not one.* `Database.ViewsSound` is available at the round's **pre**-state,
    which is the state the encoded rule read its rows off; the term the source's firing builds
    lands in the **post**-state. `FDatabase.SoundTerms.mono_src` does not bridge that — it
    moves a clause along `src.eqs ⊆ src'.eqs`, and `Term.app f is ∈ sd.terms` is not a clause
    at `sd` at all. `entrySound_headBuild_post` and `cong_headUnion_post` are the
    two-source forms — the reading at `sd`, the conclusion at `sd'` — and the old names are
    their `src' := src` instances.
  * *The block evaluates at all*, which is what the two domain clauses buy.
    `evalLocalActions_isSome_of_builds` is the fold: `headsDeclared` gives every applied name a
    source constructor (`Actions.Builds.of_declared`, carried on the state as
    `Database.HeadsBuild`), and `noLitUnion` gives `evalAction`'s own `union` check
    (`Actions.UnionRunnable`, whose two arms are the clause's two disjuncts). The second arm is
    the one that is not syntactic — `Spec/Scope.lean`'s `Action.Evaluable` asks a `union`
    operand to be an *application*, and a lit-free program's **variable** operand is not one —
    so it is carried as the source-run invariant `Database.NoLits`, whose data clause
    `Database.LitFree` says no term the source holds is a literal.
    `exists_step_of_mem_evalActions` is the environment part the old text called for: an action
    after a `letBind` runs at `src.env ++ τ` extended by the block's own binders, and where the
    head mentions none of them (`hlet`) the extension drops out by `Expr.eval_agreeOn`, which is
    the shape `hfired` is stated in.

  **Two conditions on the firing were named here, and both are settled.** `Rule.HeadScoped` —
  every head variable is the query's, a global, or the block's own `let` — was recorded as
  costing nothing, on the reading that an unbound head variable sticks the **encoded** head
  too. That reading is wrong at a *leaf*, which is `bareProgram`, so it is a real condition and
  it is a domain clause: `EncodeDomain.headsScoped` on the program's text,
  `Program.HeadsScoped.headScoped` for the state form the proof spends. `hlet` is gone
  outright: `headActions_soundTerms` runs the two blocks in lockstep, so each action is read at
  the environment it actually ran under and the `let` prefix is shared by construction.

  `EncodedHeadSound` is proved from those at the substitution
  `validQuerySubst_of_mem_matchQuery_diag` delivers — `validQuerySubst_of_mem_matchQuery`
  with `Signature.AllConstructors`, which no encoded target has, traded for
  `FDatabase.EqsRefl` and `FDatabase.IndexOk`, which every one of them has.

  It is the mirror of `unionsJoined_fire`, a source firing behind the target's where that one
  needs a target firing behind the source's; what it is no longer is open.

**The two legality conditions are `EncodedWriteLegal` and its maintenance counterpart, and
the domain clause they need is `EncodeDomain.aritiesAgree`.** `Program.AritiesAgree` is the
form they consume: `Program.ctors` is read off the syntax, one `(name, arity)` pair per
application and per declaration, so a program applying one name at two arities gets two table
triples and the later declaration wins — and the losing arity's rebuild rules then `set` a
view at the wrong key width, which is what `Actions.SetWidthOk` forbids and
`FDatabase.Inv.execCmdM` asks of every rule the state holds, fired or not.
`Program.EncodeDomain.aritiesAgree'` is the bridge. The third condition,
`Signature.MergesLegal` at the encoded signature, **is** a consequence and is proved:
`encodeSig_mergesLegal`, out of `encodeSig_mergeShape` and `encodeSig_ufName`.

**No fixpoint is needed on the target.** `FDatabase.RoundClosed` was named as this residue's
third missing piece; it is not one. Soundness is indifferent to under-firing — `execM_contained`
says the encoded round fires a subset, and a subset of justified writes is justified — so what
this needs is the *containment*, not the fixpoint. The fixpoint is what `execM_viewJoined`
and `unionsJoined_fire` want, where a firing has to be shown to have *happened*.

**The rule head is closed, and was the case worth doubting.** `encodeBuild` mints its skolem
over the arguments' *ids*, so `mem_terms_of_entrySound_skolem` makes the head's obligation
equivalent to the minted id being a source term — which, read off the key, is the fact
`encode_corresponds_invents_enode` refutes. It is not needed: the source reading the
correspondence delivers is a *choice*, and taking it to be the ids themselves is legitimate
because `Database.ViewsSound` reads a key column back as something congruent to the id and both
endpoints of a congruence are present. `Encoding/Match.lean`'s `exists_validQuerySubst_at_ids`
is that reading, `Expr.eval_transport` is why the source's head evaluation then gives the same
term rather than a congruent one, and `entrySound_headBuild` is the case — with `hfired` as its
only residue. `entrySound_headBuild_witness` is all of its hypotheses holding together at
`wProgram`, at the view entry that run really wrote.

**`addTerm` records every subterm**, so the induction also owes that no *id* and no *proof*
term is view- or `@UF`-shaped. **That obligation now collapses**, and no syntactic invariant on
ids is needed for it: `FDatabase.SoundTerms.addTerm_top` asks it only at the *written* term,
because a recorded subterm the state already holds is discharged by `FDatabase.SoundTerms`
itself (`FDatabase.subterms_of_columns`, at a subterm-closed state) and the shells a writer
mints around held terms are of neither shape (`Term.EntryShaped`, `not_entryShaped_of_ne`,
`not_entryShaped_of_length`, and `entryShaped_mem_of_transSym` for the one proof node a merge
body mints). The name separations `viewName_inj`, `viewName_ne_ufName`,
`viewName_ne_termName` and `viewName_ne_transName` are what pay for the shells, and
`Program.EncodeDomain.noAt` is still what keeps a source constructor out of the generated
namespace where a *head*'s skolem has to be told apart from an entry.

At a program with no rule the hypothesis is the source's own `evalAction`, and
`satTarget_viewsSound` is that case discharged; `ncTgt_soundTerms` is both clauses at a state
an encoded program reaches with a rule, a non-leader firing and a real `@UF` edge.

**Nothing is left.** `encodedHeadSound` is the head obligation discharged and every one of
the four things it needed is done. `hlet` is gone: `headActions_soundTerms` runs the two blocks
in lockstep, one source action at a time, so each action is read at the environment it actually
ran under and the `let` prefix is shared by construction rather than excluded.
`Database.TermsBuild` is `termsBuild_of_programStep`, an induction through `evalAction`,
`RunRules` and `ProgramStep`. The reading τ is taken **once**, before that induction, so a
head's nested applications all read at the same one, and `held_of_evalAction` composed with
`exists_subterm_of_mem_apps` answers a subapplication there. And `Rule.HeadScoped` is not a
case split but a hypothesis, because the statement is false without it — which is why it is a
domain clause and not a lemma.

**The clause is faithfulness, not a narrowing.** egglog rejects a rule head that reads an
unbound variable outright: `to_core_actions`, the lowering for *actions*, resolves a
`GenericExpr::Var` only when `ctx.binding` holds it or it is a global, and raises
`TypeError::Unbound` otherwise (`egglog/src/core.rs:663-670`) — the same shape the clause has.
The census is unmoved: 70 of 166 in domain, as before it was added.

**Neither the bundle nor the reduction is vacuous.** `wPreludeState_encOk` is
`FDatabase.EncOk` at the state `encode wProgram`'s prelude really leaves — the prelude is
declarations and rules, so it reduces in the kernel — `adProgram_not_maintenance_writeLegal`
is `EncodeDomain.aritiesAgree`'s necessity and `bare_build_invents_equality` is
`EncodeDomain.headsScoped`'s, each at a program every *other* clause admits, and
`execM_soundTerms_witness` is every hypothesis of this theorem holding together at a program
whose rule really fires. -/
theorem execM_soundTerms {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src :=
  execM_soundTerms_of_scoped hdom hdom.headsScoped hsrc htgt

/-- **The completeness half's invariant at the state `execM` returned.** `execM_soundTerms` is
the residue; the step from it is `viewsSound_of_soundTerms`, whose hypothesis
`execM_encode_eqsRefl` discharges. -/
theorem execM_viewsSound {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    tgt.toDatabase.ViewsSound src ∧ tgt.toDatabase.EdgesSound src :=
  viewsSound_of_soundTerms (execM_encode_eqsRefl htgt) (execM_soundTerms hdom hsrc htgt)

/-- **No equality is invented, at the source's own e-nodes. Proved.** From
`execM_viewsSound`, through `sameClass_cong_of_state` — the target-side half needs no
induction, only the invariant. `encode_corresponds_complete_witness` is it at a pair both
sides really relate.

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

/-! ### Both halves, at a program that exercises them

`ENCODING.md`'s discipline for a conclusion as much as for a hypothesis: the two theorems
above are conditionals, so each is exhibited at a program whose rule really fires, at a pair
of source e-nodes the two sides really relate. `ncProgram` is that program — its source run is
compiled (`ncProgram_programStep`) and only the encoded run is a hypothesis, for the reason
every other target-side witness here takes one, since `execM` on an encoded program does not
reduce in the kernel. -/

/-- **Every hypothesis of `execM_soundTerms` holding together**, at `ncProgram`. -/
theorem execM_soundTerms_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) : tgt.SoundTerms ncSrc.toDatabase :=
  execM_soundTerms ncProgram_encodeDomain ncProgram_programStep htgt

/-- **`encode_corresponds_complete` at a pair both sides really relate.**

`(F (A))` and `(F (B))` are two *distinct* source e-nodes of `ncProgram`: the source derives
the equation (`ncSrc_cong_FA_FB`, off the `union` its rule fires on) and the encoded run
shares an id for it (`ncTgt_sameClass_FA_FB`, at the state the run is transcribed to), so
neither side of the conclusion is empty and neither is the diagonal. The theorem itself is
then applied at the state `execM` really returns, whose `SameClass` — like every other
target-side fact here — is a decidable hypothesis, since the kernel cannot run an encoded
program. What comes back is a congruence between two distinct source terms. -/
theorem encode_corresponds_complete_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) (hsc : tgt.SubtermClosed) (hr : tgt.EqsRefl)
    (hyes : sameClassF tgt ncFA ncFB = true) :
    ncFA ≠ ncFB ∧ Cong ncSrc.toDatabase ncFA ncFB ∧
      SameClass ncTgt.toDatabase ncFA ncFB ∧ SameClass tgt.toDatabase ncFA ncFB :=
  have hsame : SameClass tgt.toDatabase ncFA ncFB := (sameClassF_iff hsc hr _ _).mp hyes
  ⟨by decide,
    encode_corresponds_complete ncProgram_encodeDomain ncProgram_programStep htgt
      ncSrc_mem_FA' ncSrc_mem_FB' hsame,
    ncTgt_sameClass_FA_FB, hsame⟩

/-- **The correspondence.** `difftest correspond 64` runs exactly this claim over the 70
in-domain cases and the seventeen probes, through `sameClassF` and `closureF`, and reports
70 agreeing, 0 LOST, 0 INVENTED — and `link-diff` 0, which is what says the swept relation
is this one.

`EncodeDomain` is still needed: outside it `encode` is not defined for the program at all —
a `:merge` declaration has no table triple to emit, and a source name in the generated
namespace collides with one. `Rebuilt` is *not* a hypothesis: it is a postcondition of the
specification's rebuild command (`cmdStep_rebuilt`), and the hypothesis here names an
`execM` target, so what both halves lean on is the interpreter's own `mergeSaturateF`
fixpoint instead.

**Stated at the source's e-nodes**, which is where the encoding is faithful and where the
corpus sweep measures it. The two membership hypotheses cost the forward direction nothing —
`Cong src a b` implies both — and the backward direction cannot do without them:
`encode_corresponds_invents_enode` refutes the unrestricted `iff` at the witness program
`Encoding/Correspond.lean` keeps for it. -/
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt.toDatabase a b :=
  ⟨encode_corresponds_forward hdom hsrc htgt, encode_corresponds_complete hdom hsrc htgt ha hb⟩


end Egglog
