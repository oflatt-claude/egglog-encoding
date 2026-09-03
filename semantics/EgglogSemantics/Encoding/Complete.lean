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

/-- The two source clauses move along a source that grows and keeps its environment. -/
theorem FDatabase.EncOk.mono_src {d : FDatabase} {P : Program} {sg : Signature}
    {sd sd' : Database} (h : d.EncOk P sg sd) (heq : sd.eqs ⊆ sd'.eqs)
    (henv : ∀ v t, Env.lookup v sd'.env = some t → Env.lookup v sd.env = some t) :
    d.EncOk P sg sd' where
  base := h.base
  glob := fun v t hv => h.glob v t (henv v t hv)
  sound := h.sound.mono_src heq

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
    ∀ (s : Rule) (i n : Nat), Cmd.rule s ∈ P → (encodeRule i s n).1 ∈ d.rules →
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

/-- The bundle moves onto the command's post-state, where neither the source environment nor
the target's has moved. -/
theorem FDatabase.EncOk.step_src {P : Program} {sg : Signature} {sd sd' : Database}
    {d : FDatabase} (hok : d.EncOk P sg sd) {c : Cmd} (hc : ∀ a, c ≠ Cmd.action a)
    (hstep : CmdStep sd c sd') : d.EncOk P sg sd' :=
  hok.mono_src (CmdStep.contained hstep).eqs
    (fun v t hv => by rw [cmdStep_env_of_noAction hc hstep] at hv; exact hv)

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
  have hfire : d.FiringsSound sd' := by
    refine firingsSound_of_rulesEncoded hok.base.rules hok.base.eqsRefl hok.base.inv.index
      hok.base.subtermClosed (hok.sound.mono_src (CmdStep.contained hstep).eqs) ?_
    intro s i n hmem hr σ hσ e' he'
    exact hhead hP hpre hc hstep hok s i n hmem hr σ hσ e' he'
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_⟩, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · intro v t hv
    rw [henv]
    exact hok.glob v t (by rw [cmdStep_env_of_noAction hna hstep] at hv; exact hv)
  · exact runRoundM_soundTerms (by rw [hok.base.sig]; exact hok.base.shape)
      (by rw [hok.base.sig]; exact hok.base.merges) hok.base.inv hok.base.nounions
      hok.base.wl' hfire (hok.sound.mono_src (CmdStep.contained hstep).eqs) hrun

/-- **A rebuild round.** No source rule joins `@rebuild`, so every firing is a maintenance
firing and the source state does not move. -/
theorem FDatabase.EncOk.runRoundM_rebuild {P : Program} (hdom : P.EncodeDomain)
    {sg : Signature} {sd : Database} {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.runRoundM rebuildRuleset = some e) : e.EncOk P sg sd := by
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hrun
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_⟩, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · intro v t hv; rw [henv]; exact hok.glob v t hv
  · exact runRoundM_soundTerms_in (by rw [hok.base.sig]; exact hok.base.shape)
      (by rw [hok.base.sig]; exact hok.base.merges) hok.base.inv hok.base.nounions
      hok.base.wl' (firingsSoundIn_rebuild hdom hok) hok.sound hrun

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
    refine ⟨hb, ?_, hok.sound.mono_src (CmdStep.contained hstep).eqs⟩
    intro v t hv
    rw [cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep] at hv
    exact hok.glob v t hv
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
        empty_noUnions hprel, ?_⟩, ?_, ?_⟩
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
  obtain ⟨-, rfl, rfl, hout, -⟩ := encodeSig_mergeShape P g dc hg body res hm
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


/-! ### The clause is needed, at a program the domain admits

`ENCODING.md`'s discipline for a clause as much as for a lemma: a condition that nothing
violates is not a condition. `adProgram` is two commands, it satisfies every clause of
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

/-- **`adProgram` is in the domain.** Every clause, and nothing about arities among them. -/
theorem adProgram_encodeDomain : adProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc
    simp only [adProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | h <;> simp_all [Cmd.CtorDecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [adProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | h
    · trivial
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inl (by decide)
  headsDeclared := by decide

/-- **And it violates the missing clause**, which is what says the clause is not vacuous. -/
theorem adProgram_not_aritiesAgree : ¬ adProgram.AritiesAgree := by
  intro h
  have h1 : (("F", 1) : FnName × Nat) ∈ adProgram.ctors := by decide
  have h2 : (("F", 0) : FnName × Nat) ∈ adProgram.ctors := by decide
  exact absurd (h _ h1 _ h2 rfl) (by decide)

/-- **The obligation is false there.** `encodeSig adProgram (viewName "F")` is `viewDecl 0`
and the rule keys at one column, so `Actions.SetWidthOk` fails — and with it
`FDatabase.EncBase`'s `wl`, hence `FDatabase.Inv` at every state after the rebuild.

Compiled, and with no `sorry` anywhere under it: this is the clause `Program.EncodeDomain`
would have to gain for `execM_soundTerms` to follow from the reduction. -/
theorem adProgram_not_maintenance_writeLegal :
    ¬ ∀ r ∈ maintenanceRules adProgram, Actions.WriteLegal r.actions (encodeSig adProgram) := by
  intro h
  have hsig : encodeSig adProgram (viewName "F") = some (viewDecl 0) := rfl
  have hone := ((h adBadRule adBadRule_mem).2.1 (viewDecl 0) hsig).1
  simp [rebuildVars, viewDecl] at hone

/-- **The residue of the completeness half. Not proved.**

**It was false, twice over, and the domain now excludes both.** A source rule head that gets
*stuck* contributes nothing — `RuleResults` asks `evalLocalActions` for a `some` — and its
encoding's head, which is `.set`s, writes anyway. `Encoding/Correspond.lean`'s
`execM_soundTerms_false` is a head applying a constructor nobody declared, and its
`encode_corresponds_unions_literals` is a head unioning two literals; the second refutes not
this residue but `encode_corresponds_complete` **itself**, at a pair of terms the source holds
and the two membership hypotheses are satisfied at. So `EncodeDomain.noLitUnion` and
`EncodeDomain.headsDeclared` are load-bearing for the conclusion and not only for the
proof, and everything below is stated under them.

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

  **What is left is `EncodedHeadSound` and `EncodedActionSound`**, and two legality
  conditions. `execM_soundTerms_of_obligations` is the reduction, and it is `sorryAx`-free.
* **The row-to-entry direction, which is the one that is *not* refuted, and it is proved.** A
  rule fires off `d.rows` (`patternHolds`), and turning a matched row into a `Database.Out` is
  `FDatabase.IndexOk.entry` — a row is an entry term. That is the direction soundness needs,
  and `mem_terms_of_patternHolds_values` is it.
  `FDatabase.IndexCurrent` is its converse, and `cxTgt_not_indexCurrent` refutes *that*; so the
  refutation that blocks `execM_viewLeaderRows` does not block this residue, which is why the
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

  **Two conditions on the firing remain, and neither is a domain clause.** `Rule.HeadScoped` —
  every head variable is the query's, a global, or the block's own `let` — is not one because
  it costs nothing: `encodeBuild` keeps a source variable as itself and the encoded query binds
  no name the source query does not, so a head variable neither the query nor a global binds
  sticks the **encoded** head too and that firing writes on neither side; what is missing is
  the lemma that says so. `hlet` is not one either: where the block's `let`s *do* shadow the
  head, the encoded block performs the same `let`s, so `entrySound_headBuild`'s own `hval` is
  stated at the wrong environment as well, and the repair is to carry the shared prefix on both
  sides rather than to restrict the source.

  These two are what `EncodedHeadSound` still has to be proved from, at the substitution
  `validQuerySubst_of_mem_matchQuery_diag` delivers — `validQuerySubst_of_mem_matchQuery`
  with `Signature.AllConstructors`, which no encoded target has, traded for
  `FDatabase.EqsRefl` and `FDatabase.IndexOk`, which every one of them has.

  It is still the mirror of `unionsJoined_fire`, a source firing behind the target's where
  that one needs a target firing behind the source's; what it is no longer is open.

**The two legality conditions are `EncodedWriteLegal` and its maintenance counterpart, and
they need a domain clause `Program.EncodeDomain` does not have.** `Program.AritiesAgree`
records it: `Program.ctors` is read off the syntax, one `(name, arity)` pair per application
and per declaration, so a program applying one name at two arities gets two table triples and
the later declaration wins — and the losing arity's rebuild rules then `set` a view at the
wrong key width, which is what `Actions.SetWidthOk` forbids and `FDatabase.Inv.execCmdM` asks
of every rule the state holds, fired or not. It is reported rather than added. The third
condition, `Signature.MergesLegal` at the encoded signature, **is** a consequence and is
proved: `encodeSig_mergesLegal`, out of `encodeSig_mergeShape` and `encodeSig_ufName`.

**No fixpoint is needed on the target.** `FDatabase.RoundClosed` was named as this residue's
third missing piece; it is not one. Soundness is indifferent to under-firing — `execM_contained`
says the encoded round fires a subset, and a subset of justified writes is justified — so what
this needs is the *containment*, not the fixpoint. The fixpoint is what `execM_viewLeaderRows`
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
an encoded program reaches with a rule, a non-leader firing and a real `@UF` edge. -/
theorem execM_soundTerms {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.SoundTerms src := by
  sorry

/-- **The completeness half's invariant at the state `execM` returned.** `execM_soundTerms` is
the residue; the step from it is `viewsSound_of_soundTerms`, whose hypothesis
`execM_encode_eqsRefl` discharges. -/
theorem execM_viewsSound {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    tgt.toDatabase.ViewsSound src ∧ tgt.toDatabase.EdgesSound src :=
  viewsSound_of_soundTerms (execM_encode_eqsRefl htgt) (execM_soundTerms hdom hsrc htgt)

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
`encode_corresponds_invents_enode` refutes the unrestricted `iff` at the witness program
`Encoding/Correspond.lean` keeps for it. -/
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) (ha : a ∈ src.terms)
    (hb : b ∈ src.terms) :
    Cong src a b ↔ SameClass tgt.toDatabase a b :=
  ⟨encode_corresponds_forward hdom hsrc htgt, encode_corresponds_complete hdom hsrc htgt ha hb⟩


end Egglog
