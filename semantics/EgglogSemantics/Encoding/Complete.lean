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

/-! ### Two side conditions the aligned run carries, and their writers

Both are clauses of `FDatabase.EncBase` below rather than run-wide theorems about the state
`execM` returns, because the rebuild firing reads them at an **intermediate** state of the run:
`rebuildRules`' e-class rule has to be a rule that state holds, and its query's variables have
to be ones the environment leaves free.

Neither is a condition on the source program. `Program.EncodeDomain.noAt` is what the second
reduces to at each emitted command, and `encodePrelude` is what supplies the first; what is
new here is only that the two are carried along the run rather than read off the source. -/

/-- **Every maintenance rule is one the state holds.** The converse of
`FDatabase.RulesEncoded`, which says only that a rule the state holds is one of the two
families. -/
def FDatabase.RulesHeld (d : FDatabase) (P : Program) : Prop :=
  ∀ r ∈ maintenanceRules P, r ∈ d.rules

/-- **A `let` whose binder is not in the generated namespace**; nothing else binds. -/
def Action.NoAtLet : Action → Prop
  | .letBind v _ => ¬ "@".isPrefixOf v
  | _ => True

/-- `Action.NoAtLet` at a command. Only a top-level action can bind: a firing runs its block
under `FDatabase.execLocalActions`, which puts the environment back. -/
def Cmd.NoAtLet : Cmd → Prop
  | .action a => a.NoAtLet
  | _ => True

/-- A `set` binds nothing, which is what the encoded blocks of a build are. -/
theorem Action.NoAtLet.of_isSet {a : Action} (h : a.IsSet) : a.NoAtLet := by
  cases a with
  | set f args out => trivial
  | expr e => exact (h : False).elim
  | letBind v e => exact (h : False).elim
  | union e₁ e₂ => exact (h : False).elim

/-- **No block an encoded action emits binds a generated variable.** The only `letBind`
`encodeAction` emits is the source `let`'s own binder, kept unchanged
(`encodeAction_letBind_actions`); every other action a build or a head emits is a `set`. -/
theorem noAtLet_encodeAction {P : Program} (hdom : P.EncodeDomain) {a : Action}
    (hc : Cmd.action a ∈ P) (n : Nat) : ∀ b ∈ (encodeAction fiatE a n).1, b.NoAtLet := by
  intro b hb
  cases a with
  | expr e =>
      rw [encodeAction_expr_actions] at hb
      exact Action.NoAtLet.of_isSet (encodeBuild_isSet e n b hb)
  | letBind v e =>
      rw [encodeAction_letBind_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · exact Action.NoAtLet.of_isSet (encodeBuild_isSet e n b h)
      · obtain rfl : b = Action.letBind v (encodeBuild e n).1 := by simpa using h
        refine hdom.noAt v ?_
        rw [Program.names]
        refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
        rw [Program.vars, List.mem_dedup]
        exact List.mem_flatMap.mpr
          ⟨Cmd.action (.letBind v e), hc, by simp [Cmd.vars, Action.vars]⟩
  | union e₁ e₂ =>
      rw [encodeAction_union_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact Action.NoAtLet.of_isSet (encodeBuild_isSet e₁ n b h')
        · exact Action.NoAtLet.of_isSet (encodeBuild_isSet e₂ _ b h')
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; trivial
  | set f args out =>
      rw [encodeAction_set_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact Action.NoAtLet.of_isSet (encodeBuildArgs_isSet args n b h')
        · exact Action.NoAtLet.of_isSet (encodeBuildArgs_isSet out _ b h')
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; trivial

@[inherit_doc noAtLet_encodeAction]
theorem noAtLet_encodeCmd {P : Program} (hdom : P.EncodeDomain) (G : List (Var × Expr))
    (c : Cmd) (hc : c ∈ P) (n i : Nat) :
    ∀ c' ∈ (encodeCmd G c n i).1, c'.NoAtLet := by
  intro c' hc'
  cases c with
  | action a =>
      rw [encodeCmd_action_fst] at hc'
      rcases List.mem_append.mp hc' with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        exact noAtLet_encodeAction hdom hc n b hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; trivial
  | rule r =>
      rw [encodeCmd_rule_fst] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl; trivial
  | run R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | decl f dc => simp [encodeCmd] at hc'

/-- **The environment binds no generated variable.** What it buys is `Query.freeVars`: a query
variable the environment already binds is not one `matchQuery` assigns, and every variable of a
maintenance rule's query is `@`-prefixed. -/
def FDatabase.NoAtEnv (d : FDatabase) : Prop := ∀ b ∈ d.env, ¬ "@".isPrefixOf b.1

namespace FDatabase

/-- **And every `Cmd.rule` of the block registers its rule.** With
`FDatabase.execProgramM_rules_mono` this is the converse of
`execProgramM_rules_of_declOrRule`: what the prelude emits, the state after it holds. -/
theorem execProgramM_mem_rules {p : Program} :
    ∀ {d D : FDatabase}, d.execProgramM p = some D → ∀ r, Cmd.rule r ∈ p → r ∈ D.rules := by
  induction p with
  | nil => intro d D _ r hr; exact absurd hr (by simp)
  | cons c cs ih =>
    intro d D hs r hr
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine execProgramM_rules_mono h₂ r ?_
      rw [FDatabase.execCmdM, Option.some.injEq] at h₁
      exact h₁ ▸ List.mem_cons_self
    · exact ih h₂ r hr'

/-- **One command keeps the environment clear of the generated namespace.** Only
`Action.letBind` writes `env`, and only with its own binder. -/
theorem execCmdM_noAtEnv {d d' : FDatabase} {c : Cmd} (hc : c.NoAtLet) (h : d.NoAtEnv)
    (hs : d.execCmdM c = some d') : d'.NoAtEnv := by
  cases c with
  | action a =>
      rw [FDatabase.execCmdM] at hs
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
      rw [NoAtEnv, (FDatabase.mergeSaturateF_fields h₂).2.1]
      cases a with
      | expr e =>
          rw [Egglog.execAction] at h₁
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h₁
          exact h
      | letBind v e =>
          rw [Egglog.execAction] at h₁
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h₁
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact hc
          · exact h b hb'
      | union e₁ e₂ =>
          rw [Egglog.execAction] at h₁
          obtain ⟨t₁, -, h₃⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨t₂, -, h₄⟩ := Option.bind_eq_some_iff.mp h₃
          split at h₄
          · exact absurd h₄ (by simp)
          · rw [Option.some.injEq] at h₄; exact h₄ ▸ h
      | set f args out =>
          rw [Egglog.execAction] at h₁
          obtain ⟨as, -, h₃⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h₃
          exact h
  | rule r =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs; exact h
  | run R =>
      rw [FDatabase.execCmdM] at hs
      rw [NoAtEnv, (FDatabase.runRoundM_fields hs).2.1]; exact h
  | saturate R =>
      rw [FDatabase.execCmdM] at hs
      rw [NoAtEnv, (FDatabase.runSaturateM_fields runFuel hs).2.1]; exact h
  | decl f dc =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs; exact h

@[inherit_doc execCmdM_noAtEnv]
theorem execProgramM_noAtEnv {p : Program} (hp : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.NoAtEnv → d.execProgramM p = some D → D.NoAtEnv := by
  induction p with
  | nil =>
    intro d D h hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro d D h hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc'))
      (execCmdM_noAtEnv (hp c List.mem_cons_self) h h₁) h₂

end FDatabase

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
  /-- **And every maintenance rule is one the state holds**, which is what lets a rebuild
  firing be exhibited rather than assumed. -/
  held : d.RulesHeld P
  /-- **And the environment binds no generated variable**, so a maintenance rule's query
  variables are all ones `matchQuery` assigns. -/
  noAtEnv : d.NoAtEnv

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
    (hwl : c.WriteLegal sg) (hlet : c.NoAtLet) (hs : d.execCmdM c = some d') :
    d'.EncBase P sg where
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
  held := fun r hr => FDatabase.execCmdM_rules_mono hs r (h.held r hr)
  noAtEnv := FDatabase.execCmdM_noAtEnv hlet h.noAtEnv hs

/-- **A block of them.** -/
theorem execProgramM {P : Program} {sg : Signature} {p : Program}
    (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal sg)
    (hlet : ∀ c ∈ p, c.NoAtLet) :
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
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (h.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self)
        h₁) h₂

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
    (∃ (s : Rule) (G : List (Var × Expr)) (i n : Nat), Cmd.rule s ∈ P ∧ s ∈ sd.rules ∧
        sd.GlobalsInline G ∧ P.GlobalsOnce G ∧ r = (encodeRule i (s.substGlobals G) n).1) ∨
      r ∈ allMaintenanceRules P

/-- The three source clauses move along a source that grows and keeps its environment. -/
theorem FDatabase.EncOk.mono_src {d : FDatabase} {P : Program} {sg : Signature}
    {sd sd' : Database} (h : d.EncOk P sg sd) (heq : sd.eqs ⊆ sd'.eqs)
    (henv : ∀ v t, Env.lookup v sd'.env = some t → Env.lookup v sd.env = some t)
    (henv' : ∀ v t, Env.lookup v sd.env = some t → Env.lookup v sd'.env = some t)
    (hsig : ∀ f, sd.sig.IsCtor f → sd'.sig.IsCtor f)
    (hrules : ∀ r ∈ sd.rules, r ∈ sd'.rules) :
    d.EncOk P sg sd' where
  base := h.base
  glob := fun v t hv => h.glob v t (henv v t hv)
  sound := h.sound.mono_src heq
  srcRules := fun r hr =>
    (h.srcRules r hr).imp
      (fun ⟨s, G, i, n, hm, hs, hg, hgo, he⟩ =>
        ⟨s, G, i, n, hm, hrules s hs, hg.mono_ctor hsig henv', hgo, he⟩) id

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
    ∀ (s : Rule) (G : List (Var × Expr)) (i n : Nat), Cmd.rule s ∈ P → s ∈ sd.rules →
      s.ruleset = R → sd.GlobalsInline G → P.GlobalsOnce G →
      (encodeRule i (s.substGlobals G) n).1 ∈ d.rules →
    ∀ σ ∈ matchQuery d (encodeRule i (s.substGlobals G) n).1.query, ∀ e : FDatabase,
      execLocalActions d (encodeRule i (s.substGlobals G) n).1.actions σ = some e →
        e.SoundTerms sd'

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
  ∀ c ∈ P, ∀ (G : List (Var × Expr)) (n i : Nat),
    ∀ c' ∈ (encodeCmd G c n i).1, c'.WriteLegal sg

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
  rcases hok.base.rules r hr with ⟨s, G, i, n, hmem, rfl⟩ | hmaint
  · exact absurd (hrs ▸ rfl : s.ruleset = rebuildRuleset) (ruleset_ne_rebuild hdom hmem)
  · exact maintenance_soundTerms (mem_maintenanceRules_of_mem_all hmaint) hok.base.eqsRefl
      hok.base.inv.index hok.base.subtermClosed hok.sound hσ he


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

/-! ### What the substitution's names are, and that the source's environment settles them

`Cmd.globalBind` adds a name only when the whole program binds it **once**, so a name the
substitution carries cannot be rebound later — which is what keeps `Database.GlobalsInline`
true as the source run goes on. The fact that pays for it is that a name the source's
environment binds is one some earlier top-level `let` bound. -/

/-- **Only a top-level `let` puts a name in the source's environment.** -/
theorem mem_letNames_of_lookup_env : ∀ {p : Program} {db sd : Database} {v : Var},
    ProgramStep db p sd → (Env.lookup v sd.env).isSome →
    v ∈ Program.letNames p ∨ (Env.lookup v db.env).isSome := by
  intro p db sd v h
  induction h with
  | nil => exact fun hlk => Or.inr hlk
  | @cons db₀ d sd' c cs hstep _ ih =>
      intro hlk
      have hsub : v ∈ Program.letNames cs → v ∈ Program.letNames (c :: cs) := by
        intro hm
        cases c <;> simp_all [Program.letNames]
      rcases ih hlk with hm | hd
      · exact Or.inl (hsub hm)
      cases hc : c with
      | action a =>
          subst hc
          obtain ⟨d₀, hreach, hcl⟩ := hstep
          have hev : evalAction db₀ a = some d₀ := hreach
          have henv : d.env = d₀.env := (MergeClosure.envRules hcl).1
          cases a with
          | letBind w e =>
              rw [evalAction] at hev
              obtain ⟨t, -, hd0⟩ := Option.map_eq_some_iff.mp hev
              by_cases hvw : v = w
              · exact Or.inl (by subst hvw; simp [Program.letNames])
              · refine Or.inr ?_
                rw [henv, ← hd0] at hd
                simpa [Env.lookup, hvw] using hd
          | expr e =>
              rw [evalAction] at hev
              obtain ⟨t, -, hd0⟩ := Option.map_eq_some_iff.mp hev
              exact Or.inr (by rw [henv, ← hd0] at hd; exact hd)
          | union e₁ e₂ =>
              refine Or.inr ?_
              rw [henv] at hd
              rw [evalAction] at hev
              obtain ⟨t₁, -, hev⟩ := Option.bind_eq_some_iff.mp hev
              obtain ⟨t₂, -, hev⟩ := Option.bind_eq_some_iff.mp hev
              by_cases hl : t₁.isLit || t₂.isLit
              · rw [if_pos hl] at hev; exact absurd hev (by simp)
              · rw [if_neg hl, Option.some.injEq] at hev
                rw [← hev] at hd
                exact hd
          | set f args out =>
              refine Or.inr ?_
              rw [henv] at hd
              rw [evalAction] at hev
              obtain ⟨as, -, hev⟩ := Option.bind_eq_some_iff.mp hev
              obtain ⟨vs, -, hd0⟩ := Option.map_eq_some_iff.mp hev
              rw [← hd0] at hd
              exact hd
      | rule r =>
          exact Or.inr (by
            rw [cmdStep_env_of_noAction (by intro a h'; exact absurd h' (by simp))
              (hc ▸ hstep)] at hd
            exact hd)
      | run R =>
          exact Or.inr (by
            rw [cmdStep_env_of_noAction (by intro a h'; exact absurd h' (by simp))
              (hc ▸ hstep)] at hd
            exact hd)
      | saturate R =>
          exact Or.inr (by
            rw [cmdStep_env_of_noAction (by intro a h'; exact absurd h' (by simp))
              (hc ▸ hstep)] at hd
            exact hd)
      | decl f dc =>
          exact Or.inr (by
            rw [cmdStep_env_of_noAction (by intro a h'; exact absurd h' (by simp))
              (hc ▸ hstep)] at hd
            exact hd)

/-- Rounds of a ruleset do not move the signature. -/
theorem runStepReach_sig {R : RulesetName} {sd d : Database}
    (h : Relation.ReflTransGen (RunStep R) sd d) : d.sig = sd.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ((MergeClosure.sig hstep).trans RunRules.sig).trans ih

/-- **The source's signature moves only at a declaration.** -/
theorem cmdStep_sig_eq_of_noDecl {sd sd' : Database} {c : Cmd}
    (hc : ∀ f d, c ≠ Cmd.decl f d) (h : CmdStep sd c sd') : sd'.sig = sd.sig := by
  obtain ⟨d, hreach, hcl⟩ := h
  refine (MergeClosure.sig hcl).trans ?_
  cases c with
  | decl f dc => exact absurd rfl (hc f dc)
  | action a =>
      replace hreach : evalAction sd a = some d := hreach
      exact evalAction_sig hreach
  | saturate R =>
      replace hreach : SaturateReach R sd d := hreach
      exact runStepReach_sig hreach.1
  | rule r =>
      replace hreach : cmdEffect sd (.rule r) = some d := hreach
      rw [cmdEffect, Option.some.injEq] at hreach; exact hreach ▸ rfl
  | run R =>
      replace hreach : cmdEffect sd (.run R) = some d := hreach
      rw [cmdEffect, Option.some.injEq] at hreach; exact hreach ▸ rfl

theorem Program.letNames_cons_action_letBind (v : Var) (e : Expr) (q : Program) :
    Program.letNames (Cmd.action (.letBind v e) :: q) = v :: Program.letNames q := rfl

theorem Program.letNames_append (p q : Program) :
    Program.letNames (p ++ q) = Program.letNames p ++ Program.letNames q := by
  rw [Program.letNames, Program.letNames, Program.letNames, List.filterMap_append]

/-- **A name the substitution carries is not the one a later `let` binds.** Two occurrences —
the one the source's environment already has, and this command's — against the guard's
"exactly once". -/
theorem lookupG_eq_none_of_letBind {P pre q : Program} {v : Var} {e : Expr}
    {sd : Database} {G : List (Var × Expr)}
    (hP : P = pre ++ Cmd.action (.letBind v e) :: q)
    (hpre : ProgramStep Database.empty pre sd) (hgi : sd.GlobalsInline G)
    (honce : P.GlobalsOnce G) : Expr.lookupG v G = none := by
  by_contra hcon
  obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.mp hcon
  obtain ⟨-, t, -, hlk⟩ := hgi v e' he'
  have hmem : v ∈ Program.letNames pre :=
    (mem_letNames_of_lookup_env hpre (by rw [hlk]; rfl)).resolve_right
      (by simp [Database.empty])
  have h1 : 0 < (Program.letNames pre).count v := List.count_pos_iff.mpr hmem
  have hcount : 2 ≤ P.letNames.count v := by
    rw [hP, Program.letNames_append, Program.letNames_cons_action_letBind, List.count_append,
      List.count_cons_self]
    omega
  have := honce v hcon
  omega

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
    (hsig : ∀ f, sd.sig.IsCtor f → sd'.sig.IsCtor f)
    (hstep : CmdStep sd c sd') : d.EncOk P sg sd' :=
  hok.mono_src (CmdStep.contained hstep).eqs
    (fun v t hv => by rw [cmdStep_env_of_noAction hc hstep] at hv; exact hv)
    (fun v t hv => by rw [cmdStep_env_of_noAction hc hstep]; exact hv) hsig
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
    rcases hok.srcRules r hr with ⟨s, G, i, n, hmem, hsr, hgi, hgo, rfl⟩ | hmaint
    · exact hhead hP hpre hc hstep hok s G i n hmem hsr hrs hgi hgo hr σ hσ e' he'
    · exact maintenance_soundTerms (mem_maintenanceRules_of_mem_all hmaint) hok.base.eqsRefl
        hok.base.inv.index hok.base.subtermClosed
        (hok.sound.mono_src (CmdStep.contained hstep).eqs) hσ he'
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · exact fun r hr => hrules ▸ hok.base.held r hr
  · exact fun b hb => hok.base.noAtEnv b (henv ▸ hb)
  · intro v t hv
    rw [henv]
    exact hok.glob v t (by rw [cmdStep_env_of_noAction hna hstep] at hv; exact hv)
  · exact runRoundM_soundTerms_in (by rw [hok.base.sig]; exact hok.base.shape)
      (by rw [hok.base.sig]; exact hok.base.merges) hok.base.inv hok.base.nounions
      hok.base.wl' hfire (hok.sound.mono_src (CmdStep.contained hstep).eqs) hrun
  · intro r hr
    have hnd : ∀ (f : FnName) (dd : FnDecl), c ≠ Cmd.decl f dd := by
      rcases hc with rfl | rfl <;> intro f dd hcon <;> exact absurd hcon (by simp)
    exact (hok.srcRules r (hrules ▸ hr)).imp
      (fun ⟨s, G, i, n, hm, hs, hgi, hgo, he⟩ =>
        ⟨s, G, i, n, hm, cmdStep_rules_subset hstep s hs,
          hgi.of_eq (cmdStep_sig_eq_of_noDecl hnd hstep)
            (cmdStep_env_of_noAction hna hstep),
          hgo, he⟩) id

/-- **A rebuild round.** No source rule joins `@rebuild`, so every firing is a maintenance
firing and the source state does not move. -/
theorem FDatabase.EncOk.runRoundM_rebuild {P : Program} (hdom : P.EncodeDomain)
    {sg : Signature} {sd : Database} {d e : FDatabase} (hok : d.EncOk P sg sd)
    (hrun : d.runRoundM rebuildRuleset = some e) : e.EncOk P sg sd := by
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hrun
  refine ⟨⟨hsig.trans hok.base.sig, ?_, hok.base.shape, hok.base.merges,
      hok.base.inv.runRoundM (by rw [hok.base.sig]; exact hok.base.merges) hok.base.wl' hrun,
      runRoundM_noUnions hok.base.nounions hrun, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun r hr => hok.base.rules r (hrules ▸ hr)
  · exact fun r hr => hok.base.wl r (hrules ▸ hr)
  · exact fun r hr => hrules ▸ hok.base.held r hr
  · exact fun b hb => hok.base.noAtEnv b (henv ▸ hb)
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
    runFuel (hok.step_src (by intro a h; exact absurd h (by simp))
      (by rw [cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep]
          exact fun _ h => h) hstep) hrun



/-! ## One aligned command, and the induction over the run

`encodeCmds` maps one source command to a block, and `encodeCmd`'s five cases are five
shapes of block: nothing for a declaration, one `Cmd.rule` for a rule, a round or a
saturation followed by a rebuild for the two firing commands, and the action block followed
by a rebuild for a top-level action. The induction below is over that alignment, carrying
`FDatabase.EncOk` at the **contemporaneous** source state, and it lifts to the run's final
source only at the last step. -/

/-- `encodeCmd` emits no declaration, which is what fixes the signature for the whole
aligned run. -/
theorem noDecl_encodeCmd (G : List (Var × Expr)) (c : Cmd) (n i : Nat) :
    ∀ c' ∈ (encodeCmd G c n i).1, c'.NoDecl := by
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
      have h : c' ∈ [Cmd.rule (encodeRule i (r.substGlobals G) n).1] := hc'
      obtain rfl : c' = Cmd.rule (encodeRule i (r.substGlobals G) n).1 := by simpa using h
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

mutual

/-- **`Expr.inlineGlobals` computes what the source's environment already says.** The stored
definitions are closed and agree with the environment, so replacing a name by its definition
changes nothing the source evaluates. -/
theorem Expr.eval_inlineGlobals {sd : Database} {G : List (Var × Expr)}
    (hG : sd.GlobalsInline G) :
    ∀ e : Expr, (e.inlineGlobals G).eval sd.sig sd.env = e.eval sd.sig sd.env
  | .lit _ => rfl
  | .var v => by
      rw [Expr.inlineGlobals]
      cases hlk : Expr.lookupG v G with
      | none => simp only [Option.getD]
      | some e =>
          obtain ⟨hcl, t, hev, hbind⟩ := hG v e hlk
          simp only [Option.getD]
          rw [Expr.eval_of_vars_nil hcl, hev, Expr.eval, hbind]
  | .app f args => by
      rw [Expr.inlineGlobals, Expr.eval, Expr.eval, Expr.evalList_inlineGlobals hG args]

@[inherit_doc Expr.eval_inlineGlobals]
theorem Expr.evalList_inlineGlobals {sd : Database} {G : List (Var × Expr)}
    (hG : sd.GlobalsInline G) :
    ∀ es : List Expr, Expr.evalList sd.sig (Expr.inlineGlobalsList G es) sd.env
      = Expr.evalList sd.sig es sd.env
  | [] => rfl
  | e :: es => by
      rw [Expr.inlineGlobalsList, Expr.evalList_cons, Expr.evalList_cons,
        Expr.eval_inlineGlobals hG e, Expr.evalList_inlineGlobals hG es]

end

/-- **A top-level action keeps `Database.GlobalsInline` at the globals already carried.** The
`let` case is the only one with content, and `lookupG_eq_none_of_letBind` is what pays it: the
name this `let` binds is not one the substitution carries, because the program binds a carried
name once and the source's environment already holds it. -/
theorem globalsInline_action {P pre q : Program} {a : Action} {sd sd' : Database}
    {G : List (Var × Expr)} (hP : P = pre ++ Cmd.action a :: q)
    (hpre : ProgramStep Database.empty pre sd) (hstep : CmdStep sd (.action a) sd')
    (hgi : sd.GlobalsInline G) (honce : P.GlobalsOnce G) : sd'.GlobalsInline G := by
  have hsig : sd'.sig = sd.sig :=
    cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep
  obtain ⟨d₀, hreach, hcl⟩ := hstep
  have hev : evalAction sd a = some d₀ := hreach
  have henv : sd'.env = d₀.env := (MergeClosure.envRules hcl).1
  cases a with
  | expr e =>
      rw [evalAction] at hev
      obtain ⟨t, -, hd0⟩ := Option.map_eq_some_iff.mp hev
      exact hgi.of_eq hsig (by rw [henv, ← hd0]; rfl)
  | union e₁ e₂ =>
      refine hgi.of_eq hsig ?_
      rw [evalAction] at hev
      obtain ⟨t₁, -, hev⟩ := Option.bind_eq_some_iff.mp hev
      obtain ⟨t₂, -, hev⟩ := Option.bind_eq_some_iff.mp hev
      by_cases hl : t₁.isLit || t₂.isLit
      · rw [if_pos hl] at hev; exact absurd hev (by simp)
      · rw [if_neg hl, Option.some.injEq] at hev
        rw [henv, ← hev]; rfl
  | set f args out =>
      refine hgi.of_eq hsig ?_
      rw [evalAction] at hev
      obtain ⟨as, -, hev⟩ := Option.bind_eq_some_iff.mp hev
      obtain ⟨vs, -, hd0⟩ := Option.map_eq_some_iff.mp hev
      rw [henv, ← hd0]; rfl
  | letBind v e =>
      rw [evalAction] at hev
      obtain ⟨t, ht, hd0⟩ := Option.map_eq_some_iff.mp hev
      have hnone : Expr.lookupG v G = none := lookupG_eq_none_of_letBind hP hpre hgi honce
      have henv' : sd'.env = (v, t) :: sd.env := by rw [henv, ← hd0]
      intro w e' hw
      have hwv : w ≠ v := by
        intro hcon; rw [hcon, hnone] at hw; exact absurd hw (by simp)
      obtain ⟨hcl', t', hev', hbind'⟩ := hgi w e' hw
      exact ⟨hcl', t', by rw [hsig]; exact hev',
        by rw [henv']; simpa [Env.lookup, hwv] using hbind'⟩

/-- **The two clauses survive one source command**, at the globals `Cmd.globalBind` leaves.

The `let` case is the only one with content, and its two halves are the two guards: the name is
bound once in `P`, so no name already carried is the one this `let` moves
(`lookupG_eq_none_of_letBind`), and the stored definition is closed, so it means at the new
state what it meant at the old. -/
theorem globalsInline_step {P : Program} (hdom : P.EncodeDomain) {pre q : Program} {c : Cmd}
    (hP : P = pre ++ c :: q) {sd sd' : Database} (hstate : sd.CtorState)
    (hpre : ProgramStep Database.empty pre sd) (hstep : CmdStep sd c sd')
    {G : List (Var × Expr)} (hgi : sd.GlobalsInline G) (honce : P.GlobalsOnce G) :
    sd'.GlobalsInline (c.globalBind P G) ∧ P.GlobalsOnce (c.globalBind P G) := by
  have hcP : c ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
  cases hc : c with
  | decl f dc =>
      subst hc
      obtain ⟨-, henv, -⟩ := cmdStep_decl_fields hstate.sig (hdom.ctorsOnly _ hcP) hstep
      refine ⟨?_, honce⟩
      refine hgi.mono_ctor ?_ (fun v t hv => by rw [henv]; exact hv)
      intro g hg
      obtain ⟨d, hd, hm⟩ := hg
      obtain ⟨d₀, hreach, hcl⟩ := hstep
      have hd0 : some { sd with sig := Function.update sd.sig f (some dc) } = some d₀ := hreach
      have hsig' : sd'.sig = Function.update sd.sig f (some dc) := by
        rw [MergeClosure.sig hcl, ← Option.some.inj hd0]
      by_cases hgf : g = f
      · subst hgf
        exact ⟨dc, by rw [hsig', Function.update_self], (hdom.ctorsOnly _ hcP : dc.merge = none)⟩
      · exact ⟨d, by rw [hsig', Function.update_of_ne hgf]; exact hd, hm⟩
  | rule r =>
      subst hc
      refine ⟨hgi.of_eq (cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep)
        (cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep), honce⟩
  | run R =>
      subst hc
      refine ⟨hgi.of_eq (cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep)
        (cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep), honce⟩
  | saturate R =>
      subst hc
      refine ⟨hgi.of_eq (cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep)
        (cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep), honce⟩
  | action a =>
      subst hc
      have hkeep : sd'.GlobalsInline G := globalsInline_action hP hpre hstep hgi honce
      have hsig : sd'.sig = sd.sig :=
        cmdStep_sig_eq_of_noDecl (by intro f d h; exact absurd h (by simp)) hstep
      obtain ⟨d₀, hreach, hcl⟩ := hstep
      have hev : evalAction sd a = some d₀ := hreach
      have henv : sd'.env = d₀.env := (MergeClosure.envRules hcl).1
      cases a with
      | expr e => exact ⟨hkeep, honce⟩
      | union e₁ e₂ => exact ⟨hkeep, honce⟩
      | set f args out => exact ⟨hkeep, honce⟩
      | letBind v e =>
          rw [evalAction] at hev
          obtain ⟨t, ht, hd0⟩ := Option.map_eq_some_iff.mp hev
          have henv' : sd'.env = (v, t) :: sd.env := by rw [henv, ← hd0]
          rw [Cmd.globalBind]
          by_cases hg : P.letNames.count v = 1 ∧ (e.inlineGlobals G).vars = []
          · rw [if_pos hg]
            refine ⟨?_, ?_⟩
            · intro w e' hw
              rw [Expr.lookupG] at hw
              by_cases hwv : w = v
              · subst hwv
                rw [if_pos rfl, Option.some.injEq] at hw
                subst hw
                refine ⟨hg.2, t, ?_, by rw [henv']; simp [Env.lookup]⟩
                rw [hsig, ← Expr.eval_of_vars_nil hg.2 sd.env, Expr.eval_inlineGlobals hgi e]
                exact ht
              · rw [if_neg hwv] at hw
                exact hkeep w e' hw
            · intro w hw
              rw [Expr.lookupG] at hw
              by_cases hwv : w = v
              · subst hwv; exact hg.1
              · rw [if_neg hwv] at hw; exact honce w hw
          · rw [if_neg hg]
            exact ⟨hkeep, honce⟩

/-- **One aligned command.** The five cases of `encodeCmd`, each carrying
`FDatabase.EncOk` from the source command's pre-state to its post-state. -/
theorem FDatabase.EncOk.stepCmd {P : Program} (hdom : P.EncodeDomain) {sg : Signature}
    (hhead : EncodedHeadSound P sg) (hact : EncodedActionSound P sg)
    (hwlP : EncodedWriteLegal P sg) {pre q : Program} {c : Cmd} (hP : P = pre ++ c :: q)
    {sd sd' : Database} (hpre : ProgramStep Database.empty pre sd)
    (hstep : CmdStep sd c sd') {G : List (Var × Expr)} {n i : Nat} {d D : FDatabase}
    (hgi : sd.GlobalsInline G) (honce : P.GlobalsOnce G) (hok : d.EncOk P sg sd)
    (hrun : d.execProgramM (encodeCmd G c n i).1 = some D) : D.EncOk P sg sd' := by
  have hcP : c ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
  have hbase : ∀ {c' : Cmd} {x y : FDatabase}, c' ∈ (encodeCmd G c n i).1 →
      Cmd.RulesEncodedOk P c' → x.EncBase P sg → x.execCmdM c' = some y → y.EncBase P sg :=
    fun hmem hro hb hs =>
      hb.execCmdM hro (encodeCmd_unionFree G c n i _ hmem) (noDecl_encodeCmd G c n i _ hmem)
        (hwlP c hcP G n i _ hmem) (noAtLet_encodeCmd hdom G c hcP n i _ hmem) hs
  cases hc : c with
  | decl f dc =>
    subst hc
    have hnil : d.execProgramM ([] : Program) = some D := hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hnil
    subst hnil
    obtain ⟨-, henv, -⟩ := cmdStep_decl_fields (hpre.ctorState Database.CtorState.empty
      (fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc'))).sig
      (hdom.ctorsOnly _ hcP) hstep
    refine hok.step_src (by intro a h; exact absurd h (by simp)) ?_ hstep
    intro g hg
    obtain ⟨dd, hdd, hm⟩ := hg
    obtain ⟨d₀, hreach, hcl⟩ := hstep
    have hd0 : some { sd with sig := Function.update sd.sig f (some dc) } = some d₀ := hreach
    have hsig' : sd'.sig = Function.update sd.sig f (some dc) := by
      rw [MergeClosure.sig hcl, ← Option.some.inj hd0]
    by_cases hgf : g = f
    · subst hgf
      exact ⟨dc, by rw [hsig', Function.update_self], (hdom.ctorsOnly _ hcP : dc.merge = none)⟩
    · exact ⟨dd, by rw [hsig', Function.update_of_ne hgf]; exact hdd, hm⟩
  | rule r =>
    subst hc
    have hrun' : d.execProgramM [Cmd.rule (encodeRule i (r.substGlobals G) n).1] = some D := hrun
    have hs : d.execCmdM (Cmd.rule (encodeRule i (r.substGlobals G) n).1) = some D :=
      execProgramM_single hrun'
    have hmem : Cmd.rule r ∈ P := by rw [hP]; exact List.mem_append_right _ List.mem_cons_self
    have hmem' : Cmd.rule (encodeRule i (r.substGlobals G) n).1
        ∈ (encodeCmd G (Cmd.rule r) n i).1 := List.mem_cons_self
    have hb : D.EncBase P sg :=
      hbase hmem' (Or.inl ⟨r, G, i, n, hmem, rfl⟩) hok.base hs
    obtain rfl : D = { d with rules := (encodeRule i (r.substGlobals G) n).1 :: d.rules } := by
      rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs.symm
    have hsigeq : sd'.sig = sd.sig :=
      cmdStep_sig_eq_of_noDecl (by intro f dd h; exact absurd h (by simp)) hstep
    have henveq : sd'.env = sd.env :=
      cmdStep_env_of_noAction (by intro a h; exact absurd h (by simp)) hstep
    refine ⟨hb, ?_, hok.sound.mono_src (CmdStep.contained hstep).eqs, ?_⟩
    · intro v t hv
      rw [henveq] at hv
      exact hok.glob v t hv
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr''
      · exact Or.inl ⟨r, G, i, n, hmem, cmdStep_rule_mem hstep,
          hgi.of_eq hsigeq henveq, honce, rfl⟩
      · exact (hok.srcRules r' hr'').imp
          (fun ⟨s, H, j, m, hm, hs', hgi', hgo', he⟩ =>
            ⟨s, H, j, m, hm, cmdStep_rules_subset hstep s hs',
              hgi'.of_eq hsigeq henveq, hgo', he⟩) id
  | run R =>
    subst hc
    have hrun' : d.execProgramM [Cmd.run R, Cmd.saturate rebuildRuleset] = some D := hrun
    obtain ⟨d₁, h₁, h₂⟩ := execProgramM_pair hrun'
    have hok₁ : d₁.EncOk P sg sd' :=
      hok.runRoundM hhead hP hpre (Or.inl rfl) hstep (by rw [FDatabase.execCmdM] at h₁; exact h₁)
    exact hok₁.saturate_rebuild hdom h₂
  | saturate R =>
    subst hc
    have hrun' : d.execProgramM [Cmd.saturate R, Cmd.saturate rebuildRuleset] = some D := hrun
    obtain ⟨d₁, h₁, h₂⟩ := execProgramM_pair hrun'
    exact (hok.saturate_src hhead hP hpre hstep h₁).saturate_rebuild hdom h₂
  | action a =>
    subst hc
    have hrun' : d.execProgramM ((encodeAction fiatE a n).1.map Cmd.action ++
        [Cmd.saturate rebuildRuleset]) = some D := hrun
    obtain ⟨D₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun'
    have hb₁ : D₁.EncBase P sg := by
      refine FDatabase.EncBase.execProgramM (P := P) (sg := sg) ?_ ?_ ?_ ?_ ?_ hok.base hblock
      all_goals
        intro c' hc'
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
        have hmem : Cmd.action b ∈ (encodeCmd G (Cmd.action a) n i).1 :=
          List.mem_append_left _ (List.mem_map_of_mem hb)
      · trivial
      · exact encodeCmd_unionFree G (Cmd.action a) n i _ hmem
      · exact noDecl_encodeCmd G (Cmd.action a) n i _ hmem
      · exact hwlP (Cmd.action a) hcP G n i _ hmem
      · exact noAtLet_encodeCmd hdom G (Cmd.action a) hcP n i _ hmem
    exact (hact hP hpre hstep hok hblock hb₁).saturate_rebuild hdom (execProgramM_single hafter)

/-- **The per-command induction.** `FDatabase.EncOk` at the state the target run has reached
and the source state the source run has reached, carried command by command along the
alignment `encodeCmds` sets up.

This is the shape the residue needed, and the reason it cannot be a single application of
`firingsSound_of_rulesEncoded`: the head's reading is at the contemporaneous source state
and its conclusion at that command's post-state, so the invariant reaches the run's final
source only at the end, by `FDatabase.SoundTerms.mono_src`.

The globals the encoder carries are threaded alongside, and `globalsInline_step` is what keeps
their two clauses true as the source run goes on. -/
theorem FDatabase.EncOk.stepCmds {P : Program} (hdom : P.EncodeDomain) {sg : Signature}
    (hhead : EncodedHeadSound P sg) (hact : EncodedActionSound P sg)
    (hwlP : EncodedWriteLegal P sg) :
    ∀ (p pre : Program), P = pre ++ p →
      ∀ {sd src : Database}, ProgramStep Database.empty pre sd → ProgramStep sd p src →
      ∀ (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase},
        sd.GlobalsInline G → P.GlobalsOnce G → d.EncOk P sg sd →
        d.execProgramM (encodeCmds P G p n i).1 = some D → D.EncOk P sg src := by
  intro p
  induction p with
  | nil =>
    intro pre _ sd src _ hsrc G n i d D _ _ hok hrun
    obtain rfl : sd = src := ProgramStep.nil_inv hsrc
    have hnil : d.execProgramM ([] : Program) = some D := hrun
    rw [FDatabase.execProgramM, Option.some.injEq] at hnil
    exact hnil ▸ hok
  | cons c cs ih =>
    intro pre hP sd src hpre hsrc G n i d D hgi honce hok hrun
    obtain ⟨sd', hstep, hrest⟩ := ProgramStep.cons_inv hsrc
    rw [encodeCmds_cons_fst] at hrun
    obtain ⟨d₁, hblock, hafter⟩ := FDatabase.execProgramM_append hrun
    have hstate : sd.CtorState :=
      hpre.ctorState Database.CtorState.empty
        (fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc'))
    obtain ⟨hgi', honce'⟩ := globalsInline_step hdom hP hstate hpre hstep hgi honce
    exact ih (pre ++ [c]) (by rw [List.append_assoc]; exact hP)
      (hpre.append (ProgramStep.cons hstep ProgramStep.nil)) hrest _ _ _ hgi' honce'
      (hok.stepCmd hdom hhead hact hwlP hP hpre hstep hgi honce hblock) hafter


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
  have hproof : ∀ (R : Program) (G : List (Var × Expr)) (p : Program) (i : Nat),
      ∀ c ∈ ruleProofDecls R G p i, Cmd.DeclOrRule c := by
    intro R G p
    induction p generalizing G with
    | nil => intro i c hc; simp [ruleProofDecls] at hc
    | cons c₀ cs ih =>
      intro i c hc
      rw [ruleProofDecls] at hc
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨r, -, rfl⟩ := mem_proofDeclOf h
        trivial
      · exact ih _ _ c h
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
      · exact hproof _ _ _ _ c h₂
    · rcases List.mem_cons.mp h₁ with rfl | h₂
      · trivial
      · obtain ⟨fk, -, h₃⟩ := List.mem_flatMap.mp h₂
        have h₄ : c = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            c = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            c = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₃
        rcases h₄ with rfl | rfl | rfl <;> trivial
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
    trivial

/-- The prelude declares and registers rules, and neither binds. -/
theorem NoAtLet.of_declOrRule {c : Cmd} (h : c.DeclOrRule) : c.NoAtLet := by
  cases c with
  | decl f dc => trivial
  | rule r => trivial
  | action a => exact (h : False).elim
  | run R => exact (h : False).elim
  | saturate R => exact (h : False).elim

/-- Every rule a prelude command registers is a maintenance rule. -/
theorem mem_maintenanceRules_of_encodePrelude {P : Program} {r : Rule}
    (h : Cmd.rule r ∈ encodePrelude P) : r ∈ allMaintenanceRules P := by
  have hproof : ∀ (R : Program) (G : List (Var × Expr)) (p : Program) (i : Nat),
      Cmd.rule r ∉ ruleProofDecls R G p i := by
    intro R G p
    induction p generalizing G with
    | nil => intro i hc; simp [ruleProofDecls] at hc
    | cons c cs ih =>
      intro i hc
      rw [ruleProofDecls] at hc
      rcases List.mem_append.mp hc with h | h
      · obtain ⟨s, -, hcon⟩ := mem_proofDeclOf h
        exact absurd hcon (by simp)
      · exact ih _ _ h
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
      · exact hproof _ _ _ _ h₃
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
        empty_noUnions hprel, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact FDatabase.execProgramM_rulesEncoded (rulesEncodedOk_encodePrelude P)
      (fun r hr => absurd hr (by simp [FDatabase.empty])) hprel
  · rw [← hsig]
    exact FDatabase.execProgramM_mergeShape (mergeShapeOk_encodePrelude P)
      Signature.mergeShape_empty hprel
  · intro r hr
    rcases execProgramM_rules_of_declOrRule hprel r hr with hc | hc
    · exact hmaint { r with ruleset := rebuildRuleset }
        (mem_maintenanceRules_of_mem_all (mem_maintenanceRules_of_encodePrelude hc))
    · exact absurd hc (by simp [FDatabase.empty])
  · exact fun r hr => FDatabase.execProgramM_mem_rules hprel r
      (by rw [encodePrelude]
          exact List.mem_append_right _
            (List.mem_map_of_mem (mem_allMaintenanceRules_of_mem hr)))
  · intro b hb
    rw [hv, show FDatabase.empty.env = ([] : Env) from rfl] at hb
    exact absurd hb (by simp)
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
  exact (FDatabase.EncOk.stepCmds hdom hhead hact hwlP P [] rfl ProgramStep.nil hsrc [] 0 0
    (by intro v e he; exact absurd he (by simp [Expr.lookupG]))
    (by intro v he; exact absurd he (by simp [Expr.lookupG]))
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
  intro c hcP G n i c' hc'
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
    have h : c' ∈ [Cmd.rule (encodeRule i (r.substGlobals G) n).1] := hc'
    obtain rfl : c' = Cmd.rule (encodeRule i (r.substGlobals G) n).1 := by simpa using h
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
        ⟨(hwl b List.mem_cons_self).1.1, (hwl b List.mem_cons_self).2.1⟩
        (Action.NoAtLet.of_isSet hbset) h₂c
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
      (∃ (s : Rule) (G : List (Var × Expr)) (i n : Nat), Cmd.rule s ∈ P ∧ s ∈ sd'.rules ∧
          sd'.GlobalsInline G ∧ P.GlobalsOnce G ∧
          r = (encodeRule i (s.substGlobals G) n).1) ∨
        r ∈ allMaintenanceRules P := by
    intro r hr
    have hnr : Cmd.rule r ∉ (encodeAction fiatE a n).1.map Cmd.action := by
      intro hc
      obtain ⟨b, -, hb⟩ := List.mem_map.mp hc
      exact absurd hb (by simp)
    rcases hok.srcRules r ((execProgramM_rules_of_declOrRule hblock r hr).resolve_left hnr) with
      ⟨s, G, i, m, hm, hs, hgi, hgo, he⟩ | hmaint
    · exact Or.inl ⟨s, G, i, m, hm, cmdStep_rules_subset hstep s hs,
        globalsInline_action hP hpre hstep hgi hgo, hgo, he⟩
    · exact Or.inr hmaint
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

/-! ## Descent, run-wide

**`FDatabase.UFRowsDescend` at the state `execM` returned, proved.** The state-level halves are
`Encoding/Correspond.lean`'s — the three writers, the firing fold, the merge pass and the merge
phase — and what is left here is the run: the prelude, whose state holds **no row at all**, and
then `encodeCmds`' blocks carried command by command against `FDatabase.EncBase`.

Unlike `execM_soundTerms` this owes nothing to a source-rule head: descent is a condition on
the `@UF` writes an action *syntactically* performs (`Action.UFWriteSafe`), and the one write
that is not syntactic — `pathCompressRule`'s — reads only the rows its own query matched. So
the induction needs neither `EncodedHeadSound` nor `Program.HeadsScoped`, and the only clause
beyond the domain it spends is `Program.AritiesAgree`, and that solely to inhabit
`FDatabase.EncBase` at the prelude (`encOk_preludeState`).

`hufsg` is the one fact about the signature the argument cannot do without: `@UF` has to carry
a `:merge`, or `patternHolds` would read a path-compression premise out of `terms` — where
superseded edges live forever — instead of out of `rows`. `encodeSig_ufName` is it discharged
at the prelude's own signature. -/

/-- **Whether a command can write an `@UF` row the invariant would have to check.** Only a
top-level action can; a `.rule`, a `.run` and a `.saturate` write through `d.rules`, which
`FDatabase.RulesEncoded` covers, and a `.decl` writes no data. -/
def Cmd.UFWriteOk : Cmd → Prop
  | .action a => a.UFWriteSafe
  | _ => True

/-- The `@UF` declaration, as the merge-function test the row-valued reading needs. -/
theorem encodeSig_mergeOf_ufName {P : Program} (hdom : P.EncodeDomain) :
    (encodeSig P).mergeOf ufName ≠ none := by
  rw [Signature.mergeOf, encodeSig_ufName hdom]
  exact fun hc => absurd hc (by simp [ufDecl])

/-- **Rounds of one ruleset descend**, given the bundle at each round's own start. -/
theorem FDatabase.EncBase.runSaturateM_ufRowsDescend {P : Program} {sg : Signature}
    (hufsg : sg.mergeOf ufName ≠ none) {R : RulesetName} :
    ∀ (n : Nat) {d d' : FDatabase}, d.EncBase P sg → d.UFRowsDescend →
      d.runSaturateM R n = some d' → d'.UFRowsDescend := by
  intro n d d' hb hdes hrun
  refine (runSaturateM_closed (R := R) (Φ := fun x => x.EncBase P sg ∧ x.UFRowsDescend)
    ?_ n ⟨hb, hdes⟩ hrun).2
  intro x y hx hstep
  have hstep' : x.execCmdM (Cmd.run R) = some y := hstep
  refine ⟨hx.1.execCmdM (c := Cmd.run R) trivial trivial trivial trivial trivial hstep', ?_⟩
  refine runRoundM_ufRowsDescend (by rw [hx.1.sig]; exact hx.1.shape)
    (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl' ?_ hx.2 hstep
  exact firingsUFDescend_of_rulesEncoded hx.1.rules hx.1.eqsRefl
    (by rw [hx.1.sig]; exact hufsg) hx.2

/-- **One command of the aligned run.** The same five side conditions
`FDatabase.EncBase.execCmdM` takes, plus the one about `@UF` writes. -/
theorem FDatabase.EncBase.execCmdM_ufRowsDescend {P : Program} {sg : Signature}
    (hufsg : sg.mergeOf ufName ≠ none) {d d' : FDatabase} {c : Cmd} (hb : d.EncBase P sg)
    (huf : c.UnionFree) (hnd : c.NoDecl) (hwl : c.WriteLegal sg) (hok : c.UFWriteOk)
    (hdes : d.UFRowsDescend) (hs : d.execCmdM c = some d') : d'.UFRowsDescend := by
  have hmg : d.sig.mergeOf ufName ≠ none := by rw [hb.sig]; exact hufsg
  have hfire : d.FiringsUFDescend :=
    firingsUFDescend_of_rulesEncoded hb.rules hb.eqsRefl hmg hdes
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine mergeSaturateF_ufRowsDescend mergeFuel ?_ ?_ ?_ ?_
      (execAction_ufRowsDescend hok hdes h₁) h₂
    · rw [FDatabase.execAction_sig h₁, hb.sig]; exact hb.shape
    · rw [FDatabase.execAction_sig h₁, hb.sig]; exact hb.merges
    · exact hb.inv.execAction (by rw [hb.sig]; exact hwl) h₁
    · exact execAction_noUnions huf hb.nounions h₁
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ hdes.mono fun _ hr => hr
  | run R =>
    rw [FDatabase.execCmdM] at hs
    exact runRoundM_ufRowsDescend (by rw [hb.sig]; exact hb.shape)
      (by rw [hb.sig]; exact hb.merges) hb.inv hb.nounions hb.wl' hfire hdes hs
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact FDatabase.EncBase.runSaturateM_ufRowsDescend hufsg runFuel hb hdes hs
  | decl f dc => exact (hnd : False).elim

/-- **A block of them.** -/
theorem FDatabase.EncBase.execProgramM_ufRowsDescend {P : Program} {sg : Signature}
    (hufsg : sg.mergeOf ufName ≠ none) {p : Program}
    (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal sg) (hok : ∀ c ∈ p, c.UFWriteOk)
    (hlet : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.EncBase P sg → d.UFRowsDescend → d.execProgramM p = some D →
      D.UFRowsDescend := by
  induction p with
  | nil =>
    intro d D _ hdes hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hdes
  | cons c cs ih =>
    intro d D hb hdes hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hok c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (hb.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self) h₁)
      (hb.execCmdM_ufRowsDescend hufsg (huf c List.mem_cons_self) (hnd c List.mem_cons_self)
        (hwl c List.mem_cons_self) (hok c List.mem_cons_self) hdes h₁) h₂

/-- **A command of `encodeCmds`' output is a command of some `encodeCmd`'s**, which is what
lets the per-command read-backs stated over `encodeCmd` be applied along the block. -/
theorem mem_encodeCmd_of_mem_encodeCmds {P R : Program} :
    ∀ (p : Program), (∀ c ∈ p, c ∈ P) →
    ∀ (G : List (Var × Expr)) (n i : Nat), ∀ c' ∈ (encodeCmds R G p n i).1,
      ∃ c, c ∈ P ∧ ∃ (H : List (Var × Expr)) (m j : Nat), c' ∈ (encodeCmd H c m j).1
  | [], _, _, _, _ => by simp [encodeCmds]
  | c :: cs, hp, G, n, i => by
      intro c' hc'
      rw [encodeCmds_cons_fst] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact ⟨c, hp c List.mem_cons_self, G, n, i, h⟩
      · exact mem_encodeCmd_of_mem_encodeCmds cs
          (fun x hx => hp x (List.mem_cons_of_mem c hx)) _ _ _ c' h

/-- **The `union` head is the only `set` at `@UF` a block emits.** -/
theorem ufWriteOk_encodeCmd (G : List (Var × Expr)) (c : Cmd) (n i : Nat) :
    ∀ c' ∈ (encodeCmd G c n i).1, c'.UFWriteOk := by
  intro c' hc'
  cases c with
  | action a =>
      rw [encodeCmd_action_fst] at hc'
      rcases List.mem_append.mp hc' with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        exact encodeAction_ufWriteSafe fiatE a n b hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; trivial
  | rule r =>
      rw [encodeCmd_rule_fst] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl; trivial
  | run R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | decl f dc => simp [encodeCmd] at hc'

/-- **`FDatabase.UFRowsDescend` at the state `execM` returned.** Every live `@UF` row of an
encoded run's target runs `ordering-max ↦ ordering-min`, so `FDatabase.exists_ufRowRoot` applies
there: every id reaches a point with no outgoing row, along a path that strictly descends
`Term.blt` inside a finite list.

**This is one of the two hypotheses the rebuild residue's forest argument rests on**, and it is
now a theorem rather than a hypothesis. What is still a hypothesis is
`FDatabase.UFRowsForest` — one outgoing edge per key — which is the merge fixpoint at `@UF`'s
own table and wants a lexicographic measure, since `mergeBody` writes into `@UF` and the
per-key count there can grow inside the very pass that shrinks a view key's
(`FDatabase.mergeRound_countP_lt` is the view half). -/
theorem execM_encode_ufRowsDescend {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.UFRowsDescend := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  have hdes₀ : d₀.UFRowsDescend := by
    have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
    refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
    exact absurd hmem (by simp)
  refine FDatabase.EncBase.execProgramM_ufRowsDescend (encodeSig_mergeOf_ufName hdom)
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hdes₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact ufWriteOk_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **Descent with the arity clause spelled out.** `Program.EncodeDomain` implies it
(`Program.EncodeDomain.aritiesAgree'`); it is named here for the same reason the completeness
half names it. -/
theorem execM_ufRowsDescend {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.UFRowsDescend :=
  execM_encode_ufRowsDescend hdom hdom.aritiesAgree' htgt

/-- **Every id of an encoded target reaches an `@UF` row root**, with no hypothesis about the
state left over: `FDatabase.exists_ufRowRoot` at `execM_ufRowsDescend`. Uniqueness of that root
is `FDatabase.ufRowRoot_unique` and still wants `FDatabase.UFRowsForest`. -/
theorem execM_exists_ufRowRoot {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) (a : Term) :
    ∃ r, tgt.UFRowReach a r ∧ tgt.UFRowRoot r :=
  FDatabase.exists_ufRowRoot (execM_ufRowsDescend hdom htgt) a


/-! ## The forest, run-wide

`FDatabase.ufRowsForest_of_settled` is a statement about a merge **fixpoint**, and every
command of an encoded run but one ends at a fixpoint: `Cmd.action` and `Cmd.run` end in
`FDatabase.mergeSaturateF`, and `Cmd.saturate` returns either the state it started at or a
round's output, which is one. The exception is `Cmd.rule`, which writes no row at all — so the
clause is carried across it rather than re-established, and that is why the induction carries
`FDatabase.UFRowsForest` itself instead of `FDatabase.settled`.

`hsy` and `htr` are the side condition `mergeOneWith_isSome_of_collide` records: `mergeBody`
mints `@Trans (@Sym _) _`, so a signature that does not declare those two heads leaves every
collision standing at what would otherwise be a fixpoint. The prelude's `proofDecls` declares
both; they are hypotheses here for the same reason they are hypotheses there. -/

/-- **The forest clause at a merge fixpoint of an encoded run**, with everything but the
fixpoint read off `FDatabase.EncBase`. -/
theorem FDatabase.EncBase.ufRowsForest {P : Program} {sg : Signature}
    (hufsg : sg ufName = some ufDecl) (hsy : sg.IsCtor symName) (htr : sg.IsCtor transName)
    {d : FDatabase} (hb : d.EncBase P sg) (hdes : d.UFRowsDescend) (hset : d.settled = true) :
    d.UFRowsForest :=
  FDatabase.ufRowsForest_of_settled hset (by rw [hb.sig]; exact hb.shape)
    (by rw [hb.sig]; exact hb.merges) hb.inv (fun p hp => diag_closureF hb.eqsRefl hp)
    (by rw [hb.sig]; exact hsy) (by rw [hb.sig]; exact htr)
    (by rw [hb.sig]; exact hufsg) rfl hdes
    (rowArgs_mem_closureF hb.eqsRefl hb.inv.index hb.subtermClosed)

/-- **Rounds of one ruleset keep the forest**: each round ends in a merge phase, and the
alternative the fixpoint test takes is the state the rounds started at. -/
theorem FDatabase.EncBase.runSaturateM_ufRowsForest {P : Program} {sg : Signature}
    (hufsg : sg ufName = some ufDecl) (hsy : sg.IsCtor symName) (htr : sg.IsCtor transName)
    {R : RulesetName} :
    ∀ (n : Nat) {d d' : FDatabase}, d.EncBase P sg → d.UFRowsDescend → d.UFRowsForest →
      d.runSaturateM R n = some d' → d'.UFRowsForest := by
  intro n d d' hb hdes hfor hrun
  have hufsgne : sg.mergeOf ufName ≠ none := by
    rw [Signature.mergeOf, hufsg]; simp [ufDecl]
  refine (runSaturateM_closed (R := R)
    (Φ := fun x => x.EncBase P sg ∧ x.UFRowsDescend ∧ x.UFRowsForest) ?_ n
    ⟨hb, hdes, hfor⟩ hrun).2.2
  intro x y hx hstep
  have hstep' : x.execCmdM (Cmd.run R) = some y := hstep
  have hby : y.EncBase P sg :=
    hx.1.execCmdM (c := Cmd.run R) trivial trivial trivial trivial trivial hstep'
  have hdesy : y.UFRowsDescend := by
    refine runRoundM_ufRowsDescend (by rw [hx.1.sig]; exact hx.1.shape)
      (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl' ?_ hx.2.1 hstep
    exact firingsUFDescend_of_rulesEncoded hx.1.rules hx.1.eqsRefl
      (by rw [hx.1.sig]; exact hufsgne) hx.2.1
  refine ⟨hby, hdesy, ?_⟩
  rw [FDatabase.runRoundM] at hstep
  exact FDatabase.EncBase.ufRowsForest hufsg hsy htr hby hdesy
    (FDatabase.mergeSaturateF_settled mergeFuel hstep)

/-- **One command of the aligned run keeps the forest.** -/
theorem FDatabase.EncBase.execCmdM_ufRowsForest {P : Program} {sg : Signature}
    (hufsg : sg ufName = some ufDecl) (hsy : sg.IsCtor symName) (htr : sg.IsCtor transName)
    {d d' : FDatabase} {c : Cmd} (hb : d.EncBase P sg)
    (huf : c.UnionFree) (hnd : c.NoDecl) (hwl : c.WriteLegal sg) (hok : c.UFWriteOk)
    (hlet : c.NoAtLet)
    (hdes : d.UFRowsDescend) (hfor : d.UFRowsForest) (hs : d.execCmdM c = some d') :
    d'.UFRowsForest := by
  have hufsgne : sg.mergeOf ufName ≠ none := by
    rw [Signature.mergeOf, hufsg]; simp [ufDecl]
  have hbd' : ∀ (hro : Cmd.RulesEncodedOk P c), d'.EncBase P sg := fun hro =>
    hb.execCmdM hro huf hnd hwl hlet hs
  have hdes' : d'.UFRowsDescend :=
    hb.execCmdM_ufRowsDescend hufsgne huf hnd hwl hok hdes hs
  cases c with
  | action a =>
    have hb' : d'.EncBase P sg := hbd' trivial
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, -, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact FDatabase.EncBase.ufRowsForest hufsg hsy htr hb' hdes'
      (FDatabase.mergeSaturateF_settled mergeFuel h₂)
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ (show ({ d with rules := r :: d.rules } : FDatabase).UFRowsForest from hfor)
  | run R =>
    have hb' : d'.EncBase P sg := hbd' trivial
    rw [FDatabase.execCmdM, FDatabase.runRoundM] at hs
    exact FDatabase.EncBase.ufRowsForest hufsg hsy htr hb' hdes'
      (FDatabase.mergeSaturateF_settled mergeFuel hs)
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact FDatabase.EncBase.runSaturateM_ufRowsForest hufsg hsy htr runFuel hb hdes hfor hs
  | decl f dc => exact (hnd : False).elim

/-- **A block of them.** -/
theorem FDatabase.EncBase.execProgramM_ufRowsForest {P : Program} {sg : Signature}
    (hufsg : sg ufName = some ufDecl) (hsy : sg.IsCtor symName) (htr : sg.IsCtor transName)
    {p : Program} (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal sg) (hok : ∀ c ∈ p, c.UFWriteOk)
    (hlet : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.EncBase P sg → d.UFRowsDescend → d.UFRowsForest →
      d.execProgramM p = some D → D.UFRowsForest := by
  have hufsgne : sg.mergeOf ufName ≠ none := by
    rw [Signature.mergeOf, hufsg]; simp [ufDecl]
  induction p with
  | nil =>
    intro d D _ _ hfor hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hfor
  | cons c cs ih =>
    intro d D hb hdes hfor hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hok c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (hb.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self) h₁)
      (hb.execCmdM_ufRowsDescend hufsgne (huf c List.mem_cons_self) (hnd c List.mem_cons_self)
        (hwl c List.mem_cons_self) (hok c List.mem_cons_self) hdes h₁)
      (hb.execCmdM_ufRowsForest hufsg hsy htr (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hok c List.mem_cons_self)
        (hlet c List.mem_cons_self) hdes hfor h₁) h₂

/-- **`FDatabase.UFRowsForest` at the state `execM` returned.** Together with
`execM_ufRowsDescend` this is both hypotheses of the rebuild residue's forest argument, so
`FDatabase.exists_ufRowRoot` and `FDatabase.ufRowRoot_unique` apply at an encoded target
outright: every id reaches an `@UF` row root, and the root is unique. -/
theorem execM_encode_ufRowsForest {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.UFRowsForest := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
  have hdes₀ : d₀.UFRowsDescend := by
    refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
    exact absurd hmem (by simp)
  have hfor₀ : d₀.UFRowsForest := by
    intro a b c hb _
    obtain ⟨pf, hmem⟩ := hb.1
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
    exact absurd hmem (by simp)
  refine FDatabase.EncBase.execProgramM_ufRowsForest (encodeSig_ufName hdom) hsy htr
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hdes₀ hfor₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact ufWriteOk_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **Every id of an encoded target has a unique `@UF` row root.** `exists_ufRowRoot` and
`ufRowRoot_unique` at `execM_ufRowsDescend` and `execM_encode_ufRowsForest`: the two hypotheses
the rebuild residue's forest argument was left waiting on, both discharged. -/
theorem execM_ufRowRoot_unique {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) (a : Term) :
    ∃ r, tgt.UFRowReach a r ∧ tgt.UFRowRoot r ∧
      ∀ s, tgt.UFRowReach a s → tgt.UFRowRoot s → s = r := by
  obtain ⟨r, hr, hrr⟩ := FDatabase.exists_ufRowRoot (execM_ufRowsDescend hdom htgt) a
  exact ⟨r, hr, hrr, fun s hs hsr =>
    FDatabase.ufRowRoot_unique
      (execM_encode_ufRowsForest hdom hdom.aritiesAgree' hsy htr htgt) hs hsr hr hrr⟩

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
  intro pre q hP sd sd' hpre R c hc hstep d hok s G i n hmem hsrule hrs hgi hgo hrd σ hσ e he
  have hstate : sd.CtorState :=
    hpre.ctorState Database.CtorState.empty
      fun c' hc' => hdom.ctorsOnly c' (by rw [hP]; exact List.mem_append_left _ hc')
  have hwf' : sd'.WF := hstep.wf hstate.wf
  obtain ⟨hgr₀, hnv₀, hk₀⟩ := hdom.queryEncodable_of_mem hmem
  -- the three text conditions, at the query the encoder actually flattened
  set q' : Query := Query.substGlobals G s.query with hq'
  have hgr : ∀ p ∈ q', p.Grounded := Query.grounded_substGlobals hgr₀
  have hnv : ∀ p ∈ q', p.NoValues := Query.noValues_substGlobals hnv₀
  have hk : Query.VarsKeyed q' := Query.VarsKeyed.substGlobals hgi.closed hk₀
  obtain ⟨hbld, hun⟩ := head_facts_of_domain hdom hP hpre hmem hsrule
  have hscoped : s.HeadScoped sd := hhs.headScoped hmem sd
  have htb : sd.TermsBuild := termsBuild_of_programStep hdom hP hpre
  have hvs : d.toDatabase.ViewsSound sd :=
    (viewsSound_of_soundTerms hok.base.eqsRefl hok.sound).1
  obtain ⟨τ', hmatch, hagree⟩ := validQuerySubst_of_mem_matchQuery_diag hok.base.inv.eqs
    hok.base.eqsRefl hok.base.inv.index hσ
  have hglobτ : sd.GlobalsAgree (d.toDatabase.env ++ τ') := hok.glob.append
  have hread : ∀ p ∈ q', PatternRead d.toDatabase (d.toDatabase.env ++ τ') p :=
    patternReads_of_encodeQuery hok.base.diag hok.base.subterms hnv hk hmatch
  obtain ⟨τ, hqτ', hτ⟩ := exists_validQuerySubst_at_ids htb hvs hglobτ hgr hk hread
  -- and the source's own query is matched at the same substitution
  have hqτ : ValidQuerySubst sd s.query τ := ValidQuerySubst.of_substGlobals hgi hqτ'
  obtain ⟨D, hD, hlocal⟩ := evalLocalActions_isSome_of_builds (Scope.Models.dom sd.env)
    hstate.wf hscoped hbld hun hqτ
  -- the target's block
  rw [execLocalActions, encodeRule_actions] at he
  obtain ⟨e₀, he₀, hee⟩ := Option.map_eq_some_iff.mp he
  have hgoal : e₀.SoundTerms sd' := by
    refine headActions_soundTerms (dk := { d with env := d.env ++ σ })
      (ss := { sd with env := sd.env ++ τ }) hdom hag hwf'
      (notEntryHead_ruleE (queryProofs_var (encodeQuery_valueVars q' hnv n)))
      s.actions (Query.bind s.query (Env.dom sd.env)) (encodeQuery q' n).2
      (fun a ha fk hfk => mem_ctors_of_cmd hmem (by
        rw [Cmd.ctors]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hfk⟩)))
      ((Program.setLegal_iff_noSet (fun _ => rfl) hdom.ctorsOnly).mp hdom.setLegal _ hmem)
      hscoped ?_ hok.base.sig (hok.base.inv.setEnvMatch hσ)
      (hok.sound.mono_src (CmdStep.contained hstep).eqs) hD ?_ ?_ he₀
    · intro v hv
      have hv' : v ∈ Query.vars q' ∨ (Env.lookup v sd.env).isSome := by
        rcases List.mem_union_iff.mp hv with hv' | hv'
        · exact Or.inr (Env.lookup_isSome_iff_mem_dom.mpr hv')
        · by_cases hvq : v ∈ Query.vars q'
          · exact Or.inl hvq
          · -- a query variable the substitution replaced is a global, so the environment
            -- binds it
            refine Or.inr ?_
            obtain ⟨e', hlk⟩ := Option.ne_none_iff_exists'.mp
              (Query.lookupG_ne_none_of_not_mem_vars_substGlobals hgi.closed hv' hvq)
            obtain ⟨-, t, -, hbind⟩ := hgi v e' hlk
            rw [hbind]; rfl
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
`DiffTest.lean`'s census: the clause moved nothing when it was added, 70 of 166 in domain
then and 83 of 179 now. -/

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
The census was unmoved when it was added: 70 of 166 in domain, as before it.

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

/-! ### The two proof heads are really declared

`ENCODING.md`'s discipline at a hypothesis: `execM_encode_ufRowsForest` carries `hsy` and `htr`
for the reason `mergeOneWith_isSome_of_collide` does — a signature that does not declare `@Sym`
and `@Trans` leaves every collision standing at what would otherwise be a fixpoint, and the
forest is then false. They are not vacuous: the prelude of any in-domain program declares both,
and at `ncProgram` — the program whose rule really fires — that reduces in the kernel. -/

set_option maxRecDepth 100000 in
/-- `ncProgram`'s prelude declares `@Sym`. -/
theorem ncProgram_isCtor_symName : (encodeSig ncProgram).IsCtor symName := by decide

set_option maxRecDepth 100000 in
@[inherit_doc ncProgram_isCtor_symName]
theorem ncProgram_isCtor_transName : (encodeSig ncProgram).IsCtor transName := by decide

/-- **Every hypothesis of `execM_encode_ufRowsForest` holding together**, at a program whose
rule really fires. -/
theorem execM_ufRowsForest_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) : tgt.UFRowsForest :=
  execM_encode_ufRowsForest ncProgram_encodeDomain ncProgram_encodeDomain.aritiesAgree'
    ncProgram_isCtor_symName ncProgram_isCtor_transName htgt

@[inherit_doc execM_ufRowsForest_witness]
theorem execM_ufRowRoot_unique_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) (a : Term) :
    ∃ r, tgt.UFRowReach a r ∧ tgt.UFRowRoot r ∧
      ∀ s, tgt.UFRowReach a s → tgt.UFRowRoot s → s = r :=
  execM_ufRowRoot_unique ncProgram_encodeDomain ncProgram_isCtor_symName
    ncProgram_isCtor_transName htgt a

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


/-! ## The bridge, run-wide

**`FDatabase.EntryRowsUF` at the state `execM` returned.** The state-level halves are
`Encoding/Correspond.lean`'s — the four writers, the firing fold, the merge pass and the merge
phase — and what is left here is the run: the prelude, whose state holds no term at all, and
then `encodeCmds`' blocks carried command by command against `FDatabase.EncBase`.

Like `execM_ufRowsDescend` and unlike `execM_soundTerms`, this owes nothing to a source rule's
head. `Action.EntrySafe` is a condition on the *heads a block applies*, and the only thing the
domain is spent on is that a source constructor is not in the generated namespace
(`notEntryHead_of_mem_ctors`) — so neither `EncodedHeadSound` nor `Program.HeadsScoped` enters,
and the whole obligation at a rule firing is syntactic in its actions. -/

/-- **A name outside the generated namespace heads no entry term.** Both shapes are `@`-prefixed
(`isPrefixOf_at_viewName`), which is what makes the primitive heads a `union` compiles to free. -/
theorem notEntryHead_of_not_at {g : FnName} (h : ¬ "@".isPrefixOf g = true) : NotEntryHead g :=
  ⟨fun f hf => h (hf ▸ isPrefixOf_at_viewName f),
    fun hf => h (hf ▸ (by decide +kernel : "@".isPrefixOf ufName = true))⟩

/-- The two primitives `maxE` and `minE` compile to. -/
theorem notEntryHead_ifName : NotEntryHead "if" := notEntryHead_of_not_at (by decide +kernel)

@[inherit_doc notEntryHead_ifName]
theorem notEntryHead_gtName : NotEntryHead "ordering-gt" :=
  notEntryHead_of_not_at (by decide +kernel)

/-- `@Fiat` heads no entry term, and it is the only head a build's proof column carries. -/
theorem notEntryHead_fiatE : ∀ g ∈ fiatE.fns, NotEntryHead g := by
  intro g hg
  have hg2 : g = fiatName := by simpa [fiatE, Expr.fns, Expr.fnsList] using hg
  exact hg2 ▸ notEntryHead_fiatName

/-- **The two `set`s a build emits for one application are entry-safe.** Their operands are the
application's own naming expressions, which `encodeBuild_fst` says are the source's. -/
theorem entrySafe_buildSets {f : FnName} {args : List Expr} (hf : NotEntryHead f)
    (hargs : ∀ g ∈ Expr.fnsList args, NotEntryHead g) {a : Action}
    (h : a = Action.set (termName f) (args ++ [.app f args]) [] ∨
      a = Action.set (viewName f) args [.app f args, fiatE]) : a.EntrySafe := by
  have hel : ∀ b ∈ args, ∀ g ∈ b.fns, NotEntryHead g :=
    fun b hb g hg => hargs g (mem_fnsList_of_mem hb g hg)
  have happ : ∀ g ∈ (Expr.app f args).fns, NotEntryHead g := by
    intro g hg
    rw [Expr.fns, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact hf
    · exact hargs g hg
  rcases h with rfl | rfl
  · refine ⟨notEntryHead_fnsList (fun b hb => ?_), fun g hg => by simp [Expr.fnsList] at hg⟩
    rcases List.mem_append.mp hb with hb' | hb'
    · exact hel b hb'
    · obtain rfl : b = Expr.app f args := by simpa using hb'
      exact happ
  · refine ⟨notEntryHead_fnsList hel, notEntryHead_fnsList (fun b hb => ?_)⟩
    have hb2 : b = Expr.app f args ∨ b = fiatE := by simpa using hb
    rcases hb2 with rfl | rfl
    · exact happ
    · exact notEntryHead_fiatE

/-- **A build's block is entry-safe**, given that no head the built expression applies is an
entry head. -/
theorem encodeBuild_entrySafe {e : Expr} (hne : ∀ g ∈ e.fns, NotEntryHead g) (m : Nat) :
    ∀ a ∈ (encodeBuild e m).2.1, a.EntrySafe := by
  intro a ha
  obtain ⟨f, args, hfa, hshape⟩ := mem_encodeBuild_actions e m a ha
  obtain ⟨hfmem, hfargs⟩ := fns_of_mem_apps e hfa
  exact entrySafe_buildSets (hne f hfmem) (fun g hg => hne g (hfargs g hg)) hshape

@[inherit_doc encodeBuild_entrySafe]
theorem encodeBuildArgs_entrySafe {es : List Expr}
    (hne : ∀ g ∈ Expr.fnsList es, NotEntryHead g) (m : Nat) :
    ∀ a ∈ (encodeBuildArgs es m).2.1, a.EntrySafe := by
  intro a ha
  obtain ⟨f, args, hfa, hshape⟩ := mem_encodeBuildArgs_actions es m a ha
  obtain ⟨hfmem, hfargs⟩ := fnsList_of_mem_appsList es hfa
  exact entrySafe_buildSets (hne f hfmem) (fun g hg => hne g (hfargs g hg)) hshape

/-- **The `union` head is entry-safe.** `ordering-max`, `ordering-min` and the conditional they
compile to are primitives, and a primitive's name is not `@`-prefixed. -/
theorem entrySafe_unionHead {x y pf : Expr} (hx : ∀ g ∈ x.fns, NotEntryHead g)
    (hy : ∀ g ∈ y.fns, NotEntryHead g) (hpf : ∀ g ∈ pf.fns, NotEntryHead g) :
    (Action.set ufName [maxE x y] [minE x y, pf]).EntrySafe := by
  have hgt : ∀ (a b : Expr), (∀ g ∈ a.fns, NotEntryHead g) → (∀ g ∈ b.fns, NotEntryHead g) →
      ∀ g ∈ (gtE a b).fns, NotEntryHead g := by
    intro a b ha hb g hg
    rw [gtE, Expr.fns, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact notEntryHead_gtName
    · refine notEntryHead_fnsList (fun z hz => ?_) g hg
      have hz2 : z = a ∨ z = b := by simpa using hz
      rcases hz2 with rfl | rfl
      exacts [ha, hb]
  have hif : ∀ (a b c : Expr), (∀ g ∈ a.fns, NotEntryHead g) → (∀ g ∈ b.fns, NotEntryHead g) →
      (∀ g ∈ c.fns, NotEntryHead g) → ∀ g ∈ (ifE a b c).fns, NotEntryHead g := by
    intro a b c ha hb hc g hg
    rw [ifE, Expr.fns, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact notEntryHead_ifName
    · refine notEntryHead_fnsList (fun z hz => ?_) g hg
      have hz2 : z = a ∨ z = b ∨ z = c := by simpa using hz
      rcases hz2 with rfl | rfl | rfl
      exacts [ha, hb, hc]
  refine ⟨notEntryHead_fnsList (fun z hz => ?_), notEntryHead_fnsList (fun z hz => ?_)⟩
  · obtain rfl : z = maxE x y := by simpa using hz
    exact hif _ _ _ (hgt x y hx hy) hx hy
  · have hz2 : z = minE x y ∨ z = pf := by simpa using hz
    rcases hz2 with rfl | rfl
    · exact hif _ _ _ (hgt x y hx hy) hy hx
    · exact hpf

/-- **One source action's block is entry-safe.** The domain is spent once, on
`notEntryHead_of_mem_ctors`: a source constructor is not in the generated namespace. -/
theorem encodeAction_entrySafe {P : Program} (hdom : P.EncodeDomain) {pf : Expr}
    (hpf : ∀ g ∈ pf.fns, NotEntryHead g) {a : Action}
    (hctors : ∀ fk ∈ a.ctors, fk ∈ P.ctors) (m : Nat) :
    ∀ b ∈ (encodeAction pf a m).1, b.EntrySafe := by
  cases a with
  | expr e =>
    intro b hb
    exact encodeBuild_entrySafe (head_conditions_of_ctors hdom hctors).1 m b
      (encodeAction_expr_actions .. ▸ hb)
  | letBind v e =>
    intro b hb
    have hne : ∀ g ∈ e.fns, NotEntryHead g := (head_conditions_of_ctors hdom hctors).1
    rw [encodeAction_letBind_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · exact encodeBuild_entrySafe hne m b h
    · obtain rfl : b = Action.letBind v (encodeBuild e m).1 := by simpa using h
      rw [encodeBuild_fst]
      exact hne
  | union e₁ e₂ =>
    intro b hb
    have hc₁ : ∀ fk ∈ e₁.ctors, fk ∈ P.ctors :=
      fun fk hfk => hctors fk (by rw [Action.ctors]; exact List.mem_append_left _ hfk)
    have hc₂ : ∀ fk ∈ e₂.ctors, fk ∈ P.ctors :=
      fun fk hfk => hctors fk (by rw [Action.ctors]; exact List.mem_append_right _ hfk)
    have hne₁ : ∀ g ∈ e₁.fns, NotEntryHead g := (head_conditions_of_ctors hdom hc₁).1
    have hne₂ : ∀ g ∈ e₂.fns, NotEntryHead g := (head_conditions_of_ctors hdom hc₂).1
    rw [encodeAction_union_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact encodeBuild_entrySafe hne₁ m b h'
      · exact encodeBuild_entrySafe hne₂ _ b h'
    · obtain rfl : b = Action.set ufName
          [maxE (encodeBuild e₁ m).1 (encodeBuild e₂ (encodeBuild e₁ m).2.2).1]
          [minE (encodeBuild e₁ m).1 (encodeBuild e₂ (encodeBuild e₁ m).2.2).1, pf] := by
        simpa using h
      rw [encodeBuild_fst, encodeBuild_fst]
      exact entrySafe_unionHead hne₁ hne₂ hpf
  | set f args out =>
    intro b hb
    have hc₁ : ∀ g ∈ Expr.fnsList args, NotEntryHead g := by
      intro g hg
      obtain ⟨k, hk⟩ := exists_ctor_of_mem_fnsList args hg
      exact notEntryHead_of_mem_ctors (fk := (g, k)) hdom (hctors _ (by
        rw [Action.ctors]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hk)))
    have hc₂ : ∀ g ∈ Expr.fnsList out, NotEntryHead g := by
      intro g hg
      obtain ⟨k, hk⟩ := exists_ctor_of_mem_fnsList out hg
      exact notEntryHead_of_mem_ctors (fk := (g, k)) hdom (hctors _ (by
        rw [Action.ctors]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hk)))
    rw [encodeAction_set_actions] at hb
    rcases List.mem_append.mp hb with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact encodeBuildArgs_entrySafe hc₁ m b h'
      · exact encodeBuildArgs_entrySafe hc₂ _ b h'
    · obtain rfl : b = Action.set (viewName f) (encodeBuildArgs args m).1
          ((encodeBuildArgs out (encodeBuildArgs args m).2.2).1 ++ [pf]) := by simpa using h
      rw [encodeBuildArgs_fst, encodeBuildArgs_fst]
      refine ⟨hc₁, notEntryHead_fnsList (fun z hz => ?_)⟩
      rcases List.mem_append.mp hz with hz' | hz'
      · exact fun g hg => hc₂ g (mem_fnsList_of_mem hz' g hg)
      · obtain rfl : z = pf := by simpa using hz'
        exact hpf

@[inherit_doc encodeAction_entrySafe]
theorem encodeActions_entrySafe {P : Program} (hdom : P.EncodeDomain) {pf : Expr}
    (hpf : ∀ g ∈ pf.fns, NotEntryHead g) : ∀ (as : List Action),
    (∀ a ∈ as, ∀ fk ∈ a.ctors, fk ∈ P.ctors) → ∀ (m : Nat),
      ∀ b ∈ (encodeActions pf as m).1, b.EntrySafe
  | [], _, _ => by simp [encodeActions]
  | a :: as, hc, m => by
      intro b hb
      rw [encodeActions_cons_actions] at hb
      rcases List.mem_append.mp hb with h | h
      · exact encodeAction_entrySafe hdom hpf (hc a List.mem_cons_self) m b h
      · exact encodeActions_entrySafe hdom hpf as
          (fun x hx => hc x (List.mem_cons_of_mem _ hx)) _ b h

/-- **An encoded source rule's head is entry-safe.** Its proof column is `@Rule_i` over the
query's proof variables (`notEntryHead_ruleE`); everything else is the source's own vocabulary. -/
theorem encodeRule_entrySafe {P : Program} (hdom : P.EncodeDomain) {s : Rule}
    (hmem : Cmd.rule s ∈ P) (G : List (Var × Expr)) (i n : Nat) :
    ∀ a ∈ (encodeRule i (s.substGlobals G) n).1.actions, a.EntrySafe := by
  obtain ⟨-, hnv, -⟩ := hdom.queryEncodable_of_mem hmem
  rw [encodeRule_actions]
  refine encodeActions_entrySafe hdom
    (notEntryHead_ruleE (queryProofs_var
      (encodeQuery_valueVars (Query.substGlobals G s.query)
        (Query.noValues_substGlobals hnv) n))) (s.substGlobals G).actions
    (fun a ha fk hfk => ?_) _
  exact mem_ctors_of_cmd hmem (by
    rw [Cmd.ctors]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hfk⟩))

/-- **Every firing of an encoded target keeps the bridge**, whether it is a source rule's or a
maintenance rule's. Unlike `firingsSound_of_rulesEncoded` this owes nothing: both families are
discharged, the first by `encodeRule_entrySafe` and the second by `maintenance_entrySafe`. -/
theorem FDatabase.EncBase.firingsEntryRows {P : Program} (hdom : P.EncodeDomain)
    {d : FDatabase} (hb : d.EncBase P (encodeSig P)) (h : d.EntryRowsUF) :
    d.FiringsEntryRows := by
  intro r hrm σ hσ e he
  have hshape : Signature.MergeShape d.sig := by rw [hb.sig]; exact encodeSig_mergeShape P
  refine execLocalActions_entryRowsUF hshape hb.inv (hb.wl' r hrm) ?_
    (mem_terms_of_mem_matchQuery hσ) h he
  rcases hb.rules r hrm with ⟨s, G, i, n, hmem, rfl⟩ | hmaint
  · exact encodeRule_entrySafe hdom hmem G i n
  · exact maintenance_entrySafe (r := { r with ruleset := rebuildRuleset })
      (mem_maintenanceRules_of_mem_all hmaint)

/-- **Whether a command can record an entry term the bridge would have to answer for.** Only a
top-level action can; a `.rule`, a `.run` and a `.saturate` write through `d.rules`, which
`FDatabase.RulesEncoded` covers, and a `.decl` writes no data. -/
def Cmd.EntryWriteOk : Cmd → Prop
  | .action a => a.EntrySafe
  | _ => True

/-- **Every action an encoded block emits is entry-safe.** -/
theorem entryWriteOk_encodeCmd {P : Program} (hdom : P.EncodeDomain) (G : List (Var × Expr))
    (c : Cmd) (hc : c ∈ P) (n i : Nat) :
    ∀ c' ∈ (encodeCmd G c n i).1, c'.EntryWriteOk := by
  intro c' hc'
  cases c with
  | action a =>
      rw [encodeCmd_action_fst] at hc'
      rcases List.mem_append.mp hc' with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        exact encodeAction_entrySafe hdom notEntryHead_fiatE
          (fun fk hfk => mem_ctors_of_cmd hc hfk) n b hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; trivial
  | rule r =>
      rw [encodeCmd_rule_fst] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl; trivial
  | run R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> trivial
  | decl f dc => simp [encodeCmd] at hc'

/-- **Rounds of one ruleset keep the bridge.** -/
theorem FDatabase.EncBase.runSaturateM_entryRowsUF {P : Program} (hdom : P.EncodeDomain)
    {R : RulesetName} :
    ∀ (n : Nat) {d d' : FDatabase}, d.EncBase P (encodeSig P) → d.EntryRowsUF →
      d.runSaturateM R n = some d' → d'.EntryRowsUF := by
  intro n d d' hb h hrun
  refine (runSaturateM_closed (R := R)
    (Φ := fun x => x.EncBase P (encodeSig P) ∧ x.EntryRowsUF) ?_ n ⟨hb, h⟩ hrun).2
  intro x y hx hstep
  have hstep' : x.execCmdM (Cmd.run R) = some y := hstep
  refine ⟨hx.1.execCmdM (c := Cmd.run R) trivial trivial trivial trivial trivial hstep', ?_⟩
  exact runRoundM_entryRowsUF (by rw [hx.1.sig]; exact hx.1.shape)
    (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl'
    (FDatabase.EncBase.firingsEntryRows hdom hx.1 hx.2) hx.2 hstep

/-- **One command of the aligned run keeps the bridge.** -/
theorem FDatabase.EncBase.execCmdM_entryRowsUF {P : Program} (hdom : P.EncodeDomain)
    {d d' : FDatabase} {c : Cmd} (hb : d.EncBase P (encodeSig P))
    (huf : c.UnionFree) (hnd : c.NoDecl) (hwl : c.WriteLegal (encodeSig P))
    (hok : c.EntryWriteOk) (h : d.EntryRowsUF) (hs : d.execCmdM c = some d') :
    d'.EntryRowsUF := by
  have hshape : Signature.MergeShape d.sig := by rw [hb.sig]; exact hb.shape
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    have hsig₁ : d₁.sig = d.sig := FDatabase.execAction_sig h₁
    refine mergeSaturateF_entryRowsUF mergeFuel ?_ ?_ ?_ ?_
      (execAction_entryRowsUF hshape hb.inv hok (by rw [hb.sig]; exact hwl) h h₁) h₂
    · rw [hsig₁]; exact hshape
    · rw [hsig₁, hb.sig]; exact hb.merges
    · exact hb.inv.execAction (by rw [hb.sig]; exact hwl) h₁
    · exact execAction_noUnions huf hb.nounions h₁
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.setEnvRules d.env (r :: d.rules)
  | run R =>
    rw [FDatabase.execCmdM] at hs
    exact runRoundM_entryRowsUF hshape (by rw [hb.sig]; exact hb.merges) hb.inv hb.nounions
      hb.wl' (FDatabase.EncBase.firingsEntryRows hdom hb h) h hs
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact FDatabase.EncBase.runSaturateM_entryRowsUF hdom runFuel hb h hs
  | decl f dc => exact (hnd : False).elim

/-- **A block of them.** -/
theorem FDatabase.EncBase.execProgramM_entryRowsUF {P : Program} (hdom : P.EncodeDomain)
    {p : Program} (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal (encodeSig P))
    (hok : ∀ c ∈ p, c.EntryWriteOk) (hlet : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.EncBase P (encodeSig P) → d.EntryRowsUF →
      d.execProgramM p = some D → D.EntryRowsUF := by
  induction p with
  | nil =>
    intro d D _ h hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro d D hb h hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hok c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (hb.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self) h₁)
      (hb.execCmdM_entryRowsUF hdom (huf c List.mem_cons_self) (hnd c List.mem_cons_self)
        (hwl c List.mem_cons_self) (hok c List.mem_cons_self) h h₁) h₂

/-- **The bridge at the state `execM` returned: every merge-function entry term the target holds
has a row at its own key whose e-class column the union-find reaches from the entry's.**

This is what the three clauses of `Database.RebuildClosed` were left waiting on, and it is now
a theorem rather than a hypothesis. `FDatabase.IndexCurrent` is the same claim without the
`Database.UFReach` and is refuted (`cxTgt_not_indexCurrent`); `cxTgt_currentUF` is the compiled
instance of what survives.

The arity clause is named for the same reason the completeness half names it: only the prelude's
`FDatabase.EncBase` spends it. -/
theorem execM_encode_entryRowsUF {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.EntryRowsUF := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  have h₀ : d₀.EntryRowsUF := by
    have hterms := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).1
    intro f dc hdc body res hm as x pf hlen hmem
    rw [hterms, show FDatabase.empty.terms = ([] : List Term) from rfl] at hmem
    exact absurd hmem (by simp)
  refine FDatabase.EncBase.execProgramM_entryRowsUF hdom
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ h₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact entryWriteOk_encodeCmd hdom H c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **The bridge, with the arity clause read off the domain.** -/
theorem execM_entryRowsUF {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.EntryRowsUF :=
  execM_encode_entryRowsUF hdom hdom.aritiesAgree' htgt

/-- **The bridge as `Database.Out` reads it**, which is the form the rebuild residue's three
clauses consume: an entry term the target's *denotation* holds is answered by a live row at the
same key, up to the union-find. -/
theorem execM_entryRow_of_out {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) {f : FnName} {dc : FnDecl}
    (hdc : tgt.sig f = some dc) {body : List Action} {res : List Expr}
    (hm : dc.merge = some (MergeSpec.merge body res)) {as : List Term} {x pf : Term}
    (hlen : as.length = dc.arity) (ho : tgt.toDatabase.Out f as [x, pf]) :
    ∃ v lo, (⟨f, as, [v, lo]⟩ : Row) ∈ tgt.rows ∧ tgt.toDatabase.UFReach x v :=
  (execM_entryRowsUF hdom htgt).out (execM_encode_eqsRefl htgt) hdc hm hlen ho


/-! ## The fixpoint's roots, reduced to the firing

The residue's second obligation is that at a rebuild fixpoint no surviving view row's e-class
column has an outgoing `@UF` row — `FDatabase.UFRowEdge`, so a self-loop, which `(union a a)`
really does write, is not one. The argument is four facts:

* the e-class rule **fires** there, at the view row and the `@UF` row: its conclusion is a row
  of the round's rule phase. This is `eclassRule_fires`;
* the round's **merge phase** then leaves a row at that key whose e-class column is
  `Term.blt`-at or below the one the firing wrote — `mergeResult`'s `ordering-min`, carried
  across a pass and across `FDatabase.mergeSaturateF` (`mergeSaturateF_rowsDescendCarry`);
* `FDatabase.RowsClosed` says the round's row list is the state's back, and
  `FDatabase.row_unique_of_settled` says a settled state carries at most one row per view key —
  so that row *is* the one the fixpoint started with, and its e-class column is therefore at or
  below the one the `@UF` row points at;
* `FDatabase.UFRowsDescend` says the `@UF` row points strictly *below*, and `Term.blt_asymm`
  closes it.

**What the firing cost, and what is left of it.** Four things, three of them now paid:
`matchQuery` completeness in general form (`mem_matchQuery_of_lookup`, which names
`Query.freeVars`' order and composes `Env.canon` with itself), the **converse** of
`FDatabase.RulesEncoded` (`FDatabase.EncBase.held`, that the maintenance rules are rules the
target *holds*), and that the target's environment binds no `@`-prefixed variable
(`FDatabase.EncBase.noAtEnv`, `Program.EncodeDomain.noAt` carried along the run), so that
`Query.freeVars` is the whole of the query's variables. The fourth is the one still open:
placing the columns in `FDatabase.valueTerms`, which `FDatabase.RowColumnsValued` names and
`execM_rowColumnsValued` discharges run-wide, by a per-command induction of
`FDatabase.EntryRowsUF`'s shape over the same writers. -/

/-! ### `matchQuery` completeness in general form, and the e-class rule's own firing

The residue's second obligation asks the e-class rebuild rule to have **fired**, and the kernel
cannot run `matchQuery`: `closureF` is well-founded-recursive and so irreducible, which is why
`cxRb_mem_matchQuery` is *proved* rather than decided. What follows is that one instance at an
arbitrary constructor and arity.

* `mem_matchQuery_of_lookup` is `matchQuery` completeness in general form. The enumerator lists
  `assignments` over `FDatabase.valueTerms` **in `Query.freeVars`' own order**, so a substitution
  offered to it has to be `Env.canon`-shaped there; and it checks each atom at the substitution
  restricted to that atom, so the two restrictions have to compose — `Env.canon_canon`, at
  `Query.freeVars_subset` and `Query.freeVars_nodup`.
* `patternHolds_values_of_mem_rows` is what makes each atom hold, at a row's own columns, with
  no congruence closure asked of the kernel.
* `FDatabase.EncBase.noAtEnv` is what makes the query's variables **free**: `Query.freeVars`
  drops a variable the environment already binds, and every variable a maintenance rule mentions
  is `@`-prefixed. `Program.EncodeDomain.noAt` is where that starts and
  `FDatabase.execCmdM_noAtEnv` is what carries it along the run.
* `FDatabase.EncBase.held` is what makes the rule one the state runs — the converse of
  `FDatabase.RulesEncoded`, which says only that a rule the state holds is one of the two
  families.

`rebuildVars`' key variables have to be **distinct**, or the head would not write the row's own
key back, and that is `Nat`'s decimal representation being injective (`toString_nat_inj`, off
core's `Nat.ofDigitChars_toDigits`). It is a real side condition and not bookkeeping: a rule
whose key pattern repeated a variable would match only the rows whose two columns agree.

**One state property is left over**, `FDatabase.RowColumnsValued`: `matchQuery` assigns from
`FDatabase.valueTerms` and not from `terms`, so a rule can only re-read a row whose columns are
of that kind. It is not carried by `FDatabase.EncBase`; `execM_rowColumnsValued`, two blocks
below, is it run-wide. -/

theorem toString_nat_inj {i j : Nat} (h : toString i = toString j) : i = j := by
  have hd : Nat.toDigits 10 i = Nat.toDigits 10 j := by
    rw [← Nat.toList_repr, ← Nat.toList_repr, ← Nat.toString_eq_repr, ← Nat.toString_eq_repr, h]
  have hi := Nat.ofDigitChars_toDigits (b := 10) (n := i) (by decide) (by decide)
  rw [hd, Nat.ofDigitChars_toDigits (by decide) (by decide)] at hi
  exact hi.symm

def rebuildVarNames (k : Nat) : List Var := (List.range k).map fun i => "@c" ++ toString i

theorem rebuildVars_eq_map (k : Nat) : rebuildVars k = (rebuildVarNames k).map Expr.var := by
  rw [rebuildVars, rebuildVarNames, List.map_map]; rfl

theorem length_rebuildVarNames (k : Nat) : (rebuildVarNames k).length = k := by
  simp [rebuildVarNames]

theorem rebuildVarNames_nodup (k : Nat) : (rebuildVarNames k).Nodup := by
  refine (List.nodup_map_iff_inj_on List.nodup_range).mpr fun i _ j _ h => ?_
  have h2 : ("@c" ++ toString i).toList = ("@c" ++ toString j).toList := by rw [h]
  rw [String.toList_append, String.toList_append] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left h2))

theorem getElem_rebuildVarNames {k i : Nat} (hi : i < k) :
    (rebuildVarNames k)[i]'(by rw [length_rebuildVarNames]; exact hi) = "@c" ++ toString i := by
  simp [rebuildVarNames]

theorem atPrefix_rebuildVarNames {k : Nat} {v : Var} (h : v ∈ rebuildVarNames k) :
    "@".isPrefixOf v = true := by
  rw [rebuildVarNames, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  rw [String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@c").toList = ['@', 'c'] from by decide]
  exact ⟨'c' :: (toString i).toList, rfl⟩

theorem not_mem_rebuildVarNames {v : Var} {c : Char} (hv : v.toList = ['@', c]) (hc : c ≠ 'c')
    (k : Nat) : v ∉ rebuildVarNames k := by
  intro h
  rw [rebuildVarNames, List.mem_map] at h
  obtain ⟨i, -, heq⟩ := h
  have h2 : v.toList = ['@', 'c'] ++ (toString i).toList := by
    rw [← heq, String.toList_append, show ("@c").toList = ['@', 'c'] from by decide]
  rw [hv] at h2
  exact hc (List.cons.inj (List.cons.inj h2).2).1



theorem Env.lookup_append_of_none {v : Var} {σ₁ σ₂ : Env} (h : Env.lookup v σ₁ = none) :
    Env.lookup v (σ₁ ++ σ₂) = Env.lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨w, t⟩ := b
    rw [Env.lookup_cons] at h
    split at h
    · exact absurd h (by simp)
    · next hne => rw [List.cons_append, Env.lookup_cons, if_neg hne]; exact ih h

theorem Env.lookup_append_of_some {v : Var} {t : Term} {σ₁ σ₂ : Env}
    (h : Env.lookup v σ₁ = some t) : Env.lookup v (σ₁ ++ σ₂) = some t := by
  induction σ₁ with
  | nil => exact absurd h (by simp [Env.lookup])
  | cons b bs ih =>
    obtain ⟨w, u⟩ := b
    rw [Env.lookup_cons] at h
    rw [List.cons_append, Env.lookup_cons]
    split
    · next hveq => rwa [if_pos hveq] at h
    · next hne => exact ih (by rwa [if_neg hne] at h)

theorem Env.dom_zip_subset : ∀ (vs : List Var) (as : List Term), Env.dom (vs.zip as) ⊆ vs
  | [], _ => by simp [Env.dom]
  | _ :: _, [] => by simp [Env.dom]
  | v :: vs, a :: as => by
      intro w hw
      rw [List.zip_cons_cons, Env.dom_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Env.dom_zip_subset vs as hw)

theorem Env.lookup_zip : ∀ (vs : List Var) (as : List Term), vs.length = as.length →
    vs.Nodup → ∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length),
      Env.lookup vs[i] (vs.zip as) = some as[i]
  | [], [], _, _, i, hi, _ => by simp at hi
  | v :: vs, a :: as, hlen, hnd, 0, _, _ => by
      rw [List.zip_cons_cons, Env.lookup_cons]
      simp
  | v :: vs, a :: as, hlen, hnd, i + 1, hi, hi' => by
      rw [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hi'
      have hne : vs[i] ≠ v := fun hc => hnd.1 (hc ▸ List.getElem_mem hi)
      rw [List.zip_cons_cons]
      simp only [List.getElem_cons_succ]
      rw [Env.lookup_cons, if_neg hne]
      exact Env.lookup_zip vs as (by simpa using hlen) hnd.2 i hi hi'



/-- **A list of variables evaluates to what the environment binds them to.** -/
theorem Expr.evalList_map_var {sig : Signature} : ∀ (vs : List Var) (as : List Term) (ρ : Env),
    vs.length = as.length →
    (∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length), Env.lookup vs[i] ρ = some as[i]) →
    Expr.evalList sig (vs.map Expr.var) ρ = some as
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | v :: vs, a :: as, ρ, hlen, h => by
      have h0 : Env.lookup v ρ = some a := h 0 (by simp) (by simp)
      have hrest : Expr.evalList sig (vs.map Expr.var) ρ = some as :=
        Expr.evalList_map_var vs as ρ (by simpa using hlen)
          (fun i hi hi' => h (i + 1) (by simpa using hi) (by simpa using hi'))
      rw [List.map_cons, Expr.evalList, Expr.eval, h0, Option.bind_some, hrest]
      rfl

/-- Every free variable of a list of variable atoms is one of them. -/
theorem Expr.freeVarsList_map_var_subset : ∀ (vs : List Var) (σ : Env),
    Expr.freeVarsList (vs.map Expr.var) σ ⊆ vs
  | [], _ => by simp
  | v :: vs, σ => by
      intro w hw
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff] at hw
      rcases hw with hw | hw
      · rw [Expr.freeVars] at hw
        split at hw
        · exact absurd hw (by simp)
        · rw [List.mem_singleton] at hw; exact hw ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Expr.freeVarsList_map_var_subset vs σ hw)

/-- And one the environment does not bind is free. -/
theorem Expr.mem_freeVarsList_map_var : ∀ (vs : List Var) (σ : Env) {v : Var}, v ∈ vs →
    Env.lookup v σ = none → v ∈ Expr.freeVarsList (vs.map Expr.var) σ
  | [], _, _, hv, _ => by simp at hv
  | w :: vs, σ, v, hv, hn => by
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Or.inl (by rw [Expr.freeVars, hn]; simp)
      · exact Or.inr (Expr.mem_freeVarsList_map_var vs σ hv' hn)

/-- **`matchQuery` completeness, in general form.** A substitution the enumerator will offer is
`Env.canon`-shaped at `Query.freeVars`' own order and drawn from `FDatabase.valueTerms`; the
per-atom check then reads it restricted to that atom, and the two restrictions compose. -/
theorem mem_matchQuery_of_lookup {d : FDatabase} {q : Query} {τ : Env}
    (hdef : ∀ v ∈ Query.freeVars q d.env, (Env.lookup v τ).isSome = true)
    (hval : ∀ v ∈ Query.freeVars q d.env, ∀ t, Env.lookup v τ = some t → t ∈ d.valueTerms)
    (hp : ∀ p ∈ q, patternHolds d p (Env.canon (p.freeVars d.env) τ) = true) :
    Env.canon (Query.freeVars q d.env) τ ∈ matchQuery d q := by
  rw [matchQuery, List.mem_filter]
  refine ⟨mem_assignments.mpr ⟨Env.dom_canon hdef, fun b hb => ?_⟩, List.all_eq_true.mpr ?_⟩
  · obtain ⟨hmem, hlk⟩ := Env.mem_canon hb
    exact hval b.1 hmem b.2 hlk
  · intro p hpq
    rw [Env.canon_canon (Query.freeVars_subset hpq) (Query.freeVars_nodup q d.env)]
    exact hp p hpq



/-- **Every column a row records is a value `matchQuery` will assign.** `matchQuery` enumerates
`FDatabase.valueTerms` and not `terms`, so a rule can only re-read a row whose columns are of
that kind. `execM_rowColumnsValued` is this at an `execM` target. -/
def FDatabase.RowColumnsValued (d : FDatabase) : Prop :=
  ∀ r ∈ d.rows, ∀ t ∈ r.args ++ r.out, t ∈ d.valueTerms

set_option maxRecDepth 100000 in
/-- **Non-vacuous**, at the state the one-off instance matches at: `cxRb` is `cxPre` without the
third `set`, and every column its two rows record is a value the enumerator would assign. -/
theorem cxRb_rowColumnsValued : cxRb.RowColumnsValued := by
  change ∀ r ∈ cxRb.rows, ∀ t ∈ r.args ++ r.out, t ∈ cxRb.valueTerms
  decide

/-- The e-class rebuild rule of a `k`-ary constructor, named. -/
def eclassRule (f : FnName) (k : Nat) : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k),
              .values [.var "@x", .var "@q"] ufName [.var "@e"]],
    actions := [.set (viewName f) (rebuildVars k) [.var "@x", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

theorem eclassRule_mem_maintenanceRules {P : Program} {f : FnName} {k : Nat}
    (h : (f, k) ∈ P.ctors) : eclassRule f k ∈ maintenanceRules P := by
  rw [maintenanceRules, List.mem_cons]
  exact Or.inr (List.mem_flatMap.mpr ⟨(f, k), h, List.mem_cons_self⟩)

/-- A generated query variable is read past the environment and off the substitution. -/
theorem lookup_env_canon {d : FDatabase} (hnoat : d.NoAtEnv) {vars : List Var}
    (hnd : vars.Nodup) {τ : Env} {v : Var} (hv : v ∈ vars) (hat : "@".isPrefixOf v = true) :
    Env.lookup v (d.env ++ Env.canon vars τ) = Env.lookup v τ := by
  rw [Env.lookup_append_of_none (Env.lookup_eq_none_iff.mpr (fun hc => ?_)),
    Env.lookup_canon hnd hv]
  obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hc
  exact hnoat (v, t) ht hat

theorem mem_addRow_rows_self {d : FDatabase} {g : FnName} {as vs : List Term} :
    (⟨g, as, vs⟩ : Row) ∈ (FDatabase.addRow g as vs d).rows := by
  simp [FDatabase.addRow, List.mem_dedup]



/-- The substitution the e-class rule matches at a view row and the `@UF` row above it. -/
def eclassSubst (k : Nat) (as : List Term) (e pf x q : Term) : Env :=
  (rebuildVarNames k).zip as ++ [("@e", e), ("@p", pf), ("@x", x), ("@q", q)]

section
variable {k : Nat} {as : List Term} {e pf x q : Term}

theorem lookup_eclassSubst_col (hlen : as.length = k) {i : Nat} (hi : i < k) :
    Env.lookup ("@c" ++ toString i) (eclassSubst k as e pf x q)
      = some (as[i]'(by omega)) := by
  rw [eclassSubst]
  refine Env.lookup_append_of_some ?_
  have h := Env.lookup_zip (rebuildVarNames k) as (by rw [length_rebuildVarNames, hlen])
    (rebuildVarNames_nodup k) i (by rw [length_rebuildVarNames]; exact hi) (by omega)
  rwa [getElem_rebuildVarNames hi] at h

private theorem lookup_eclassSubst_head {v : Var} {c : Char} (hv : v.toList = ['@', c])
    (hc : c ≠ 'c') :
    Env.lookup v (eclassSubst k as e pf x q)
      = Env.lookup v [("@e", e), ("@p", pf), ("@x", x), ("@q", q)] := by
  rw [eclassSubst]
  refine Env.lookup_append_of_none (Env.lookup_eq_none_iff.mpr fun hc' => ?_)
  exact not_mem_rebuildVarNames hv hc k (Env.dom_zip_subset _ _ hc')

theorem lookup_eclassSubst_e : Env.lookup "@e" (eclassSubst k as e pf x q) = some e := by
  rw [lookup_eclassSubst_head (c := 'e') (by decide) (by decide)]
  simp [Env.lookup]

theorem lookup_eclassSubst_p : Env.lookup "@p" (eclassSubst k as e pf x q) = some pf := by
  rw [lookup_eclassSubst_head (c := 'p') (by decide) (by decide)]
  simp [Env.lookup]

theorem lookup_eclassSubst_x : Env.lookup "@x" (eclassSubst k as e pf x q) = some x := by
  rw [lookup_eclassSubst_head (c := 'x') (by decide) (by decide)]
  simp [Env.lookup]

theorem lookup_eclassSubst_q : Env.lookup "@q" (eclassSubst k as e pf x q) = some q := by
  rw [lookup_eclassSubst_head (c := 'q') (by decide) (by decide)]
  simp [Env.lookup]

end



theorem lookup_env_eq_none {d : FDatabase} (hnoat : d.NoAtEnv) {v : Var}
    (hat : "@".isPrefixOf v = true) : Env.lookup v d.env = none :=
  Env.lookup_eq_none_iff.mpr fun hc => by
    obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hc; exact hnoat (v, t) ht hat

theorem mem_freeVars_values {vs cs : List Var} {g : FnName} {σ : Env} {v : Var}
    (hn : Env.lookup v σ = none) (h : v ∈ vs ∨ v ∈ cs) :
    v ∈ (Pattern.values (vs.map Expr.var) g (cs.map Expr.var)).freeVars σ := by
  rw [Pattern.freeVars, List.mem_union_iff]
  exact h.imp (fun hv => Expr.mem_freeVarsList_map_var vs σ hv hn)
    (fun hv => Expr.mem_freeVarsList_map_var cs σ hv hn)

theorem freeVars_values_subset {vs cs : List Var} {g : FnName} {σ : Env} {v : Var}
    (h : v ∈ (Pattern.values (vs.map Expr.var) g (cs.map Expr.var)).freeVars σ) :
    v ∈ vs ∨ v ∈ cs := by
  rw [Pattern.freeVars, List.mem_union_iff] at h
  exact h.imp (fun hv => Expr.freeVarsList_map_var_subset vs σ hv)
    (fun hv => Expr.freeVarsList_map_var_subset cs σ hv)

/-- Every variable the e-class rule's query leaves free is one of its six families. -/
theorem mem_freeVars_eclassRule {d : FDatabase} {f : FnName} {k : Nat} {v : Var}
    (h : v ∈ Query.freeVars (eclassRule f k).query d.env) :
    v = "@e" ∨ v = "@p" ∨ v = "@x" ∨ v = "@q" ∨ v ∈ rebuildVarNames k := by
  obtain ⟨p, hp, hv⟩ := Query.mem_freeVars.mp h
  have hp2 : p = Pattern.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k) ∨
      p = Pattern.values [.var "@x", .var "@q"] ufName [.var "@e"] := by
    simpa [eclassRule] using hp
  rcases hp2 with rfl | rfl
  · rw [rebuildVars_eq_map] at hv
    rcases freeVars_values_subset (vs := ["@e", "@p"]) hv with h' | h'
    · rcases List.mem_cons.mp h' with rfl | h'' 
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simpa using h''))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · rcases freeVars_values_subset (vs := ["@x", "@q"]) (cs := ["@e"]) hv with h' | h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h''))))
    · exact Or.inl (by simpa using h')




theorem Expr.evalList_pair_var {sig : Signature} {v w : Var} {a b : Term} {ρ : Env}
    (hv : Env.lookup v ρ = some a) (hw : Env.lookup w ρ = some b) :
    Expr.evalList sig [Expr.var v, Expr.var w] ρ = some [a, b] := by
  rw [Expr.evalList, Expr.eval, hv, Option.bind_some, Expr.evalList, Expr.eval, hw,
    Option.bind_some, Expr.evalList]
  rfl

theorem Expr.evalList_single_var {sig : Signature} {v : Var} {a : Term} {ρ : Env}
    (hv : Env.lookup v ρ = some a) : Expr.evalList sig [Expr.var v] ρ = some [a] := by
  rw [Expr.evalList, Expr.eval, hv, Option.bind_some, Expr.evalList]
  rfl

theorem evalList_rebuildVars {sig : Signature} {k : Nat} {as : List Term} {ρ : Env}
    (hlen : as.length = k)
    (h : ∀ (i : Nat) (hi : i < k), Env.lookup ("@c" ++ toString i) ρ = some (as[i]'(by omega))) :
    Expr.evalList sig (rebuildVars k) ρ = some as := by
  rw [rebuildVars_eq_map]
  refine Expr.evalList_map_var _ _ _ (by rw [length_rebuildVarNames, hlen]) (fun i hi hi' => ?_)
  rw [length_rebuildVarNames] at hi
  rw [getElem_rebuildVarNames hi]
  exact h i hi

theorem eval_transE {sig : Signature} (htr : sig.IsCtor transName) {ρ : Env} {a b : Term}
    (ha : Env.lookup "@p" ρ = some a) (hb : Env.lookup "@q" ρ = some b) :
    Expr.eval sig (transE (.var "@p") (.var "@q")) ρ = some (Term.app transName [a, b]) := by
  rw [transE, Expr.eval, Expr.evalList_pair_var ha hb]
  rw [show Prim.ofName transName = none from rfl]
  rw [if_pos htr]
  rfl


theorem atPrefix_of_eclass_var {v : Var} {k : Nat}
    (h : v = "@e" ∨ v = "@p" ∨ v = "@x" ∨ v = "@q" ∨ v ∈ rebuildVarNames k) :
    "@".isPrefixOf v = true := by
  rcases h with rfl | rfl | rfl | rfl | h'
  · exact (by decide +kernel : "@".isPrefixOf "@e" = true)
  · exact (by decide +kernel : "@".isPrefixOf "@p" = true)
  · exact (by decide +kernel : "@".isPrefixOf "@x" = true)
  · exact (by decide +kernel : "@".isPrefixOf "@q" = true)
  · exact atPrefix_rebuildVarNames h'

theorem mem_freeVars_view {d : FDatabase} (hnoat : d.NoAtEnv) {f : FnName} {k : Nat} {v : Var}
    (h : v = "@e" ∨ v = "@p" ∨ v ∈ rebuildVarNames k) :
    v ∈ (Pattern.values [Expr.var "@e", Expr.var "@p"] (viewName f)
      (rebuildVars k)).freeVars d.env := by
  have hn : Env.lookup v d.env = none :=
    lookup_env_eq_none hnoat (atPrefix_of_eclass_var (k := k) (by tauto))
  rw [rebuildVars_eq_map]
  refine mem_freeVars_values (vs := ["@e", "@p"]) hn ?_
  rcases h with rfl | rfl | h'
  · exact Or.inl List.mem_cons_self
  · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Or.inr h'

theorem mem_freeVars_uf {d : FDatabase} (hnoat : d.NoAtEnv) {v : Var}
    (h : v = "@x" ∨ v = "@q" ∨ v = "@e") :
    v ∈ (Pattern.values [Expr.var "@x", Expr.var "@q"] ufName
      [Expr.var "@e"]).freeVars d.env := by
  have hn : Env.lookup v d.env = none :=
    lookup_env_eq_none hnoat (atPrefix_of_eclass_var (k := 0) (by tauto))
  refine mem_freeVars_values (vs := ["@x", "@q"]) (cs := ["@e"]) hn ?_
  rcases h with rfl | rfl | rfl
  · exact Or.inl List.mem_cons_self
  · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Or.inr List.mem_cons_self

/-- **The e-class rebuild rule fires**, at a view row and the `@UF` row above its e-class
column: the row it writes carries the row's own key, the edge's far end, and the composed
proof. This is the residue's second obligation's hole, discharged. -/
theorem eclassRule_fires {P : Program} {d : FDatabase} (hb : d.EncBase P (encodeSig P))
    (htr : (encodeSig P).IsCtor transName) (hcv : d.RowColumnsValued)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors)
    (hmg : (d.sig.mergeOf (viewName f)).isSome = true)
    (hmguf : (d.sig.mergeOf ufName).isSome = true)
    {as : List Term} (hlen : as.length = k) {e pf x q : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows)
    (huf : (⟨ufName, [e], [x, q]⟩ : Row) ∈ d.rows) :
    (⟨viewName f, as, [x, Term.app transName [pf, q]]⟩ : Row) ∈
      (execRunRules rebuildRuleset d).rows := by
  set τ := eclassSubst k as e pf x q with hτ
  set qy := (eclassRule f k).query with hqy
  -- the two rows' columns are values, hence terms
  have hvrow := hcv _ hrow
  have hvuf := hcv _ huf
  have hve : e ∈ d.valueTerms := hvrow e (by simp)
  have hvp : pf ∈ d.valueTerms := hvrow pf (by simp)
  have hvx : x ∈ d.valueTerms := hvuf x (by simp)
  have hvq : q ∈ d.valueTerms := hvuf q (by simp)
  have hvc : ∀ t ∈ as, t ∈ d.valueTerms := fun t ht => hvrow t (by simp [ht])
  -- every free variable of the query is bound by `τ`, to a value
  have hat : ∀ v ∈ Query.freeVars qy d.env, "@".isPrefixOf v = true := by
    intro v hv
    rcases mem_freeVars_eclassRule hv with rfl | rfl | rfl | rfl | hv'
    · exact (by decide +kernel : "@".isPrefixOf "@e" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@p" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@x" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@q" = true)
    · exact atPrefix_rebuildVarNames hv'
  have hlkv : ∀ v ∈ Query.freeVars qy d.env, ∃ t, Env.lookup v τ = some t ∧ t ∈ d.valueTerms := by
    intro v hv
    rcases mem_freeVars_eclassRule hv with rfl | rfl | rfl | rfl | hv'
    · exact ⟨e, lookup_eclassSubst_e, hve⟩
    · exact ⟨pf, lookup_eclassSubst_p, hvp⟩
    · exact ⟨x, lookup_eclassSubst_x, hvx⟩
    · exact ⟨q, lookup_eclassSubst_q, hvq⟩
    · rw [rebuildVarNames, List.mem_map] at hv'
      obtain ⟨i, hi, rfl⟩ := hv'
      rw [List.mem_range] at hi
      exact ⟨as[i]'(by omega), lookup_eclassSubst_col hlen hi,
        hvc _ (List.getElem_mem (by omega))⟩
  -- a variable of either atom reads off `τ`, past the environment and through both canons
  have hread : ∀ (vars : List Var), vars.Nodup →
      (∀ v ∈ vars, v ∈ Query.freeVars qy d.env) → ∀ v ∈ vars,
        Env.lookup v (d.env ++ Env.canon vars τ) = Env.lookup v τ :=
    fun vars hnd hsub v hv => lookup_env_canon hb.noAtEnv hnd hv (hat v (hsub v hv))
  have hv₁ : Pattern.values [Expr.var "@e", Expr.var "@p"] (viewName f) (rebuildVars k) ∈ qy :=
    List.mem_cons_self
  have hv₂ : Pattern.values [Expr.var "@x", Expr.var "@q"] ufName [Expr.var "@e"] ∈ qy :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hr₁ : ∀ v, (v = "@e" ∨ v = "@p" ∨ v ∈ rebuildVarNames k) →
      Env.lookup v (d.env ++ Env.canon
        ((Pattern.values [Expr.var "@e", Expr.var "@p"] (viewName f)
          (rebuildVars k)).freeVars d.env) τ) = Env.lookup v τ := by
    intro v hv
    exact hread _ (Pattern.freeVars_nodup _ d.env)
      (fun w hw => Query.mem_freeVars.mpr ⟨_, hv₁, hw⟩) v (mem_freeVars_view hb.noAtEnv hv)
  have hr₂ : ∀ v, (v = "@x" ∨ v = "@q" ∨ v = "@e") →
      Env.lookup v (d.env ++ Env.canon
        ((Pattern.values [Expr.var "@x", Expr.var "@q"] ufName
          [Expr.var "@e"]).freeVars d.env) τ) = Env.lookup v τ := by
    intro v hv
    exact hread _ (Pattern.freeVars_nodup _ d.env)
      (fun w hw => Query.mem_freeVars.mpr ⟨_, hv₂, hw⟩) v (mem_freeVars_uf hb.noAtEnv hv)
  have hrq : ∀ v, (v = "@e" ∨ v = "@p" ∨ v = "@x" ∨ v = "@q" ∨ v ∈ rebuildVarNames k) →
      Env.lookup v (d.env ++ Env.canon (Query.freeVars qy d.env) τ) = Env.lookup v τ := by
    intro v hv
    refine hread _ (Query.freeVars_nodup qy d.env) (fun w hw => hw) v ?_
    rcases hv with rfl | rfl | rfl | rfl | hv'
    · exact Query.mem_freeVars.mpr ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inl rfl)⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inr (Or.inl rfl))⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₂, mem_freeVars_uf hb.noAtEnv (Or.inl rfl)⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₂, mem_freeVars_uf hb.noAtEnv (Or.inr (Or.inl rfl))⟩
    · exact Query.mem_freeVars.mpr
        ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inr (Or.inr hv'))⟩
  -- every column is a term the state holds
  have hterm : ∀ t ∈ as ++ [e, pf], t ∈ d.terms := by
    intro t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · exact FDatabase.mem_terms_of_mem_valueTerms (hvc t ht')
    · have : t = e ∨ t = pf := by simpa using ht'
      rcases this with rfl | rfl
      · exact FDatabase.mem_terms_of_mem_valueTerms hve
      · exact FDatabase.mem_terms_of_mem_valueTerms hvp
  have htermu : ∀ t ∈ [e] ++ [x, q], t ∈ d.terms := by
    intro t ht
    have : t = e ∨ t = x ∨ t = q := by simpa using ht
    rcases this with rfl | rfl | rfl
    · exact FDatabase.mem_terms_of_mem_valueTerms hve
    · exact FDatabase.mem_terms_of_mem_valueTerms hvx
    · exact FDatabase.mem_terms_of_mem_valueTerms hvq
  -- the match
  have hσ : Env.canon (Query.freeVars qy d.env) τ ∈ matchQuery d qy := by
    refine mem_matchQuery_of_lookup (fun v hv => ?_) (fun v hv t ht => ?_) (fun p hp => ?_)
    · obtain ⟨t, ht, -⟩ := hlkv v hv; rw [ht]; rfl
    · obtain ⟨u, hu, hval⟩ := hlkv v hv
      rw [ht] at hu; exact (Option.some.inj hu) ▸ hval
    · have hp2 : p = Pattern.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k) ∨
          p = Pattern.values [.var "@x", .var "@q"] ufName [.var "@e"] := by
        simpa [hqy, eclassRule] using hp
      rcases hp2 with rfl | rfl
      · refine patternHolds_values_of_mem_rows hmg ?_ ?_ hrow hterm
        · refine evalList_rebuildVars hlen (fun i hi => ?_)
          rw [hr₁ _ (Or.inr (Or.inr (by
            rw [rebuildVarNames, List.mem_map]
            exact ⟨i, List.mem_range.mpr hi, rfl⟩))), lookup_eclassSubst_col hlen hi]
        · exact Expr.evalList_pair_var (hr₁ _ (Or.inl rfl) ▸ lookup_eclassSubst_e)
            (hr₁ _ (Or.inr (Or.inl rfl)) ▸ lookup_eclassSubst_p)
      · refine patternHolds_values_of_mem_rows hmguf ?_ ?_ huf htermu
        · exact Expr.evalList_single_var (hr₂ _ (Or.inr (Or.inr rfl)) ▸ lookup_eclassSubst_e)
        · exact Expr.evalList_pair_var (hr₂ _ (Or.inl rfl) ▸ lookup_eclassSubst_x)
            (hr₂ _ (Or.inr (Or.inl rfl)) ▸ lookup_eclassSubst_q)
  -- the head
  have hcs : Expr.evalList d.sig (rebuildVars k)
      (d.env ++ Env.canon (Query.freeVars qy d.env) τ) = some as := by
    refine evalList_rebuildVars hlen (fun i hi => ?_)
    rw [hrq _ (Or.inr (Or.inr (Or.inr (Or.inr (by
      rw [rebuildVarNames, List.mem_map]
      exact ⟨i, List.mem_range.mpr hi, rfl⟩))))), lookup_eclassSubst_col hlen hi]
  have hout : Expr.evalList d.sig [Expr.var "@x", transE (.var "@p") (.var "@q")]
      (d.env ++ Env.canon (Query.freeVars qy d.env) τ)
      = some [x, Term.app transName [pf, q]] := by
    rw [Expr.evalList, Expr.eval, hrq _ (Or.inr (Or.inr (Or.inl rfl))), lookup_eclassSubst_x,
      Option.bind_some, Expr.evalList,
      eval_transE (by rw [hb.sig]; exact htr) (hrq _ (Or.inr (Or.inl rfl)) ▸ lookup_eclassSubst_p)
        (hrq _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ▸ lookup_eclassSubst_q),
      Option.bind_some, Expr.evalList]
    rfl
  refine mem_rows_execRunRules.mpr (Or.inr ⟨eclassRule f k,
    hb.held _ (eclassRule_mem_maintenanceRules hfk), rfl, _, hσ,
    { FDatabase.addRow (viewName f) as [x, Term.app transName [pf, q]]
        { d with env := d.env ++ Env.canon (Query.freeVars qy d.env) τ } with
      env := d.env, rules := d.rules }, ?_, mem_addRow_rows_self⟩)
  change execLocalActions d (eclassRule f k).actions _ = some _
  rw [eclassRule, execLocalActions]
  simp only [execActions, Egglog.execAction, hcs, Option.bind_some, hout, Option.map_some]

/-! ### The other rebuild rule

`rebuildRules` emits one rule per child column beside the e-class rule, and the two are the same
shape at the same size: one view atom, one `@UF` atom, one `set`. What differs is where the
`@UF` atom is keyed — column `i` rather than the e-class column — and therefore where the head
writes: the e-class rule re-`set`s the row at **its own key**, and the column rule re-`set`s it
at a **different** one, keeping the e-class it read and composing a congruence step into the
proof. That difference is the whole reason the descent contradiction that closes
`no_ufRowEdge_of_rowsClosed` has no counterpart here.

Below is that rule named, its firing proved through the same three lemmas
(`mem_matchQuery_of_lookup`, `patternHolds_values_of_mem_rows`, `mem_rows_execRunRules`), and the
evaluation of the proof term its head builds — `@Trans (@Sym (@Congr_k @Fiat … @q … @Fiat)) @p`,
whose four heads are the four `Signature.IsCtor` hypotheses the theorem carries. -/

theorem Prim.ofName_of_atPrefix {s : FnName} (h : "@".isPrefixOf s = true) :
    Prim.ofName s = none := by
  unfold Prim.ofName
  split <;> first
    | rfl
    | exact absurd h (by decide +kernel)

theorem atPrefix_colVar (i : Nat) : "@".isPrefixOf ("@c" ++ toString i) = true := by
  rw [String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@c").toList = ['@', 'c'] from by decide]
  exact ⟨'c' :: (toString i).toList, rfl⟩

theorem prim_ofName_congrName {k : Nat} : Prim.ofName (congrName k) = none :=
  Prim.ofName_of_atPrefix (by
    rw [congrName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
      show ("@Congr_").toList = ['@', 'C', 'o', 'n', 'g', 'r', '_'] from by decide]
    exact ⟨['C', 'o', 'n', 'g', 'r', '_'] ++ (toString k).toList, rfl⟩)

/-- The column-`i` rebuild rule of a `k`-ary constructor, named. -/
def columnRule (f : FnName) (k i : Nat) : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k),
              .values [.var "@x", .var "@q"] ufName [.var ("@c" ++ toString i)]],
    actions := [.set (viewName f) ((rebuildVars k).set i (.var "@x"))
      [.var "@e", transE (symE (congrE (congrChildren k i))) (.var "@p")]],
    ruleset := rebuildRuleset }

theorem columnRule_mem_maintenanceRules {P : Program} {f : FnName} {k i : Nat}
    (h : (f, k) ∈ P.ctors) (hi : i < k) : columnRule f k i ∈ maintenanceRules P := by
  rw [maintenanceRules, List.mem_cons]
  refine Or.inr (List.mem_flatMap.mpr ⟨(f, k), h, ?_⟩)
  change columnRule f k i ∈ rebuildRules f k
  rw [rebuildRules]
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem mem_freeVars_columnRule {d : FDatabase} {f : FnName} {k i : Nat} (hi : i < k) {v : Var}
    (h : v ∈ Query.freeVars (columnRule f k i).query d.env) :
    v = "@e" ∨ v = "@p" ∨ v = "@x" ∨ v = "@q" ∨ v ∈ rebuildVarNames k := by
  obtain ⟨p, hp, hv⟩ := Query.mem_freeVars.mp h
  have hp2 : p = Pattern.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k) ∨
      p = Pattern.values [.var "@x", .var "@q"] ufName [.var ("@c" ++ toString i)] := by
    simpa [columnRule] using hp
  rcases hp2 with rfl | rfl
  · rw [rebuildVars_eq_map] at hv
    rcases freeVars_values_subset (vs := ["@e", "@p"]) hv with h' | h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simpa using h''))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · rcases freeVars_values_subset (vs := ["@x", "@q"]) (cs := ["@c" ++ toString i]) hv with h' | h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using h''))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      obtain rfl : v = "@c" ++ toString i := by simpa using h'
      rw [rebuildVarNames, List.mem_map]
      exact ⟨i, List.mem_range.mpr hi, rfl⟩

theorem mem_freeVars_ufc {d : FDatabase} (hnoat : d.NoAtEnv) {i : Nat} {v : Var}
    (h : v = "@x" ∨ v = "@q" ∨ v = "@c" ++ toString i) :
    v ∈ (Pattern.values [Expr.var "@x", Expr.var "@q"] ufName
      [Expr.var ("@c" ++ toString i)]).freeVars d.env := by
  have hn : Env.lookup v d.env = none := by
    refine lookup_env_eq_none hnoat ?_
    rcases h with rfl | rfl | rfl
    · exact (by decide +kernel : "@".isPrefixOf "@x" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@q" = true)
    · exact atPrefix_colVar i
  refine mem_freeVars_values (vs := ["@x", "@q"]) (cs := ["@c" ++ toString i]) hn ?_
  rcases h with rfl | rfl | rfl
  · exact Or.inl List.mem_cons_self
  · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact Or.inr List.mem_cons_self

end Egglog

namespace Egglog

theorem Expr.evalList_map {sig : Signature} {α : Type} (g : α → Expr) (h : α → Term) (ρ : Env) :
    ∀ (l : List α), (∀ a ∈ l, Expr.eval sig (g a) ρ = some (h a)) →
      Expr.evalList sig (l.map g) ρ = some (l.map h)
  | [], _ => rfl
  | a :: l, hp => by
      rw [List.map_cons, Expr.evalList, hp a List.mem_cons_self, Option.bind_some,
        Expr.evalList_map g h ρ l (fun b hb => hp b (List.mem_cons_of_mem _ hb)),
        Option.map_some, List.map_cons]

theorem evalList_rebuildVars_set {sig : Signature} {k i : Nat} {as : List Term} {x : Term}
    {ρ : Env} (hlen : as.length = k) (hx : Env.lookup "@x" ρ = some x)
    (h : ∀ (j : Nat) (hj : j < k), Env.lookup ("@c" ++ toString j) ρ = some (as[j]'(by omega))) :
    Expr.evalList sig ((rebuildVars k).set i (.var "@x")) ρ = some (as.set i x) := by
  rw [rebuildVars_eq_map, ← List.map_set]
  refine Expr.evalList_map_var _ _ _ (by simp [length_rebuildVarNames, hlen]) (fun j hj hj' => ?_)
  rw [List.length_set, length_rebuildVarNames] at hj
  rw [List.getElem_set, List.getElem_set]
  by_cases hji : i = j
  · subst hji; rw [if_pos rfl, if_pos rfl]; exact hx
  · rw [if_neg hji, if_neg hji, getElem_rebuildVarNames hj]
    exact h j hj

/-- The child proofs a column-`i` rebuild firing evaluates: the edge's proof at `i`, `@Fiat`
elsewhere. -/
def congrProofs (k i : Nat) (q : Term) : List Term :=
  (List.range k).map fun j => if j = i then q else Term.app fiatName []

theorem length_congrChildren (k i : Nat) : (congrChildren k i).length = k := by
  simp [congrChildren]

theorem evalList_congrChildren {sig : Signature} {k i : Nat} {q : Term} {ρ : Env}
    (hfi : sig.IsCtor fiatName) (hq : Env.lookup "@q" ρ = some q) :
    Expr.evalList sig (congrChildren k i) ρ = some (congrProofs k i q) := by
  rw [congrChildren, congrProofs]
  refine Expr.evalList_map _ _ _ _ (fun j _ => ?_)
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj]; exact hq
  · rw [if_neg hj, if_neg hj, fiatE,
      Expr.eval_app_ctor (show Prim.ofName fiatName = none from rfl) hfi]
    rfl

/-- The proof a column-`i` rebuild firing records. -/
def columnProof (k i : Nat) (pf q : Term) : Term :=
  Term.app transName [Term.app symName [Term.app (congrName k) (congrProofs k i q)], pf]

theorem eval_columnProof {sig : Signature} {k i : Nat} {pf q : Term} {ρ : Env}
    (hfi : sig.IsCtor fiatName) (hsy : sig.IsCtor symName) (hcg : sig.IsCtor (congrName k))
    (htr : sig.IsCtor transName)
    (hp : Env.lookup "@p" ρ = some pf) (hq : Env.lookup "@q" ρ = some q) :
    Expr.eval sig (transE (symE (congrE (congrChildren k i))) (.var "@p")) ρ
      = some (columnProof k i pf q) := by
  have hcong : Expr.eval sig (congrE (congrChildren k i)) ρ
      = some (Term.app (congrName k) (congrProofs k i q)) := by
    rw [congrE, length_congrChildren,
      Expr.eval_app_ctor prim_ofName_congrName hcg, evalList_congrChildren hfi hq]
    rfl
  have hsym : Expr.eval sig (symE (congrE (congrChildren k i))) ρ
      = some (Term.app symName [Term.app (congrName k) (congrProofs k i q)]) := by
    rw [symE, Expr.eval_app_ctor (show Prim.ofName symName = none from rfl) hsy,
      Expr.evalList, hcong, Option.bind_some, Expr.evalList]
    rfl
  rw [transE, Expr.eval_app_ctor (show Prim.ofName transName = none from rfl) htr,
    Expr.evalList, hsym, Option.bind_some, Expr.evalList, Expr.eval, hp, Option.bind_some,
    Expr.evalList]
  rfl


/-- **A column rebuild rule fires**, at a view row and the `@UF` row above its column `i`:
the row it writes carries the same e-class column, the key with column `i` moved to the edge's
far end, and the congruence proof of the move. Sibling of `eclassRule_fires`. -/
theorem columnRule_fires {P : Program} {d : FDatabase} (hb : d.EncBase P (encodeSig P))
    (hcv : d.RowColumnsValued) {f : FnName} {k : Nat}
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName) (hcg : (encodeSig P).IsCtor (congrName k))
    (hfk : (f, k) ∈ P.ctors)
    (hmg : (d.sig.mergeOf (viewName f)).isSome = true)
    (hmguf : (d.sig.mergeOf ufName).isSome = true)
    {as : List Term} (hlen : as.length = k) {i : Nat} (hi : i < k) {e pf x q ci : Term}
    (hci : as[i]? = some ci)
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows)
    (huf : (⟨ufName, [ci], [x, q]⟩ : Row) ∈ d.rows) :
    (⟨viewName f, as.set i x, [e, columnProof k i pf q]⟩ : Row) ∈
      (execRunRules rebuildRuleset d).rows := by
  have hilen : i < as.length := by omega
  have hcieq : as[i]'hilen = ci := by
    rw [List.getElem?_eq_getElem hilen] at hci; exact Option.some.inj hci
  set τ := eclassSubst k as e pf x q with hτ
  set qy := (columnRule f k i).query with hqy
  have hvrow := hcv _ hrow
  have hvuf := hcv _ huf
  have hve : e ∈ d.valueTerms := hvrow e (by simp)
  have hvp : pf ∈ d.valueTerms := hvrow pf (by simp)
  have hvx : x ∈ d.valueTerms := hvuf x (by simp)
  have hvq : q ∈ d.valueTerms := hvuf q (by simp)
  have hvc : ∀ t ∈ as, t ∈ d.valueTerms := fun t ht => hvrow t (by simp [ht])
  have hat : ∀ v ∈ Query.freeVars qy d.env, "@".isPrefixOf v = true := by
    intro v hv
    rcases mem_freeVars_columnRule hi hv with rfl | rfl | rfl | rfl | hv'
    · exact (by decide +kernel : "@".isPrefixOf "@e" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@p" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@x" = true)
    · exact (by decide +kernel : "@".isPrefixOf "@q" = true)
    · exact atPrefix_rebuildVarNames hv'
  have hlkv : ∀ v ∈ Query.freeVars qy d.env, ∃ t, Env.lookup v τ = some t ∧ t ∈ d.valueTerms := by
    intro v hv
    rcases mem_freeVars_columnRule hi hv with rfl | rfl | rfl | rfl | hv'
    · exact ⟨e, lookup_eclassSubst_e, hve⟩
    · exact ⟨pf, lookup_eclassSubst_p, hvp⟩
    · exact ⟨x, lookup_eclassSubst_x, hvx⟩
    · exact ⟨q, lookup_eclassSubst_q, hvq⟩
    · rw [rebuildVarNames, List.mem_map] at hv'
      obtain ⟨j, hj, rfl⟩ := hv'
      rw [List.mem_range] at hj
      exact ⟨as[j]'(by omega), lookup_eclassSubst_col hlen hj,
        hvc _ (List.getElem_mem (by omega))⟩
  have hread : ∀ (vars : List Var), vars.Nodup →
      (∀ v ∈ vars, v ∈ Query.freeVars qy d.env) → ∀ v ∈ vars,
        Env.lookup v (d.env ++ Env.canon vars τ) = Env.lookup v τ :=
    fun vars hnd hsub v hv => lookup_env_canon hb.noAtEnv hnd hv (hat v (hsub v hv))
  have hv₁ : Pattern.values [Expr.var "@e", Expr.var "@p"] (viewName f) (rebuildVars k) ∈ qy :=
    List.mem_cons_self
  have hv₂ : Pattern.values [Expr.var "@x", Expr.var "@q"] ufName
      [Expr.var ("@c" ++ toString i)] ∈ qy := List.mem_cons_of_mem _ List.mem_cons_self
  have hcmem : ("@c" ++ toString i) ∈ rebuildVarNames k := by
    rw [rebuildVarNames, List.mem_map]; exact ⟨i, List.mem_range.mpr hi, rfl⟩
  have hr₁ : ∀ v, (v = "@e" ∨ v = "@p" ∨ v ∈ rebuildVarNames k) →
      Env.lookup v (d.env ++ Env.canon
        ((Pattern.values [Expr.var "@e", Expr.var "@p"] (viewName f)
          (rebuildVars k)).freeVars d.env) τ) = Env.lookup v τ := by
    intro v hv
    exact hread _ (Pattern.freeVars_nodup _ d.env)
      (fun w hw => Query.mem_freeVars.mpr ⟨_, hv₁, hw⟩) v (mem_freeVars_view hb.noAtEnv hv)
  have hr₂ : ∀ v, (v = "@x" ∨ v = "@q" ∨ v = "@c" ++ toString i) →
      Env.lookup v (d.env ++ Env.canon
        ((Pattern.values [Expr.var "@x", Expr.var "@q"] ufName
          [Expr.var ("@c" ++ toString i)]).freeVars d.env) τ) = Env.lookup v τ := by
    intro v hv
    exact hread _ (Pattern.freeVars_nodup _ d.env)
      (fun w hw => Query.mem_freeVars.mpr ⟨_, hv₂, hw⟩) v (mem_freeVars_ufc hb.noAtEnv hv)
  have hrq : ∀ v, (v = "@e" ∨ v = "@p" ∨ v = "@x" ∨ v = "@q" ∨ v ∈ rebuildVarNames k) →
      Env.lookup v (d.env ++ Env.canon (Query.freeVars qy d.env) τ) = Env.lookup v τ := by
    intro v hv
    refine hread _ (Query.freeVars_nodup qy d.env) (fun w hw => hw) v ?_
    rcases hv with rfl | rfl | rfl | rfl | hv'
    · exact Query.mem_freeVars.mpr ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inl rfl)⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inr (Or.inl rfl))⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₂, mem_freeVars_ufc hb.noAtEnv (Or.inl rfl)⟩
    · exact Query.mem_freeVars.mpr ⟨_, hv₂, mem_freeVars_ufc hb.noAtEnv (Or.inr (Or.inl rfl))⟩
    · exact Query.mem_freeVars.mpr
        ⟨_, hv₁, mem_freeVars_view hb.noAtEnv (Or.inr (Or.inr hv'))⟩
  have hterm : ∀ t ∈ as ++ [e, pf], t ∈ d.terms := by
    intro t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · exact FDatabase.mem_terms_of_mem_valueTerms (hvc t ht')
    · have : t = e ∨ t = pf := by simpa using ht'
      rcases this with rfl | rfl
      · exact FDatabase.mem_terms_of_mem_valueTerms hve
      · exact FDatabase.mem_terms_of_mem_valueTerms hvp
  have htermu : ∀ t ∈ [ci] ++ [x, q], t ∈ d.terms := by
    intro t ht
    have : t = ci ∨ t = x ∨ t = q := by simpa using ht
    rcases this with rfl | rfl | rfl
    · exact FDatabase.mem_terms_of_mem_valueTerms
        (hcieq ▸ hvc _ (List.getElem_mem hilen))
    · exact FDatabase.mem_terms_of_mem_valueTerms hvx
    · exact FDatabase.mem_terms_of_mem_valueTerms hvq
  have hσ : Env.canon (Query.freeVars qy d.env) τ ∈ matchQuery d qy := by
    refine mem_matchQuery_of_lookup (fun v hv => ?_) (fun v hv t ht => ?_) (fun p hp => ?_)
    · obtain ⟨t, ht, -⟩ := hlkv v hv; rw [ht]; rfl
    · obtain ⟨u, hu, hval⟩ := hlkv v hv
      rw [ht] at hu; exact (Option.some.inj hu) ▸ hval
    · have hp2 : p = Pattern.values [.var "@e", .var "@p"] (viewName f) (rebuildVars k) ∨
          p = Pattern.values [.var "@x", .var "@q"] ufName [.var ("@c" ++ toString i)] := by
        simpa [hqy, columnRule] using hp
      rcases hp2 with rfl | rfl
      · refine patternHolds_values_of_mem_rows hmg ?_ ?_ hrow hterm
        · refine evalList_rebuildVars hlen (fun j hj => ?_)
          rw [hr₁ _ (Or.inr (Or.inr (by
            rw [rebuildVarNames, List.mem_map]
            exact ⟨j, List.mem_range.mpr hj, rfl⟩))), lookup_eclassSubst_col hlen hj]
        · exact Expr.evalList_pair_var (hr₁ _ (Or.inl rfl) ▸ lookup_eclassSubst_e)
            (hr₁ _ (Or.inr (Or.inl rfl)) ▸ lookup_eclassSubst_p)
      · refine patternHolds_values_of_mem_rows hmguf ?_ ?_ huf htermu
        · refine Expr.evalList_single_var ?_
          rw [hr₂ _ (Or.inr (Or.inr rfl)), lookup_eclassSubst_col hlen hi, hcieq]
        · exact Expr.evalList_pair_var (hr₂ _ (Or.inl rfl) ▸ lookup_eclassSubst_x)
            (hr₂ _ (Or.inr (Or.inl rfl)) ▸ lookup_eclassSubst_q)
  have hcs : Expr.evalList d.sig ((rebuildVars k).set i (.var "@x"))
      (d.env ++ Env.canon (Query.freeVars qy d.env) τ) = some (as.set i x) := by
    refine evalList_rebuildVars_set hlen
      (by rw [hrq _ (Or.inr (Or.inr (Or.inl rfl)))]; exact lookup_eclassSubst_x)
      (fun j hj => ?_)
    rw [hrq _ (Or.inr (Or.inr (Or.inr (Or.inr (by
      rw [rebuildVarNames, List.mem_map]
      exact ⟨j, List.mem_range.mpr hj, rfl⟩))))), lookup_eclassSubst_col hlen hj]
  have hout : Expr.evalList d.sig
      [Expr.var "@e", transE (symE (congrE (congrChildren k i))) (.var "@p")]
      (d.env ++ Env.canon (Query.freeVars qy d.env) τ)
      = some [e, columnProof k i pf q] := by
    rw [Expr.evalList, Expr.eval, hrq _ (Or.inl rfl), lookup_eclassSubst_e,
      Option.bind_some, Expr.evalList,
      eval_columnProof (by rw [hb.sig]; exact hfi) (by rw [hb.sig]; exact hsy)
        (by rw [hb.sig]; exact hcg) (by rw [hb.sig]; exact htr)
        (by rw [hrq _ (Or.inr (Or.inl rfl))]; exact lookup_eclassSubst_p)
        (by rw [hrq _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact lookup_eclassSubst_q),
      Option.bind_some, Expr.evalList]
    rfl
  refine mem_rows_execRunRules.mpr (Or.inr ⟨columnRule f k i,
    hb.held _ (columnRule_mem_maintenanceRules hfk hi), rfl, _, hσ,
    { FDatabase.addRow (viewName f) (as.set i x) [e, columnProof k i pf q]
        { d with env := d.env ++ Env.canon (Query.freeVars qy d.env) τ } with
      env := d.env, rules := d.rules }, ?_, mem_addRow_rows_self⟩)
  change execLocalActions d (columnRule f k i).actions _ = some _
  rw [columnRule, execLocalActions]
  simp only [execActions, Egglog.execAction, hcs, Option.bind_some, hout, Option.map_some]

/-- **The fixpoint's roots**: at a rebuild fixpoint no surviving view row's e-class column has an
outgoing `@UF` row. The firing is `eclassRule_fires`, and `FDatabase.RowColumnsValued` — that a
row's columns are terms `matchQuery` will assign — is `execM_rowColumnsValued` at an `execM`
target. -/
theorem no_ufRowEdge_of_rowsClosed {P : Program} {d d' : FDatabase} (hdom : P.EncodeDomain)
    (hb : d.EncBase P (encodeSig P)) (hsy : (encodeSig P).IsCtor symName)
    (htr : (encodeSig P).IsCtor transName) (hcv : d.RowColumnsValued)
    (hset : d.settled = true) (hdes : d.UFRowsDescend)
    (hclosed : d.RowsClosed rebuildRuleset) (hround : d.runRoundM rebuildRuleset = some d')
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors)
    {as : List Term} {e pf x : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows) (hedge : d.UFRowEdge e x) :
    False := by
  have hsigd : d.sig = encodeSig P := hb.sig
  have hdecl : (encodeSig P) (viewName f) = some (viewDecl k) :=
    (encodeSig_tables hdom hdom.aritiesAgree' hfk).1
  have hdcm : (viewDecl k).merge = some (MergeSpec.merge mergeBody mergeResult) := rfl
  have hmgne : d.sig.mergeOf (viewName f) ≠ none := by
    rw [Signature.mergeOf, hsigd, hdecl, Option.bind_some, hdcm]; simp
  have hlen : as.length = k :=
    (hb.inv.index.width ⟨viewName f, as, [e, pf]⟩ hrow (viewDecl k)
      (by rw [hsigd]; exact hdecl) hmgne).1
  obtain ⟨q, hufrow⟩ := hedge.1
  have hfired : (⟨viewName f, as, [x, Term.app transName [pf, q]]⟩ : Row) ∈
      (execRunRules rebuildRuleset d).rows :=
    eclassRule_fires hb htr hcv hfk
      (by rw [Option.isSome_iff_ne_none]; exact hmgne)
      (by
        rw [Option.isSome_iff_ne_none, Signature.mergeOf, hsigd, encodeSig_ufName hdom,
          Option.bind_some]
        simp [ufDecl])
      hlen hrow hufrow
  have hshape : Signature.MergeShape d.sig := by rw [hsigd]; exact hb.shape
  have hlegal : Signature.MergesLegal d.sig := by rw [hsigd]; exact hb.merges
  have hsigR : (execRunRules rebuildRuleset d).sig = d.sig := FDatabase.execRunRules_fields.1
  -- the merge phase leaves a row at the key, at or below the column the firing wrote
  rw [FDatabase.runRoundM] at hround
  have hcarry := mergeSaturateF_rowsDescendCarry mergeFuel
    (by rw [hsigR]; exact hshape) (by rw [hsigR]; exact hlegal)
    (hb.inv.execRunRules hb.wl') (execRunRules_noUnions hb.nounions) hround
  obtain ⟨v, lo, hv, hle⟩ := hcarry (viewName f) as x (Term.app transName [pf, q]) hfired
  rw [hclosed d' (by rw [FDatabase.runRoundM]; exact hround)] at hv
  -- and a settled state carries at most one row per view key
  have hout : ([e, pf] : List Term) = [v, lo] :=
    FDatabase.row_unique_of_settled hset hshape hlegal hb.inv
      (fun p hp => diag_closureF hb.eqsRefl hp) (by rw [hsigd]; exact hsy)
      (by rw [hsigd]; exact htr) (by rw [hsigd]; exact hdecl) hdcm
      (fun hc => viewName_ne_ufName hc)
      (rowArgs_mem_closureF hb.eqsRefl hb.inv.index hb.subtermClosed
        ⟨viewName f, as, [e, pf]⟩ hrow hmgne)
      hrow hv
  obtain rfl : e = v := (List.cons.inj hout).1
  -- the edge descends, and the survivor does not
  have hxe : Term.blt x e = true := hdes e x hedge
  rcases hle with rfl | hlt
  · exact hedge.2 rfl
  · rw [Term.blt_asymm x e hxe] at hlt
    exact absurd hlt (by simp)


/-! ## The columns a row records, run-wide

`FDatabase.RowColumnsValued` is the fourth cost of the e-class rule's firing and the one
hypothesis `no_ufRowEdge_of_rowsClosed` still carries. What places a column in
`FDatabase.valueTerms` is a fact about `terms` alone, and it needs nothing syntactic: a
`Term.app` only ever reaches `terms` through `Expr.eval`, whose application case is guarded by
`Signature.IsCtor` — a *declared* name with no `:merge`. So every term any action evaluates is
a value, and an entry term reaches `terms` only as the top of what `FDatabase.addRow` mints.
`FDatabase.Valued` is that invariant, and it is carried over the same writers
`FDatabase.EntryRowsUF` is. -/

/-- **A term a rule variable may be bound to**: a literal, or an application of a name that
carries no `:merge`. `FDatabase.valueTerms` is this test over `terms`. -/
def Term.IsValue (sig : Signature) : Term → Prop
  | .lit _ => True
  | .app f _ => sig.mergeOf f = none

@[simp] theorem Term.isValue_lit {sig : Signature} {l : Lit} : Term.IsValue sig (.lit l) := trivial

@[simp] theorem Term.isValue_app {sig : Signature} {f : FnName} {as : List Term} :
    Term.IsValue sig (.app f as) ↔ sig.mergeOf f = none := Iff.rfl

/-- **No argument of any subterm of `t` is an entry term.** Stated over `Term.subtermList`
rather than by recursion, for the reason `Term.LitFree` is: the argument list makes a direct
recursion on `Term` awkward and every consumer reads it at a subterm anyway. -/
def Term.ArgsValue (sig : Signature) (t : Term) : Prop :=
  ∀ s ∈ t.subtermList, ∀ f as, s = Term.app f as → ∀ a ∈ as, Term.IsValue sig a

theorem Term.argsValue_lit {sig : Signature} {l : Lit} : Term.ArgsValue sig (.lit l) := by
  intro s hs f as hsf a ha
  rw [Term.subtermList_lit, List.mem_singleton] at hs
  exact absurd (hs ▸ hsf) (by simp)

/-- An application whose arguments are values with valued arguments. -/
theorem Term.argsValue_app {sig : Signature} {f : FnName} {ts : List Term}
    (hv : ∀ a ∈ ts, Term.IsValue sig a) (ha : ∀ a ∈ ts, Term.ArgsValue sig a) :
    Term.ArgsValue sig (Term.app f ts) := by
  intro s hs g bs hsg a hab
  rw [Term.subtermList_app, List.mem_cons] at hs
  rcases hs with rfl | hs
  · obtain ⟨rfl, rfl⟩ : f = g ∧ ts = bs := by
      injection hsg with h₁ h₂; exact ⟨h₁, h₂⟩
    exact hv a hab
  · obtain ⟨u, hu, hsub⟩ := (Term.mem_subtermListL ts).mp hs
    exact ha u hu s ((Term.mem_subtermList u).mpr hsub) g bs hsg a hab

/-- A subterm of a term with valued arguments has them too. -/
theorem Term.ArgsValue.subterm {sig : Signature} {t s : Term} (h : Term.ArgsValue sig t)
    (hs : s ∈ t.subtermList) : Term.ArgsValue sig s :=
  fun u hu => h u ((Term.mem_subtermList t).mpr
    (((Term.mem_subtermList s).mp hu).trans ((Term.mem_subtermList t).mp hs)))

/-- The arguments themselves, read off the top. -/
theorem Term.ArgsValue.args {sig : Signature} {f : FnName} {as : List Term}
    (h : Term.ArgsValue sig (Term.app f as)) : ∀ a ∈ as, Term.IsValue sig a :=
  fun a ha => h _ ((Term.mem_subtermList _).mpr (.refl _)) f as rfl a ha

/-- `FDatabase.valueTerms` split into its two conditions. -/
theorem FDatabase.mem_valueTerms_iff {d : FDatabase} {t : Term} :
    t ∈ d.valueTerms ↔ t ∈ d.terms ∧ Term.IsValue d.sig t := by
  rw [FDatabase.valueTerms, List.mem_filter]
  constructor
  · rintro ⟨hm, hb⟩
    refine ⟨hm, ?_⟩
    cases t with
    | lit l => trivial
    | app f as => exact Option.isNone_iff_eq_none.mp (by simpa using hb)
  · rintro ⟨hm, hv⟩
    refine ⟨hm, ?_⟩
    cases t with
    | lit l => rfl
    | app f as =>
      change (d.sig.mergeOf f).isNone = true
      rw [Term.isValue_app.mp hv]
      rfl

/-- **Every argument of every term the state holds is a value, and so is every term its
environment binds.** The invariant `FDatabase.RowColumnsValued` is read off. -/
structure FDatabase.Valued (d : FDatabase) : Prop where
  /-- No argument of a term the state holds is an entry term. -/
  terms : ∀ t ∈ d.terms, Term.ArgsValue d.sig t
  /-- Nor is anything the environment binds. -/
  env : ∀ b ∈ d.env, Term.IsValue d.sig b.2 ∧ Term.ArgsValue d.sig b.2

/-! ### Evaluation lands in the values

No syntactic hypothesis on the expression: `Expr.eval`'s application case demands
`Signature.IsCtor`, which is a declaration whose `merge` is `none`, and its primitive case
answers with a literal or with an operand (`prim_apply_cases`). -/

mutual

/-- **An expression evaluates to a value with valued arguments**, in an environment that binds
only such terms. -/
theorem isValue_of_eval {sig : Signature} {ρ : Env}
    (hρ : ∀ b ∈ ρ, Term.IsValue sig b.2 ∧ Term.ArgsValue sig b.2) :
    ∀ (e : Expr) {t : Term}, e.eval sig ρ = some t →
      Term.IsValue sig t ∧ Term.ArgsValue sig t
  | .lit l, t, h => by
      obtain rfl : t = Term.lit l := (Option.some.inj h).symm
      exact ⟨Term.isValue_lit, Term.argsValue_lit⟩
  | .var v, t, h => by
      rw [Expr.eval] at h
      exact hρ (v, t) (Env.mem_of_lookup h)
  | .app f args, t, h => by
      cases hp : Prim.ofName f with
      | some p =>
          simp only [Expr.eval, hp] at h
          obtain ⟨ts, hargs, hap⟩ := Option.bind_eq_some_iff.mp h
          have hts := isValue_of_evalList hρ args hargs
          rcases prim_apply_cases hap with ⟨l, rfl⟩ | hmem
          · exact ⟨Term.isValue_lit, Term.argsValue_lit⟩
          · exact hts t hmem
      | none =>
          simp only [Expr.eval, hp] at h
          by_cases hct : sig.IsCtor f
          · rw [if_pos hct] at h
            obtain ⟨ts, hargs, happ⟩ := Option.map_eq_some_iff.mp h
            have hts := isValue_of_evalList hρ args hargs
            obtain rfl : Term.app f ts = t := happ
            obtain ⟨dc, hdc, hmg⟩ := hct
            exact ⟨Term.isValue_app.mpr (by rw [Signature.mergeOf, hdc, Option.bind_some, hmg]),
              Term.argsValue_app (fun a ha => (hts a ha).1) (fun a ha => (hts a ha).2)⟩
          · rw [if_neg hct] at h
            exact absurd h (by simp)

@[inherit_doc isValue_of_eval]
theorem isValue_of_evalList {sig : Signature} {ρ : Env}
    (hρ : ∀ b ∈ ρ, Term.IsValue sig b.2 ∧ Term.ArgsValue sig b.2) :
    ∀ (es : List Expr) {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ u ∈ ts, Term.IsValue sig u ∧ Term.ArgsValue sig u
  | [], ts, h => by
      rw [Expr.evalList, Option.some.injEq] at h
      subst h
      intro u hu
      simp at hu
  | e :: es, ts, h => by
      rw [Expr.evalList] at h
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact isValue_of_eval hρ e ht
      · exact isValue_of_evalList hρ es hus u hu'

end

/-! ### The writers -/

/-- `FDatabase.Valued` reads `sig`, `terms` and `env`; the rule list may be replaced freely. -/
theorem FDatabase.Valued.setRules {d : FDatabase} (h : d.Valued) (rs : List Rule) :
    ({ d with rules := rs } : FDatabase).Valued where
  terms := h.terms
  env := h.env

/-- **And the environment may be replaced by any binding of values.** -/
theorem FDatabase.Valued.setEnv {d : FDatabase} (h : d.Valued) {σ : Env} {rs : List Rule}
    (hσ : ∀ b ∈ σ, Term.IsValue d.sig b.2 ∧ Term.ArgsValue d.sig b.2) :
    ({ d with env := σ, rules := rs } : FDatabase).Valued where
  terms := h.terms
  env := hσ

/-- **One `addTerm`**: the terms it records are subterms of one whose arguments are values. -/
theorem FDatabase.Valued.addTerm {d : FDatabase} (h : d.Valued) {t : Term}
    (ht : Term.ArgsValue d.sig t) : (d.addTerm t).Valued where
  terms := by
    intro s hs
    rcases FDatabase.mem_addTerm_terms.mp hs with hs' | hs'
    · exact ht.subterm hs'
    · exact h.terms s hs'
  env := h.env

/-- **One `addRow`**: the entry term it mints has the written columns as its arguments. -/
theorem FDatabase.Valued.addRow {d : FDatabase} (h : d.Valued) {g : FnName} {as vs : List Term}
    (hc : ∀ c ∈ as ++ vs, Term.IsValue d.sig c ∧ Term.ArgsValue d.sig c) :
    (FDatabase.addRow g as vs d).Valued :=
  let h' := h.addTerm (t := Term.app g (as ++ vs))
    (Term.argsValue_app (fun a ha => (hc a ha).1) (fun a ha => (hc a ha).2))
  ⟨h'.terms, h'.env⟩

/-- **The firing fold's union.** -/
theorem FDatabase.Valued.union {d₁ d₂ : FDatabase} (h₁ : d₁.Valued) (h₂ : d₂.Valued)
    (hsig : d₂.sig = d₁.sig) : (d₁.union d₂).Valued where
  terms := by
    intro t ht
    rcases FDatabase.mem_terms_union.mp ht with ht' | ht'
    · exact h₁.terms t ht'
    · exact hsig ▸ h₂.terms t ht'
  env := h₁.env

/-- **One action.** `expr`, `letBind` and `union` record evaluated terms; the `set` records the
entry term for the columns it evaluated. -/
theorem execAction_valued {d d' : FDatabase} {a : Action} (h : d.Valued)
    (hrun : execAction d a = some d') : d'.Valued := by
  cases a with
  | expr e =>
    simp only [execAction, Option.map_eq_some_iff] at hrun
    obtain ⟨t, ht, rfl⟩ := hrun
    exact h.addTerm (isValue_of_eval h.env e ht).2
  | letBind v e =>
    simp only [execAction, Option.map_eq_some_iff] at hrun
    obtain ⟨t, ht, rfl⟩ := hrun
    have hv := isValue_of_eval h.env e ht
    refine ⟨(h.addTerm hv.2).terms, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hv
    · exact h.env b hb'
  | union e₁ e₂ =>
    simp only [execAction] at hrun
    obtain ⟨t₁, ht₁, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨t₂, ht₂, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    split at hrun
    · exact absurd hrun (by simp)
    · rw [Option.some.injEq] at hrun
      subst hrun
      have h₁ : (d.addTerm t₁).Valued := h.addTerm (isValue_of_eval h.env e₁ ht₁).2
      have h₂ : ((d.addTerm t₁).addTerm t₂).Valued :=
        h₁.addTerm (d := FDatabase.addTerm t₁ d) (isValue_of_eval h.env e₂ ht₂).2
      exact ⟨h₂.terms, h₂.env⟩
  | set f args out =>
    obtain ⟨as, vs, has, hvs, rfl⟩ := execAction_set hrun
    refine h.addRow (fun c hc => ?_)
    rcases List.mem_append.mp hc with hc' | hc'
    · exact isValue_of_evalList h.env args has c hc'
    · exact isValue_of_evalList h.env out hvs c hc'

/-- **A block of them.** -/
theorem execActions_valued : ∀ (as : List Action) {d d' : FDatabase}, d.Valued →
    execActions d as = some d' → d'.Valued
  | [], _, _, h, hrun => by
      rw [execActions, Option.some.injEq] at hrun; exact hrun ▸ h
  | a :: as, d, d', h, hrun => by
      rw [execActions] at hrun
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hrun
      exact execActions_valued as (execAction_valued h h₁) h₂

/-- **One firing.** The substitution binds only `FDatabase.valueTerms`, which is exactly the
condition the environment owes. -/
theorem execLocalActions_valued {d d' : FDatabase} {as : List Action} {σ : Env} (h : d.Valued)
    (hσ : ∀ b ∈ σ, Term.IsValue d.sig b.2 ∧ Term.ArgsValue d.sig b.2)
    (hrun : execLocalActions d as σ = some d') : d'.Valued := by
  rw [execLocalActions] at hrun
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hrun
  have hd : ({ d with env := d.env ++ σ } : FDatabase).Valued := by
    refine ⟨h.terms, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.env b hb'
    · exact hσ b hb'
  have hm' := execActions_valued as hd hm
  have hsig : m.sig = d.sig := FDatabase.execActions_sig (d := { d with env := d.env ++ σ }) hm
  refine hm'.setEnv (fun b hb => ?_)
  rw [hsig]
  exact h.env b hb

/-- **Every binding a matched substitution makes is a value whose arguments are values**: the
first is what `matchQuery` enumerates, the second is the invariant at the term it picked. -/
theorem matchQuery_valued {d : FDatabase} {q : Query} {σ : Env} (h : d.Valued)
    (hσ : σ ∈ matchQuery d q) :
    ∀ b ∈ σ, Term.IsValue d.sig b.2 ∧ Term.ArgsValue d.sig b.2 := by
  intro b hb
  have hv := (mem_assignments.mp (List.mem_of_mem_filter hσ)).2 b hb
  obtain ⟨hmem, hval⟩ := FDatabase.mem_valueTerms_iff.mp hv
  exact ⟨hval, h.terms _ hmem⟩

/-- One firing, unioned into the accumulator. -/
theorem fireInto_valued {d acc : FDatabase} {r : Rule} {σ : Env} (h : d.Valued)
    (hσ : σ ∈ matchQuery d r.query) (hsig : acc.sig = d.sig) (ha : acc.Valued) :
    (fireInto d r acc σ).sig = d.sig ∧ (fireInto d r acc σ).Valued := by
  rw [fireInto]
  cases hx : execLocalActions d r.actions σ with
  | none => exact ⟨hsig, ha⟩
  | some e =>
    exact ⟨hsig, ha.union (execLocalActions_valued h (matchQuery_valued h hσ) hx)
      ((execLocalActions_sig hx).trans hsig.symm)⟩

/-- Every match of one rule. -/
theorem foldl_fireInto_valued {d : FDatabase} {r : Rule} (h : d.Valued) :
    ∀ (σs : List Env), (∀ σ ∈ σs, σ ∈ matchQuery d r.query) →
      ∀ {acc : FDatabase}, acc.sig = d.sig → acc.Valued →
        (σs.foldl (fireInto d r) acc).sig = d.sig ∧ (σs.foldl (fireInto d r) acc).Valued
  | [], _, _, hsig, ha => ⟨hsig, ha⟩
  | σ :: σs, hsub, _, hsig, ha =>
      foldl_fireInto_valued h σs (fun τ hτ => hsub τ (List.mem_cons_of_mem _ hτ))
        (fireInto_valued h (hsub σ List.mem_cons_self) hsig ha).1
        (fireInto_valued h (hsub σ List.mem_cons_self) hsig ha).2

@[inherit_doc foldl_fireInto_valued]
theorem fireRule_valued {d acc : FDatabase} {r : Rule} (h : d.Valued) (hsig : acc.sig = d.sig)
    (ha : acc.Valued) : (fireRule d acc r).sig = d.sig ∧ (fireRule d acc r).Valued :=
  foldl_fireInto_valued h _ (fun _ hm => hm) hsig ha

/-- The round's fold. -/
theorem foldl_fireRule_valued {d : FDatabase} (h : d.Valued) :
    ∀ (rs : List Rule) {acc : FDatabase}, acc.sig = d.sig → acc.Valued →
      (rs.foldl (fireRule d) acc).sig = d.sig ∧ (rs.foldl (fireRule d) acc).Valued
  | [], _, hsig, ha => ⟨hsig, ha⟩
  | _ :: rs, _, hsig, ha =>
      foldl_fireRule_valued h rs (fireRule_valued h hsig ha).1 (fireRule_valued h hsig ha).2

/-- **One round of rule firing.** -/
theorem execRunRules_valued {R : RulesetName} {d : FDatabase} (h : d.Valued) :
    (execRunRules R d).Valued :=
  (foldl_fireRule_valued h _ rfl h).2

/-! ### The merge phase -/

/-- **Every row is the argument tuple of a term the state holds**, whether it is a constructor
row (`FDatabase.IndexOk.ctor`, whose value columns are empty) or an entry row
(`mem_terms_of_indexOk`, read at a state that asserts nothing). -/
theorem mem_terms_of_row {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk) {r : Row}
    (hm : r ∈ d.rows) : Term.app r.fn (r.args ++ r.out) ∈ d.terms := by
  by_cases hmg : d.sig.mergeOf r.fn = none
  · obtain ⟨hout, hmem⟩ := hidx.ctor r hm hmg
    rw [hout]
    simpa using hmem
  · exact mem_terms_of_indexOk hr hidx hm hmg

/-- **A row's columns are values whose arguments are values.** Both halves come off that term:
the columns are its arguments. -/
theorem FDatabase.Valued.rowColumns {d : FDatabase} (h : d.Valued) (hr : d.EqsRefl)
    (hidx : d.IndexOk) {r : Row} (hm : r ∈ d.rows) :
    ∀ c ∈ r.args ++ r.out, Term.IsValue d.sig c ∧ Term.ArgsValue d.sig c := by
  have key := mem_terms_of_row hr hidx hm
  intro c hc
  exact ⟨(h.terms _ key).args c hc,
    (h.terms _ key).subterm ((Term.mem_subtermList _).mpr (Term.IsSubterm.arg hc (.refl c)))⟩

/-- **The invariant in the form the e-class rule's firing consumes.** -/
theorem FDatabase.Valued.rowColumnsValued {d : FDatabase} (h : d.Valued) (hr : d.EqsRefl)
    (hsc : d.SubtermClosed) (hidx : d.IndexOk) : d.RowColumnsValued := fun _ hm c hc =>
  FDatabase.mem_valueTerms_iff.mpr
    ⟨FDatabase.mem_terms_of_column hsc (mem_terms_of_row hr hidx hm) hc,
      (h.rowColumns hr hidx hm c hc).1⟩

/-- **One merge firing.** The skip branch writes nothing; the body runs in an environment the
two colliding rows' value columns make, and the survivor's entry term is the resident row's key
with whatever `res` evaluated to. -/
theorem mergeOneOriented_valued {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (h : d.Valued)
    (hfire : d.mergeOneOriented cl r₁ r₂ = some e) : e.Valued := by
  obtain ⟨hmem₁, hmem₂, -, -⟩ := mergeOneOriented_mem_rows hfire
  have hcol₁ := h.rowColumns hr hidx hmem₁
  have hcol₂ := h.rowColumns hr hidx hmem₂
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    split at hfire
    next =>
      split at hfire
      next =>
        rw [Option.some.injEq] at hfire
        subst hfire
        exact ⟨h.terms, h.env⟩
      next =>
        obtain ⟨m, hmb, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp hfire
        subst he
        have hd : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).Valued := by
          refine ⟨h.terms, fun b hb => ?_⟩
          rcases mem_mergeEnv hb with hb' | hb'
          · exact hcol₂ b.2 (List.mem_append_right _ hb')
          · exact hcol₁ b.2 (List.mem_append_right _ hb')
        have hm' := execActions_valued body hd hmb
        have hsig : m.sig = d.sig :=
          FDatabase.execActions_sig (d := { d with env := mergeEnv r₂.out r₁.out }) hmb
        have hvsv : ∀ c ∈ vs, Term.IsValue m.sig c ∧ Term.ArgsValue m.sig c :=
          isValue_of_evalList hm'.env res hvs
        have hcols : ∀ c ∈ r₂.args ++ vs,
            Term.IsValue m.sig c ∧ Term.ArgsValue m.sig c := by
          intro c hc
          rcases List.mem_append.mp hc with hc' | hc'
          · rw [hsig]
            exact hcol₂ c (List.mem_append_left _ hc')
          · exact hvsv c hc'
        have hadd : (m.addTerm (.app r₂.fn (r₂.args ++ vs))).Valued :=
          hm'.addTerm (Term.argsValue_app (fun a ha => (hcols a ha).1)
            (fun a ha => (hcols a ha).2))
        refine ⟨hadd.terms, fun b hb => ?_⟩
        exact (show m.sig = d.sig from hsig) ▸ h.env b hb
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

/-- **The same, at whichever orientation `FDatabase.mergeOneWith` chose.** -/
theorem mergeOneWith_valued {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hr : d.EqsRefl) (hidx : d.IndexOk) (h : d.Valued)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.Valued := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · exact mergeOneOriented_valued hr hidx h (he ▸ hm)
  · exact mergeOneOriented_valued hr hidx h (he ▸ hm)

/-- **A merge pass.** The rebuild writes `rows` alone, so it costs nothing here. -/
theorem mergeRound_valued {d : FDatabase} (hlegal : Signature.MergesLegal d.sig) (hinv : d.Inv)
    (hn : d.NoUnions) (h : d.Valued) : d.mergeRound.Valued := by
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      d.mergeRound.Valued := by
    refine FDatabase.mergeRound_induction_ne
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ x.Valued)
      ⟨hinv, rfl, hn, h⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        ⟨h.terms, h.env⟩⟩ ?_
    intro x y r₁ r₂ _ hx hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_valued hx.2.2.1.eqsRefl hx.1.index hx.2.2.2 hy
  exact key.2.2.2

/-- **And the whole merge phase.** -/
theorem mergeSaturateF_valued : ∀ (n : Nat) {d e : FDatabase},
    Signature.MergesLegal d.sig → d.Inv → d.NoUnions → d.Valued →
      FDatabase.mergeSaturateF n d = some e → e.Valued
  | 0, d, e, _, _, _, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · exact absurd hrun (by simp)
  | n + 1, d, e, hlegal, hinv, hn, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_valued n (by rw [hsig]; exact hlegal)
          (FDatabase.Inv.mergeRound_of_legalMerges hinv hlegal) (mergeRound_noUnions hn)
          (mergeRound_valued hlegal hinv hn h) hrun

/-- **And a whole round**, rule firing followed by the merge phase. -/
theorem runRoundM_valued {R : RulesetName} {d e : FDatabase}
    (hlegal : Signature.MergesLegal d.sig) (hinv : d.Inv) (hn : d.NoUnions)
    (hwl : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig) (h : d.Valued)
    (hrun : d.runRoundM R = some e) : e.Valued := by
  rw [FDatabase.runRoundM] at hrun
  refine mergeSaturateF_valued mergeFuel ?_ ?_ ?_ (execRunRules_valued h) hrun
  · rw [FDatabase.execRunRules_fields.1]; exact hlegal
  · exact hinv.execRunRules hwl
  · exact execRunRules_noUnions hn

/-! ### The run -/

/-- **Rounds of one ruleset.** -/
theorem FDatabase.EncBase.runSaturateM_valued {P : Program} {R : RulesetName} :
    ∀ (n : Nat) {d d' : FDatabase}, d.EncBase P (encodeSig P) → d.Valued →
      d.runSaturateM R n = some d' → d'.Valued := by
  intro n d d' hb h hrun
  refine (runSaturateM_closed (R := R)
    (Φ := fun x => x.EncBase P (encodeSig P) ∧ x.Valued) ?_ n ⟨hb, h⟩ hrun).2
  intro x y hx hstep
  have hstep' : x.execCmdM (Cmd.run R) = some y := hstep
  refine ⟨hx.1.execCmdM (c := Cmd.run R) trivial trivial trivial trivial trivial hstep', ?_⟩
  exact runRoundM_valued (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl'
    hx.2 hstep

/-- **One command of the aligned run.** -/
theorem FDatabase.EncBase.execCmdM_valued {P : Program} {d d' : FDatabase} {c : Cmd}
    (hb : d.EncBase P (encodeSig P)) (huf : c.UnionFree) (hnd : c.NoDecl)
    (hwl : c.WriteLegal (encodeSig P)) (h : d.Valued) (hs : d.execCmdM c = some d') :
    d'.Valued := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    have hsig₁ : d₁.sig = d.sig := FDatabase.execAction_sig h₁
    refine mergeSaturateF_valued mergeFuel ?_ ?_ ?_ (execAction_valued h h₁) h₂
    · rw [hsig₁, hb.sig]; exact hb.merges
    · exact hb.inv.execAction (by rw [hb.sig]; exact hwl) h₁
    · exact execAction_noUnions huf hb.nounions h₁
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.setRules (r :: d.rules)
  | run R =>
    rw [FDatabase.execCmdM] at hs
    exact runRoundM_valued (by rw [hb.sig]; exact hb.merges) hb.inv hb.nounions hb.wl' h hs
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact FDatabase.EncBase.runSaturateM_valued runFuel hb h hs
  | decl f dc => exact (hnd : False).elim

/-- **A block of them.** -/
theorem FDatabase.EncBase.execProgramM_valued {P : Program} {p : Program}
    (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal (encodeSig P))
    (hlet : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.EncBase P (encodeSig P) → d.Valued →
      d.execProgramM p = some D → D.Valued := by
  induction p with
  | nil =>
    intro d D _ h hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro d D hb h hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (hb.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self) h₁)
      (hb.execCmdM_valued (huf c List.mem_cons_self) (hnd c List.mem_cons_self)
        (hwl c List.mem_cons_self) h h₁) h₂

/-- **The invariant at the state `execM` returned.** The prelude declares and asserts nothing,
so it starts at a state with no term and no binding at all. -/
theorem execM_encode_valued {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.Valued := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  have h₀ : d₀.Valued := by
    refine ⟨fun t ht => ?_, fun b hb => ?_⟩
    · rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at ht
      exact absurd ht (by simp)
    · rw [hdata.2.2.2, show FDatabase.empty.env = ([] : Env) from rfl] at hb
      exact absurd hb (by simp)
  refine FDatabase.EncBase.execProgramM_valued
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ h₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **`FDatabase.EncBase` at the state `execM` returned**, which is the prelude's instance
carried along `encodeCmds` by `FDatabase.EncBase.execProgramM`. -/
theorem execM_encode_encBase {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.EncBase P (encodeSig P) := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  refine FDatabase.EncBase.execProgramM
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **The fourth cost of the e-class rule's firing, discharged run-wide**: every column an
`execM` target's rows record is a term `matchQuery` will assign, so a rebuild rule can re-read
the rows the fixpoint's roots argument contradicts against.

`cxRb_rowColumnsValued` is the same property decided at the state the one-off match runs at. -/
theorem execM_rowColumnsValued {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.RowColumnsValued :=
  have hb := execM_encode_encBase hdom hdom.aritiesAgree' htgt
  (execM_encode_valued hdom hdom.aritiesAgree' htgt).rowColumnsValued hb.eqsRefl
    hb.subtermClosed hb.inv.index




/-! ## Descent over entry terms, run-wide

`FDatabase.ufRowRoot_of_ufReach` — the identification the residue's three clauses spend, entry
reachability and row reachability landing on one `@UF` row root — rests on one thing this file
does not yet supply: `FDatabase.UFTermsDescend`, the `terms` counterpart of
`execM_ufRowsDescend`. It is true for the reason that one is, and the reason is that **descent
is a property of the write and not of currency**: `FDatabase.addRow` mints the entry term for
the very row it writes, and no writer removes a term, so an edge that descended when it was
written descends forever.

The induction is `execM_ufRowsDescend`'s, writer for writer, with one obligation added at each:
an action records the *subterms* of what it evaluates as well as the term itself, so the entry
terms it records other than the one its own `set` writes have to be ones the state already
holds. That obligation is `Action.EntrySafe`, and it is the one `FDatabase.EntryRowsUF`'s run
already carries — `entryShaped_mem_of_eval` and `entryShaped_mem_of_evalList` are how it is
paid, at exactly the sites they are paid there.

`pathCompressRule` is the one writer whose descent is not syntactic, and it reads **rows**
(`mem_rows_of_patternHolds_values`), so its case runs off `FDatabase.UFRowsDescend` exactly as
it does for rows. That is why the induction carries both. -/

namespace FDatabase

/-- **Descent reads `terms` and nothing else.** -/
theorem UFTermsDescend.of_terms_sub {d e : FDatabase} (h : d.UFTermsDescend)
    (hsub : ∀ t ∈ e.terms, t ∈ d.terms) : e.UFTermsDescend := by
  intro a b hedge
  obtain ⟨pf, hmem⟩ := hedge.1
  exact h a b ⟨⟨pf, hsub _ hmem⟩, hedge.2⟩

/-- **One `addTerm`.** It writes no entry term of its own, so the whole obligation is that the
`@UF`-shaped subterms it records are ones the state already holds. -/
theorem UFTermsDescend.addTerm' {d : FDatabase} (h : d.UFTermsDescend) {t : Term}
    (hsub : ∀ s ∈ t.subtermList, s.EntryShaped → s ∈ d.terms) :
    (d.addTerm t).UFTermsDescend := by
  refine ufTermsDescend_iff.mpr fun a b pf hmem => ?_
  rcases FDatabase.mem_addTerm_terms.mp hmem with hm | hm
  · exact ufTermsDescend_iff.mp h a b pf (hsub _ hm (Or.inr ⟨a, b, pf, rfl⟩))
  · exact ufTermsDescend_iff.mp h a b pf hm

/-- **One `set`, checked at the entry term it mints.** The key/value split is recovered from the
column count rather than assumed, since the entry term has lost it. -/
theorem UFTermsDescend.addRow' {d : FDatabase} {f : FnName} {as vs : List Term}
    (h : d.UFTermsDescend)
    (hnew : ∀ a b pf, Term.app f (as ++ vs) = Term.app ufName [a, b, pf] →
      b = a ∨ Term.blt b a = true)
    (hsub : ∀ c ∈ as ++ vs, ∀ s ∈ c.subtermList, s.EntryShaped → s ∈ d.terms) :
    (FDatabase.addRow f as vs d).UFTermsDescend := by
  refine ufTermsDescend_iff.mpr fun a b pf hmem => ?_
  rcases FDatabase.mem_addRow_terms.mp hmem with hm | hm
  · by_cases hq : Term.app ufName [a, b, pf] = Term.app f (as ++ vs)
    · exact hnew a b pf hq.symm
    · exact ufTermsDescend_iff.mp h a b pf
        (entryShaped_mem_of_columns hsub _ hm hq (Or.inr ⟨a, b, pf, rfl⟩))
  · exact ufTermsDescend_iff.mp h a b pf hm

/-- **A union of two descending states descends**, which is what `fireInto` costs. -/
theorem UFTermsDescend.union {d₁ d₂ : FDatabase} (h₁ : d₁.UFTermsDescend)
    (h₂ : d₂.UFTermsDescend) : (d₁.union d₂).UFTermsDescend := by
  refine ufTermsDescend_iff.mpr fun a b pf hmem => ?_
  rcases FDatabase.mem_terms_union.mp hmem with hm | hm
  · exact ufTermsDescend_iff.mp h₁ a b pf hm
  · exact ufTermsDescend_iff.mp h₂ a b pf hm

end FDatabase

/-- **The bindings an action reads are terms the state holds**, which is what makes the
recorded-subterm obligation free at every variable. `execAction_entryRowsUF` pays it the same
way; it is named here because the descent induction pays it at the same four sites. -/
theorem entryShaped_bind_of_inv {d : FDatabase} (hinv : d.Inv) :
    ∀ (v : Var) (u : Term), Env.lookup v d.env = some u →
      ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms := by
  have hsc : d.SubtermClosed := FDatabase.SubtermClosed.of_wf hinv.wf
  intro v u hu
  have hb : (v, u).2 ∈ d.terms := by
    have h := hinv.wf.envInTerms (v, u)
      (by rw [FDatabase.toDatabase_env]; exact Env.mem_of_lookup hu)
    rwa [FDatabase.mem_toDatabase_terms] at h
  exact entryShaped_mem_of_held hsc hb

/-- **One action.** The three that record a term owe `Action.EntrySafe` alone; the `set` owes
that and the shape of its own write, which is `Action.UFWriteSafe`. -/
theorem execAction_ufTermsDescend {d e : FDatabase} {a : Action} (hinv : d.Inv)
    (hsafe : a.UFWriteSafe) (hentry : a.EntrySafe) (h : d.UFTermsDescend)
    (hs : execAction d a = some e) : e.UFTermsDescend := by
  have hbind := entryShaped_bind_of_inv hinv
  cases a with
  | expr e₀ =>
    simp only [execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact h.addTerm' (entryShaped_mem_of_eval e₀ hentry (fun w _ => hbind w) ht)
  | letBind v e₀ =>
    simp only [execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact (h.addTerm' (entryShaped_mem_of_eval e₀ hentry (fun w _ => hbind w) ht)).of_terms_sub
      (fun _ ht' => ht')
  | union e₁ e₂ =>
    simp only [execAction] at hs
    obtain ⟨t₁, ht₁, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨t₂, ht₂, hs⟩ := Option.bind_eq_some_iff.mp hs
    split at hs
    · exact absurd hs (by simp)
    · rw [Option.some.injEq] at hs
      subst hs
      have h₁ : (d.addTerm t₁).UFTermsDescend :=
        h.addTerm' (entryShaped_mem_of_eval e₁ hentry.1 (fun w _ => hbind w) ht₁)
      have h₂ : ((d.addTerm t₁).addTerm t₂).UFTermsDescend :=
        h₁.addTerm' (d := FDatabase.addTerm t₁ d)
          (fun s hs' hsh => FDatabase.mem_addTerm_of_mem (t := t₁)
            (entryShaped_mem_of_eval e₂ hentry.2 (fun w _ => hbind w) ht₂ s hs' hsh))
      exact h₂.of_terms_sub (fun _ ht' => ht')
  | set f args out =>
    obtain ⟨as, vs, has, hvs, rfl⟩ := execAction_set hs
    refine h.addRow' (fun a₀ b₀ pf₀ heq => ?_) (fun c hc => ?_)
    · rcases (hsafe : f ≠ ufName ∨ ∃ x y pf, args = [maxE x y] ∧ out = [minE x y, pf]) with
        hne | ⟨x, y, pfe, rfl, rfl⟩
      · exact absurd (Term.app.inj heq).1 hne
      · obtain ⟨mx, hmx, rfl⟩ := Expr.evalList_singleton has
        obtain ⟨mn, pv, hmn, -, rfl⟩ := Expr.evalList_pair hvs
        have hcols : [mx, mn, pv] = [a₀, b₀, pf₀] := (Term.app.inj heq).2
        obtain rfl : mx = a₀ := (List.cons.inj hcols).1
        obtain rfl : mn = b₀ := (List.cons.inj (List.cons.inj hcols).2).1
        exact minE_le_maxE hmx hmn
    · rcases List.mem_append.mp hc with hc' | hc'
      · exact entryShaped_mem_of_evalList args hentry.1 (fun w _ => hbind w) has c hc'
      · exact entryShaped_mem_of_evalList out hentry.2 (fun w _ => hbind w) hvs c hc'

/-- **A block of them.** -/
theorem execActions_ufTermsDescend : ∀ (as : List Action), (∀ a ∈ as, a.UFWriteSafe) →
    (∀ a ∈ as, a.EntrySafe) → ∀ {d e : FDatabase}, d.Inv → Actions.WriteLegal as d.sig →
      d.UFTermsDescend → execActions d as = some e → e.UFTermsDescend
  | [], _, _, _, _, _, _, h, hs => by
      rw [execActions, Option.some.injEq] at hs; exact hs ▸ h
  | a :: as, hsafe, hentry, d, e, hinv, hwl, h, hs => by
      rw [execActions] at hs
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
      have hsig : d₁.sig = d.sig := FDatabase.execAction_sig h₁
      exact execActions_ufTermsDescend as (fun b hb => hsafe b (List.mem_cons_of_mem _ hb))
        (fun b hb => hentry b (List.mem_cons_of_mem _ hb)) (hinv.execAction hwl.head h₁)
        (by rw [hsig]; exact hwl.tail)
        (execAction_ufTermsDescend hinv (hsafe a List.mem_cons_self)
          (hentry a List.mem_cons_self) h h₁) h₂

/-- **And one firing of a rule whose head is a block of them.** -/
theorem execLocalActions_ufTermsDescend {d e : FDatabase} {as : List Action} {σ : Env}
    (hinv : d.Inv) (hwl : Actions.WriteLegal as d.sig) (hsafe : ∀ a ∈ as, a.UFWriteSafe)
    (hentry : ∀ a ∈ as, a.EntrySafe) (hσ : ∀ b ∈ σ, b.2 ∈ d.terms) (h : d.UFTermsDescend)
    (hs : execLocalActions d as σ = some e) : e.UFTermsDescend := by
  rw [execLocalActions] at hs
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hinv' : ({ d with env := d.env ++ σ } : FDatabase).Inv := by
    refine hinv.setEnv (fun b hb => ?_)
    rw [FDatabase.mem_toDatabase_terms]
    rcases List.mem_append.mp hb with hb' | hb'
    · have h' := hinv.wf.envInTerms b (by rw [FDatabase.toDatabase_env]; exact hb')
      rwa [FDatabase.mem_toDatabase_terms] at h'
    · exact hσ b hb'
  exact (execActions_ufTermsDescend as hsafe hentry (d := { d with env := d.env ++ σ })
    hinv' hwl (h.of_terms_sub fun _ ht => ht) hm).of_terms_sub fun _ ht => ht


/-- **The bindings a firing reads**, at the environment a rule head runs in. -/
theorem entryShaped_bind_of_match {d : FDatabase} (hinv : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.terms) :
    ∀ (v : Var) (u : Term), Env.lookup v (d.env ++ σ) = some u →
      ∀ s ∈ u.subtermList, s.EntryShaped → s ∈ d.terms := by
  have hsc : d.SubtermClosed := FDatabase.SubtermClosed.of_wf hinv.wf
  intro v u hu
  refine entryShaped_mem_of_held hsc ?_
  rcases List.mem_append.mp (Env.mem_of_lookup hu) with hb | hb
  · have h := hinv.wf.envInTerms (v, u) (by rw [FDatabase.toDatabase_env]; exact hb)
    rwa [FDatabase.mem_toDatabase_terms] at h
  · exact hσ (v, u) hb

/-- **`pathCompressRule`'s firing descends over entry terms too**, by the same composition of
the two **rows** its query matched — `mem_rows_of_patternHolds_values` is what makes the reading
a live edge — with `Action.EntrySafe` for the subterms the head records. -/
theorem pathCompressRule_ufTermsDescend {d e : FDatabase} {σ : Env} (hinv : d.Inv)
    (hr : d.EqsRefl) (hmg : d.sig.mergeOf ufName ≠ none)
    (hentry : ∀ a ∈ pathCompressRule.actions, a.EntrySafe)
    (hdes : d.UFRowsDescend) (h : d.UFTermsDescend)
    (hσ : σ ∈ matchQuery d pathCompressRule.query)
    (hf : execLocalActions d pathCompressRule.actions σ = some e) : e.UFTermsDescend := by
  have hbind := entryShaped_bind_of_match hinv (mem_terms_of_mem_matchQuery hσ)
  obtain ⟨ts₁, us₁, ha₁, hv₁, hm₁⟩ := mem_rows_of_mem_matchQuery_values hr hσ
    (vs := [Expr.var "@b", Expr.var "@p"]) (f := ufName) (as := [Expr.var "@a"]) hmg
    (by simp [pathCompressRule])
  obtain ⟨va, hla, rfl⟩ := Expr.evalList_single ha₁
  obtain ⟨vb, vp, hlb, -, rfl⟩ := Expr.evalList_pair hv₁
  obtain ⟨ts₂, us₂, ha₂, hv₂, hm₂⟩ := mem_rows_of_mem_matchQuery_values hr hσ
    (vs := [Expr.var "@c", Expr.var "@q"]) (f := ufName) (as := [Expr.var "@b"]) hmg
    (by simp [pathCompressRule])
  obtain ⟨vb', hlb', rfl⟩ := Expr.evalList_single ha₂
  obtain ⟨vc, vq, hlc, -, rfl⟩ := Expr.evalList_pair hv₂
  obtain rfl : vb = vb' := Option.some.inj (hlb.symm.trans hlb')
  have hba : vb = va ∨ Term.blt vb va = true := FDatabase.ufRowsDescend_iff.mp hdes va vb vp hm₁
  have hcb : vc = vb ∨ Term.blt vc vb = true := FDatabase.ufRowsDescend_iff.mp hdes vb vc vq hm₂
  have hca : vc = va ∨ Term.blt vc va = true := by
    rcases hba with rfl | hba' <;> rcases hcb with rfl | hcb'
    · exact Or.inl rfl
    · exact Or.inr hcb'
    · exact Or.inr hba'
    · exact Or.inr (Term.blt_trans _ _ _ hcb' hba')
  have hact : pathCompressRule.actions
      = [Action.set ufName [Expr.var "@a"]
          [Expr.var "@c", transE (Expr.var "@p") (Expr.var "@q")]] := rfl
  have hsafe : (Action.set ufName [Expr.var "@a"]
      [Expr.var "@c", transE (Expr.var "@p") (Expr.var "@q")]).EntrySafe :=
    hentry _ (by rw [hact]; exact List.mem_cons_self)
  rw [hact, execLocalActions] at hf
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hf
  rw [execActions] at hm
  obtain ⟨m₁, hm₁', hm₂'⟩ := Option.bind_eq_some_iff.mp hm
  rw [execActions, Option.some.injEq] at hm₂'
  subst hm₂'
  obtain ⟨es, vsh, hes, hvsh, rfl⟩ := execAction_set hm₁'
  obtain ⟨va', hla', rfl⟩ := Expr.evalList_singleton hes
  obtain rfl : va = va' := Option.some.inj (hla.symm.trans hla')
  obtain ⟨vc', pf, hlc', -, rfl⟩ := Expr.evalList_pair hvsh
  obtain rfl : vc = vc' := Option.some.inj (hlc.symm.trans hlc')
  refine (FDatabase.UFTermsDescend.addRow' (d := { d with env := d.env ++ σ })
    (h.of_terms_sub fun _ hx => hx) ?_ ?_).of_terms_sub fun _ hx => hx
  · intro a₀ b₀ pf₀ heq
    have hcols : [va, vc, pf] = [a₀, b₀, pf₀] := (Term.app.inj heq).2
    obtain rfl : va = a₀ := (List.cons.inj hcols).1
    obtain rfl : vc = b₀ := (List.cons.inj (List.cons.inj hcols).2).1
    exact hca
  · intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · exact entryShaped_mem_of_evalList [Expr.var "@a"] hsafe.1 (fun w _ => hbind w) hes c hc'
    · exact entryShaped_mem_of_evalList
        [Expr.var "@c", transE (Expr.var "@p") (Expr.var "@q")] hsafe.2
        (fun w _ => hbind w) hvsh c hc'

/-- **Every maintenance rule's firing descends over entry terms.** -/
theorem maintenance_ufTermsDescend {P : Program} {d e : FDatabase} {r : Rule} {σ : Env}
    (hmem : r ∈ maintenanceRules P) (hinv : d.Inv) (hr : d.EqsRefl)
    (hmg : d.sig.mergeOf ufName ≠ none) (hwl : Actions.WriteLegal r.actions d.sig)
    (hdes : d.UFRowsDescend) (h : d.UFTermsDescend) (hσ : σ ∈ matchQuery d r.query)
    (hf : execLocalActions d r.actions σ = some e) : e.UFTermsDescend := by
  have hentry := maintenance_entrySafe hmem
  rw [maintenanceRules, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact pathCompressRule_ufTermsDescend hinv hr hmg hentry hdes h hσ hf
  · obtain ⟨fk, -, hmem⟩ := List.mem_flatMap.mp hmem
    exact execLocalActions_ufTermsDescend hinv hwl (rebuildRules_ufWriteSafe fk.1 fk.2 r hmem)
      hentry (mem_terms_of_mem_matchQuery hσ) h hf

/-- **What a round's firings owe entry-term descent.** -/
def FDatabase.FiringsUFTermsDescend (d : FDatabase) : Prop :=
  ∀ r ∈ d.rules, ∀ σ ∈ matchQuery d r.query, ∀ e : FDatabase,
    execLocalActions d r.actions σ = some e → e.UFTermsDescend

/-- **At an aligned state every firing descends over entry terms**: a source rule's head is
`encodeActions_ufWriteSafe` and `encodeRule_entrySafe`, a maintenance rule's is
`maintenance_ufTermsDescend`. -/
theorem FDatabase.EncBase.firingsUFTermsDescend {P : Program} (hdom : P.EncodeDomain)
    {d : FDatabase} (hb : d.EncBase P (encodeSig P)) (hdes : d.UFRowsDescend)
    (h : d.UFTermsDescend) : d.FiringsUFTermsDescend := by
  have hmg : d.sig.mergeOf ufName ≠ none := by
    rw [hb.sig]; exact encodeSig_mergeOf_ufName hdom
  intro r hrm σ hσ e he
  rcases hb.rules r hrm with ⟨s, G, i, n, hmem, rfl⟩ | hmaint
  · refine execLocalActions_ufTermsDescend hb.inv (hb.wl' _ hrm) ?_
      (encodeRule_entrySafe hdom hmem G i n) (mem_terms_of_mem_matchQuery hσ) h he
    rw [encodeRule_actions]
    exact encodeActions_ufWriteSafe _ (s.substGlobals G).actions _
  · exact maintenance_ufTermsDescend (mem_maintenanceRules_of_mem_all hmaint) hb.inv hb.eqsRefl
      hmg (hb.wl' r hrm) hdes h hσ he

/-- One firing, unioned into the accumulator. -/
theorem fireInto_ufTermsDescend {d acc : FDatabase} {r : Rule} {σ : Env} (hr : r ∈ d.rules)
    (hσ : σ ∈ matchQuery d r.query) (hfire : d.FiringsUFTermsDescend)
    (ha : acc.UFTermsDescend) : (fireInto d r acc σ).UFTermsDescend := by
  rw [fireInto]
  cases hx : execLocalActions d r.actions σ with
  | none => exact ha
  | some e => exact ha.union (hfire r hr σ hσ e hx)

/-- Every match of one rule. -/
theorem foldl_fireInto_ufTermsDescend {d : FDatabase} {r : Rule} (hr : r ∈ d.rules)
    (hfire : d.FiringsUFTermsDescend) :
    ∀ (σs : List Env), (∀ σ ∈ σs, σ ∈ matchQuery d r.query) →
      ∀ {acc : FDatabase}, acc.UFTermsDescend → (σs.foldl (fireInto d r) acc).UFTermsDescend
  | [], _, _, ha => ha
  | σ :: σs, hsub, _, ha =>
      foldl_fireInto_ufTermsDescend hr hfire σs
        (fun τ hτ => hsub τ (List.mem_cons_of_mem _ hτ))
        (fireInto_ufTermsDescend hr (hsub σ List.mem_cons_self) hfire ha)

@[inherit_doc foldl_fireInto_ufTermsDescend]
theorem fireRule_ufTermsDescend {d acc : FDatabase} {r : Rule} (hr : r ∈ d.rules)
    (hfire : d.FiringsUFTermsDescend) (ha : acc.UFTermsDescend) :
    (fireRule d acc r).UFTermsDescend :=
  foldl_fireInto_ufTermsDescend hr hfire _ (fun _ h => h) ha

/-- The round's fold. -/
theorem foldl_fireRule_ufTermsDescend {d : FDatabase} (hfire : d.FiringsUFTermsDescend) :
    ∀ (rs : List Rule), (∀ r ∈ rs, r ∈ d.rules) →
      ∀ {acc : FDatabase}, acc.UFTermsDescend → (rs.foldl (fireRule d) acc).UFTermsDescend
  | [], _, _, ha => ha
  | r :: rs, hsub, _, ha =>
      foldl_fireRule_ufTermsDescend hfire rs
        (fun r' hr' => hsub r' (List.mem_cons_of_mem _ hr'))
        (fireRule_ufTermsDescend (hsub r List.mem_cons_self) hfire ha)

/-- **One round of rule firing descends over entry terms.** -/
theorem execRunRules_ufTermsDescend {R : RulesetName} {d : FDatabase}
    (hfire : d.FiringsUFTermsDescend) (h : d.UFTermsDescend) :
    (execRunRules R d).UFTermsDescend :=
  foldl_fireRule_ufTermsDescend hfire _ (fun _ hr => List.mem_of_mem_filter hr) h


/-- **One `addTerm`, checked at the recorded term's top.** `FDatabase.addRow` mints its entry
term this way, and so does the survivor of a merge firing. -/
theorem FDatabase.UFTermsDescend.addTerm_top {d : FDatabase} (h : d.UFTermsDescend) {t : Term}
    (hnew : ∀ a b pf, t = Term.app ufName [a, b, pf] → b = a ∨ Term.blt b a = true)
    (hsub : ∀ s ∈ t.subtermList, s ≠ t → s.EntryShaped → s ∈ d.terms) :
    (d.addTerm t).UFTermsDescend := by
  refine FDatabase.ufTermsDescend_iff.mpr fun a b pf hmem => ?_
  rcases FDatabase.mem_addTerm_terms.mp hmem with hm | hm
  · by_cases hq : Term.app ufName [a, b, pf] = t
    · exact hnew a b pf hq.symm
    · exact FDatabase.ufTermsDescend_iff.mp h a b pf (hsub _ hm hq (Or.inr ⟨a, b, pf, rfl⟩))
  · exact FDatabase.ufTermsDescend_iff.mp h a b pf hm

/-- The heads the proof node a merge body mints applies: `@Trans`, `@Sym` and the two
primitives its two selectors compile to. -/
theorem notEntryHead_mergePfE : ∀ g ∈ (transE (symE hiPfE) loPfE).fns, NotEntryHead g := by
  intro g hg
  have hg2 : g = transName ∨ g = symName ∨ g = "if" ∨ g = "ordering-gt" := by
    simpa [transE, symE, hiPfE, loPfE, ifE, gtE, Expr.fns, Expr.fnsList] using hg
  rcases hg2 with rfl | rfl | rfl | rfl
  exacts [notEntryHead_transName, notEntryHead_symName, notEntryHead_ifName, notEntryHead_gtName]

/-- **`mergeBody` is the `union` head's own shape**, so both syntactic conditions hold of it:
`Action.UFWriteSafe` because it writes `ordering-max ↦ ordering-min`, and `Action.EntrySafe`
because every head it applies is `if`, `ordering-gt`, `@Sym` or `@Trans`. -/
theorem mergeBody_ufWriteSafe : ∀ a ∈ mergeBody, a.UFWriteSafe := by
  intro a ha
  obtain rfl : a = Action.set ufName [maxE (.var "old0") (.var "new0")]
      [minE (.var "old0") (.var "new0"), transE (symE hiPfE) loPfE] := by
    simpa [mergeBody] using ha
  exact Or.inr ⟨_, _, _, rfl, rfl⟩

@[inherit_doc mergeBody_ufWriteSafe]
theorem mergeBody_entrySafe : ∀ a ∈ mergeBody, a.EntrySafe := by
  intro a ha
  obtain rfl : a = Action.set ufName [maxE (.var "old0") (.var "new0")]
      [minE (.var "old0") (.var "new0"), transE (symE hiPfE) loPfE] := by
    simpa [mergeBody] using ha
  exact entrySafe_unionHead notEntryHead_var notEntryHead_var notEntryHead_mergePfE

/-- **One merge firing descends over entry terms.** The body's own write is `mergeBody`, which
is `Action.UFWriteSafe` and `Action.EntrySafe`, so it goes through `execActions_ufTermsDescend`
unchanged; what is left is the survivor's entry term, whose e-class column is one of the two
colliding ones and so is below the key both of them were below. -/
theorem mergeOneOriented_ufTermsDescend {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hr : d.EqsRefl) (hinv : d.Inv) (hcl : ∀ p ∈ cl, p.1 = p.2) (hdes : d.UFRowsDescend)
    (h : d.UFTermsDescend) (hfire : d.mergeOneOriented cl r₁ r₂ = some e) : e.UFTermsDescend := by
  have hsc : d.SubtermClosed := FDatabase.SubtermClosed.of_wf hinv.wf
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨-, rfl, rfl, hout2, -, -⟩ := hshape r₁.fn dc hdc body res hmergedc
    split at hfire
    next hg =>
      obtain ⟨⟨⟨hfn, hargs'⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hargs'
      split at hfire
      next =>
        rw [Option.some.injEq] at hfire
        subst hfire
        exact h.of_terms_sub fun _ ht => ht
      next =>
        obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp hfire
        have hmg1 : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
        have hmg2 : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg1
        obtain ⟨-, hw1⟩ := hinv.index.width r₁ hmem₁ dc hdc hmg1
        obtain ⟨-, hw2⟩ := hinv.index.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg2
        rw [hout2] at hw1 hw2
        obtain ⟨n0, n1, hr1out⟩ := List.length_eq_two.mp hw1
        obtain ⟨o0, o1, hr2out⟩ := List.length_eq_two.mp hw2
        have hcol₁ : ∀ c ∈ r₁.args ++ r₁.out, c ∈ d.terms := fun c hc =>
          FDatabase.mem_terms_of_column hsc (mem_terms_of_indexOk hr hinv.index hmem₁ hmg1) hc
        have hcol₂ : ∀ c ∈ r₂.args ++ r₂.out, c ∈ d.terms := fun c hc =>
          FDatabase.mem_terms_of_column hsc (mem_terms_of_indexOk hr hinv.index hmem₂ hmg2) hc
        have hn0 : n0 ∈ d.terms := hcol₁ n0 (List.mem_append_right _ (by rw [hr1out]; simp))
        have hn1 : n1 ∈ d.terms := hcol₁ n1 (List.mem_append_right _ (by rw [hr1out]; simp))
        have ho0 : o0 ∈ d.terms := hcol₂ o0 (List.mem_append_right _ (by rw [hr2out]; simp))
        have ho1 : o1 ∈ d.terms := hcol₂ o1 (List.mem_append_right _ (by rw [hr2out]; simp))
        have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env
            = mergeEnv [o0, o1] [n0, n1] := by rw [hr1out, hr2out]
        have hinv' : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).Inv := by
          refine hinv.setEnv (fun b hb => ?_)
          rw [FDatabase.mem_toDatabase_terms]
          rw [hr2out, hr1out, mergeEnv_pair] at hb
          have hb2 : b = ("old0", o0) ∨ b = ("new0", n0) ∨ b = ("old1", o1) ∨
              b = ("new1", n1) := by simpa using hb
          rcases hb2 with rfl | rfl | rfl | rfl
          exacts [ho0, hn0, ho1, hn1]
        have hmdes : m.UFTermsDescend :=
          execActions_ufTermsDescend mergeBody mergeBody_ufWriteSafe mergeBody_entrySafe
            hinv' (hlegal r₁.fn dc mergeBody mergeResult hdc hmergedc).1
            (h.of_terms_sub fun _ ht => ht) hm
        obtain ⟨mx, mn, pa, pb, -, -, -, -, rfl⟩ := execActions_mergeBody_inv henv hm
        have hmono : ∀ t ∈ d.terms, t ∈ (FDatabase.addRow ufName [mx]
            [mn, Term.app transName [Term.app symName [pa], pb]]
            ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase)).terms :=
          fun t ht => FDatabase.mem_addRow_terms.mpr (Or.inr ht)
        rw [FDatabase.addRow_env, henv] at hvs
        obtain ⟨w, lo, hw0, hlo0, rfl⟩ := evalList_mergeResult_inv hvs
        subst he
        refine (FDatabase.UFTermsDescend.addTerm_top hmdes ?_ ?_).of_terms_sub fun _ ht => ht
        · intro a₀ b₀ pf₀ heq
          obtain ⟨hfeq, hcols⟩ := Term.app.inj heq
          obtain ⟨hka, hva⟩ := List.append_inj'
            (show r₂.args ++ [w, lo] = [a₀] ++ [b₀, pf₀] from hcols) rfl
          obtain rfl : w = b₀ := (List.cons.inj hva).1
          have hrow₂ : (⟨ufName, [a₀], [o0, o1]⟩ : Row) ∈ d.rows := by
            rw [show ufName = r₂.fn from hfeq.symm, show [a₀] = r₂.args from hka.symm, ← hr2out]
            exact hmem₂
          have hrow₁ : (⟨ufName, [a₀], [n0, n1]⟩ : Row) ∈ d.rows := by
            rw [show ufName = r₁.fn from (hfn.trans hfeq).symm,
              show [a₀] = r₁.args from (hargs.trans hka).symm, ← hr1out]
            exact hmem₁
          have ho : o0 = a₀ ∨ Term.blt o0 a₀ = true :=
            FDatabase.ufRowsDescend_iff.mp hdes a₀ o0 o1 hrow₂
          have hn : n0 = a₀ ∨ Term.blt n0 a₀ = true :=
            FDatabase.ufRowsDescend_iff.mp hdes a₀ n0 n1 hrow₁
          rcases hw0 with rfl | rfl
          exacts [ho, hn]
        · refine entryShaped_mem_of_columns (fun c hc => ?_)
          have hcm : c ∈ d.terms := by
            rcases List.mem_append.mp hc with hc' | hc'
            · exact hcol₂ c (List.mem_append_left _ hc')
            · have hc2 : c = w ∨ c = lo := by simpa using hc'
              rcases hc2 with rfl | rfl
              · rcases hw0 with rfl | rfl
                exacts [ho0, hn0]
              · rcases hlo0 with rfl | rfl
                exacts [ho1, hn1]
          exact fun s hs hsh => hmono _ (entryShaped_mem_of_held hsc hcm s hs hsh)
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

/-- **The same, at whichever orientation the pass chose.** -/
theorem mergeOneWith_ufTermsDescend {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hr : d.EqsRefl) (hinv : d.Inv) (hcl : ∀ p ∈ cl, p.1 = p.2) (hdes : d.UFRowsDescend)
    (h : d.UFTermsDescend) (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.UFTermsDescend := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_ufTermsDescend hshape hlegal hr hinv hcl hdes h (he ▸ hm)

/-- **A merge pass descends over entry terms.** The rebuild writes `rows` alone, so it costs
this nothing at all. -/
theorem mergeRound_ufTermsDescend {d : FDatabase} (hshape : Signature.MergeShape d.sig)
    (hlegal : Signature.MergesLegal d.sig) (hinv : d.Inv) (hn : d.NoUnions)
    (hdes : d.UFRowsDescend) (h : d.UFTermsDescend) : d.mergeRound.UFTermsDescend := by
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      d.mergeRound.UFRowsDescend ∧ d.mergeRound.UFTermsDescend := by
    refine FDatabase.mergeRound_induction
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ x.UFRowsDescend ∧ x.UFTermsDescend)
      ⟨hinv, rfl, hn, hdes, h⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        hdes.mono (fun r hr' => by
          rw [FDatabase.rebuild_diag hdiag, List.mem_dedup] at hr'; exact hr'),
        h.of_terms_sub fun _ ht => ht⟩ ?_
    intro x y r₁ r₂ hx hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy,
      mergeOneWith_ufRowsDescend (by rw [hx.2.1]; exact hshape) hx.1.index hdiag hx.2.2.2.1 hy,
      mergeOneWith_ufTermsDescend (by rw [hx.2.1]; exact hshape)
        (by rw [hx.2.1]; exact hlegal) hx.2.2.1.eqsRefl hx.1 hdiag hx.2.2.2.1 hx.2.2.2.2 hy⟩
  exact key.2.2.2.2

/-- **And the whole merge phase.** -/
theorem mergeSaturateF_ufTermsDescend : ∀ (n : Nat) {d e : FDatabase},
    Signature.MergeShape d.sig → Signature.MergesLegal d.sig → d.Inv → d.NoUnions →
    d.UFRowsDescend → d.UFTermsDescend → FDatabase.mergeSaturateF n d = some e →
      e.UFTermsDescend
  | 0, d, e, _, _, _, _, _, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · exact absurd hrun (by simp)
  | n + 1, d, e, hshape, hlegal, hinv, hn, hdes, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_ufTermsDescend n (by rw [hsig]; exact hshape)
          (by rw [hsig]; exact hlegal) (FDatabase.Inv.mergeRound_of_legalMerges hinv hlegal)
          (mergeRound_noUnions hn) (mergeRound_ufRowsDescend hshape hlegal hinv hn hdes)
          (mergeRound_ufTermsDescend hshape hlegal hinv hn hdes h) hrun

/-- **A whole round**: rule firing followed by the merge phase. -/
theorem runRoundM_ufTermsDescend {R : RulesetName} {d e : FDatabase}
    (hshape : Signature.MergeShape d.sig) (hlegal : Signature.MergesLegal d.sig)
    (hinv : d.Inv) (hn : d.NoUnions)
    (hwl : ∀ r ∈ d.rules, Actions.WriteLegal r.actions d.sig)
    (hfireR : d.FiringsUFDescend) (hfireT : d.FiringsUFTermsDescend)
    (hdes : d.UFRowsDescend) (h : d.UFTermsDescend)
    (hrun : d.runRoundM R = some e) : e.UFTermsDescend := by
  rw [FDatabase.runRoundM] at hrun
  refine mergeSaturateF_ufTermsDescend mergeFuel ?_ ?_ ?_ ?_
    (execRunRules_ufRowsDescend hfireR hdes) (execRunRules_ufTermsDescend hfireT h) hrun
  · rw [FDatabase.execRunRules_fields.1]; exact hshape
  · rw [FDatabase.execRunRules_fields.1]; exact hlegal
  · exact hinv.execRunRules hwl
  · exact execRunRules_noUnions hn


/-- **Rounds of one ruleset descend over entry terms**, given the bundle at each round's own
start. `FDatabase.UFRowsDescend` rides along because `pathCompressRule` reads rows. -/
theorem FDatabase.EncBase.runSaturateM_ufTermsDescend {P : Program} (hdom : P.EncodeDomain)
    {R : RulesetName} :
    ∀ (n : Nat) {d d' : FDatabase}, d.EncBase P (encodeSig P) → d.UFRowsDescend →
      d.UFTermsDescend → d.runSaturateM R n = some d' → d'.UFTermsDescend := by
  intro n d d' hb hdes h hrun
  refine (runSaturateM_closed (R := R)
    (Φ := fun x => x.EncBase P (encodeSig P) ∧ x.UFRowsDescend ∧ x.UFTermsDescend)
    ?_ n ⟨hb, hdes, h⟩ hrun).2.2
  intro x y hx hstep
  have hstep' : x.execCmdM (Cmd.run R) = some y := hstep
  have hmg : x.sig.mergeOf ufName ≠ none := by
    rw [hx.1.sig]; exact encodeSig_mergeOf_ufName hdom
  have hfireR : x.FiringsUFDescend :=
    firingsUFDescend_of_rulesEncoded hx.1.rules hx.1.eqsRefl hmg hx.2.1
  refine ⟨hx.1.execCmdM (c := Cmd.run R) trivial trivial trivial trivial trivial hstep',
    runRoundM_ufRowsDescend (by rw [hx.1.sig]; exact hx.1.shape)
      (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl' hfireR hx.2.1 hstep,
    ?_⟩
  exact runRoundM_ufTermsDescend (by rw [hx.1.sig]; exact hx.1.shape)
    (by rw [hx.1.sig]; exact hx.1.merges) hx.1.inv hx.1.nounions hx.1.wl' hfireR
    (hx.1.firingsUFTermsDescend hdom hx.2.1 hx.2.2) hx.2.1 hx.2.2 hstep

/-- **One command of the aligned run descends over entry terms.** The same conditions
`FDatabase.EncBase.execCmdM_ufRowsDescend` takes, plus the entry-write one the recorded
subterms cost. -/
theorem FDatabase.EncBase.execCmdM_ufTermsDescend {P : Program} (hdom : P.EncodeDomain)
    {d d' : FDatabase} {c : Cmd} (hb : d.EncBase P (encodeSig P))
    (huf : c.UnionFree) (hnd : c.NoDecl) (hwl : c.WriteLegal (encodeSig P))
    (hok : c.UFWriteOk) (hent : c.EntryWriteOk) (hdes : d.UFRowsDescend)
    (h : d.UFTermsDescend) (hs : d.execCmdM c = some d') : d'.UFTermsDescend := by
  have hmg : d.sig.mergeOf ufName ≠ none := by
    rw [hb.sig]; exact encodeSig_mergeOf_ufName hdom
  have hfireR : d.FiringsUFDescend :=
    firingsUFDescend_of_rulesEncoded hb.rules hb.eqsRefl hmg hdes
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine mergeSaturateF_ufTermsDescend mergeFuel ?_ ?_ ?_ ?_
      (execAction_ufRowsDescend hok hdes h₁)
      (execAction_ufTermsDescend hb.inv hok hent h h₁) h₂
    · rw [FDatabase.execAction_sig h₁, hb.sig]; exact hb.shape
    · rw [FDatabase.execAction_sig h₁, hb.sig]; exact hb.merges
    · exact hb.inv.execAction (by rw [hb.sig]; exact hwl) h₁
    · exact execAction_noUnions huf hb.nounions h₁
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.of_terms_sub fun _ ht => ht
  | run R =>
    rw [FDatabase.execCmdM] at hs
    exact runRoundM_ufTermsDescend (by rw [hb.sig]; exact hb.shape)
      (by rw [hb.sig]; exact hb.merges) hb.inv hb.nounions hb.wl' hfireR
      (hb.firingsUFTermsDescend hdom hdes h) hdes h hs
  | saturate R =>
    rw [FDatabase.execCmdM] at hs
    exact FDatabase.EncBase.runSaturateM_ufTermsDescend hdom runFuel hb hdes h hs
  | decl f dc => exact (hnd : False).elim

/-- **A block of them.** -/
theorem FDatabase.EncBase.execProgramM_ufTermsDescend {P : Program} (hdom : P.EncodeDomain)
    {p : Program} (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal (encodeSig P))
    (hok : ∀ c ∈ p, c.UFWriteOk) (hent : ∀ c ∈ p, c.EntryWriteOk)
    (hlet : ∀ c ∈ p, c.NoAtLet) :
    ∀ {d D : FDatabase}, d.EncBase P (encodeSig P) → d.UFRowsDescend → d.UFTermsDescend →
      d.execProgramM p = some D → D.UFTermsDescend := by
  induction p with
  | nil =>
    intro d D _ _ h hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro d D hb hdes h hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine ih (fun c' hc' => hro c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => huf c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hnd c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hwl c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hok c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hent c' (List.mem_cons_of_mem c hc'))
      (fun c' hc' => hlet c' (List.mem_cons_of_mem c hc'))
      (hb.execCmdM (hro c List.mem_cons_self) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hlet c List.mem_cons_self) h₁)
      (hb.execCmdM_ufRowsDescend (encodeSig_mergeOf_ufName hdom) (huf c List.mem_cons_self)
        (hnd c List.mem_cons_self) (hwl c List.mem_cons_self) (hok c List.mem_cons_self)
        hdes h₁)
      (hb.execCmdM_ufTermsDescend hdom (huf c List.mem_cons_self) (hnd c List.mem_cons_self)
        (hwl c List.mem_cons_self) (hok c List.mem_cons_self) (hent c List.mem_cons_self)
        hdes h h₁) h₂

/-- **`FDatabase.UFTermsDescend` at the state `execM` returned**: every `@UF` **entry term** an
encoded run's target holds runs `ordering-max ↦ ordering-min`, whether or not the row that
carried it survived.

This is the sole cost of `FDatabase.ufRowRoot_of_ufReach` — the identification of entry
reachability with row reachability that all three clauses of `Database.RebuildClosed` spend —
and it is now a theorem rather than a hypothesis. `execM_ufRowsDescend` is the same fact at the
rows; the two are one induction apart, and the extra obligation at each writer is
`Action.EntrySafe`, that no action records an entry-shaped term except the one its own `set`
writes a row for. -/
theorem execM_encode_ufTermsDescend {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.UFTermsDescend := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  have hdes₀ : d₀.UFRowsDescend := by
    refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
    rw [hdata.2.1, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
    exact absurd hmem (by simp)
  have h₀ : d₀.UFTermsDescend := by
    refine FDatabase.ufTermsDescend_iff.mpr fun a b pf hmem => ?_
    rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at hmem
    exact absurd hmem (by simp)
  refine FDatabase.EncBase.execProgramM_ufTermsDescend hdom
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) [] 0 0) (encodeCmds_unionFree P [] P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_)
    hb₀ hdes₀ h₀ hcmds
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noDecl_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ H m j c hmem
  · obtain ⟨c₀, -, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact ufWriteOk_encodeCmd H c₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact entryWriteOk_encodeCmd hdom H c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, H, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) [] 0 0 c hc
    exact noAtLet_encodeCmd hdom H c₀ hc₀ m j c hmem

/-- **Entry-term descent, with the arity clause read off the domain.** -/
theorem execM_ufTermsDescend {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.UFTermsDescend :=
  execM_encode_ufTermsDescend hdom hdom.aritiesAgree' htgt

/-- **The identification, at the state `execM` returned**: entry reachability and row
reachability land on the *same* `@UF` row root, so the row a reader of an id is answered with
by the bridge is the one every other reader of that id is answered with too.

`FDatabase.ufRowRoot_of_ufReach` with all four of its hypotheses discharged —
`execM_encode_eqsRefl`, `execM_entryRowsUF`, `execM_ufRowsDescend`,
`execM_encode_ufRowsForest` and `execM_ufTermsDescend`. -/
theorem execM_ufRowRoot_of_ufReach {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) {a b : Term}
    (hreach : tgt.toDatabase.UFReach a b) :
    ∀ r s, tgt.UFRowReach a r → tgt.UFRowRoot r → tgt.UFRowReach b s → tgt.UFRowRoot s →
      r = s :=
  FDatabase.ufRowRoot_of_ufReach (execM_encode_eqsRefl htgt) (execM_entryRowsUF hdom htgt)
    (by rw [(execM_encode_encBase hdom hdom.aritiesAgree' htgt).sig]; exact encodeSig_ufName hdom)
    (execM_ufRowsDescend hdom htgt)
    (execM_encode_ufRowsForest hdom hdom.aritiesAgree' hsy htr htgt)
    (execM_ufTermsDescend hdom htgt) hreach

/-! ## The fixpoint's roots, run-wide

`no_ufRowEdge_of_rowsClosed` reads a rebuild **fixpoint**, and `encodeCmd` emits
`Cmd.saturate rebuildRuleset` after an action, a run and a saturate but after neither a
`Cmd.rule` nor a `Cmd.decl`. So `FDatabase.ViewRowsRooted` is *established* at the end of the
first three blocks and *carried* across the other two, which change no row at all — and the
carry is one rewrite, since the property reads `rows` and nothing else.

**`FDatabase.settled` costs the carry nothing.** `FDatabase.runSaturateM_settled'` reads the
merge fixpoint off the branch the saturating run returned from, with no hypothesis about the
state that run started at — which is what keeps `settled` off the block induction, where a
`Cmd.rule` would have had to be shown to preserve it through `FDatabase.mergeRound`. -/

/-- **A saturating run returns a merge-settled state.** The branch `FDatabase.runSaturateM`
returns from tests the state it returns against a round's output on the three fields a round
can change (`FDatabase.sameData`) and `FDatabase.runRoundM_fields` gives the other three, so
the state returned **is** that output — and a round ends in `FDatabase.mergeSaturateF`. -/
theorem FDatabase.runSaturateM_settled' {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → e.settled = true := by
  intro n d e hs
  obtain ⟨e', hround, hsame⟩ := FDatabase.runSaturateM_settled n hs
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hround
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hsame
  obtain ⟨⟨hterms, hrows⟩, heqs⟩ := hsame
  obtain rfl : e' = e := by cases e'; cases e; simp_all
  rw [FDatabase.runRoundM] at hround
  exact FDatabase.mergeSaturateF_settled mergeFuel hround

/-! ### What a merge phase leaves at a key, at the union-find

`mergeSaturateF_rowsDescendCarry` is one reading of `mergeOneOriented_survivorUF` — the survivor's
e-class column is `Term.blt`-at or below the one the key carried — and it is what
`no_ufRowEdge_of_rowsClosed` spends. The **other** reading is the union-find one, and it is what
the column rules' closure spends instead: a `Term.blt` bound cannot say that a firing's e-class
column and the survivor's are the same point, and `Database.UFReach` between two `@UF` row roots
can. `FDatabase.RowsCarryUF` is that reading and `mergeOneOriented_rowsCarryUF` is it at one
firing; what is added here is the pass, the phase, and the round-level fixpoint a firing has to
be pushed through to come back at the state it started from. -/

/-- **Rows carry across one merge firing, at whichever orientation the pass chose.** -/
theorem mergeOneWith_rowsCarryUF {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : Signature.MergeShape d.sig) (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2)
    (hne : r₁ ≠ r₂) (hm : d.mergeOneWith cl r₁ r₂ = some e) : d.RowsCarryUF e := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · exact mergeOneOriented_rowsCarryUF hshape hidx hcl (Ne.symm hne) (he ▸ hm)
  · exact mergeOneOriented_rowsCarryUF hshape hidx hcl hne (he ▸ hm)

/-- **A merge pass carries them.** -/
theorem mergeRound_rowsCarryUF {d : FDatabase} (hshape : Signature.MergeShape d.sig)
    (hlegal : Signature.MergesLegal d.sig) (hinv : d.Inv) (hn : d.NoUnions) :
    d.RowsCarryUF d.mergeRound := by
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      d.RowsCarryUF d.mergeRound := by
    refine FDatabase.mergeRound_induction_ne
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ d.RowsCarryUF x)
      ⟨hinv, rfl, hn, FDatabase.RowsCarryUF.refl d⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        FDatabase.RowsCarryUF.of_subset fun r hr => by
          rw [FDatabase.rebuild_diag hdiag, List.mem_dedup]; exact hr⟩ ?_
    intro x y r₁ r₂ hne hx hy
    obtain ⟨htm, heq, hsg, -⟩ := FDatabase.mergeOneWith_confined hy
    exact ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      hsg.trans hx.2.1, mergeOneWith_noUnions hx.2.2.1 hy,
      hx.2.2.2.trans
        (mergeOneWith_rowsCarryUF (by rw [hx.2.1]; exact hshape) hx.1.index hdiag hne hy)
        htm heq⟩
  exact key.2.2.2

/-- **And a whole merge phase.** This is `mergeSaturateF_rowsDescendCarry`'s other reading:
the row the phase leaves at a key carries an e-class column the union-find reaches from the one
the key started with. -/
theorem mergeSaturateF_rowsCarryUF : ∀ (n : Nat) {d e : FDatabase},
    Signature.MergeShape d.sig → Signature.MergesLegal d.sig → d.Inv → d.NoUnions →
    FDatabase.mergeSaturateF n d = some e → d.RowsCarryUF e
  | 0, d, e, _, _, _, _, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun
        exact hrun ▸ FDatabase.RowsCarryUF.refl d
      · exact absurd hrun (by simp)
  | n + 1, d, e, hshape, hlegal, hinv, hn, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun
        exact hrun ▸ FDatabase.RowsCarryUF.refl d
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact (mergeRound_rowsCarryUF hshape hlegal hinv hn).trans
          (mergeSaturateF_rowsCarryUF n (by rw [hsig]; exact hshape)
            (by rw [hsig]; exact hlegal) (FDatabase.Inv.mergeRound_of_legalMerges hinv hlegal)
            (mergeRound_noUnions hn) hrun)
          (FDatabase.mergeSaturateF_terms hrun) (FDatabase.mergeSaturateF_eqs hrun)

/-- **A saturating run's state is a round's own fixpoint.** `FDatabase.runSaturateM_settled'`
reads the same branch for `FDatabase.settled`; this reads it for the round itself, which is
what a firing has to be pushed through to come back at the state it started from. -/
theorem FDatabase.runSaturateM_roundFixed {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → e.runRoundM R = some e := by
  intro n d e hs
  obtain ⟨e', hround, hsame⟩ := FDatabase.runSaturateM_settled n hs
  obtain ⟨hsig, henv, hrules⟩ := FDatabase.runRoundM_fields hround
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hsame
  obtain ⟨⟨hterms, hrows⟩, heqs⟩ := hsame
  obtain rfl : e' = e := by cases e'; cases e; simp_all
  exact hround

/-- **The fixpoint's roots as a property of a state**: no e-class column a live view row
records has an outgoing `@UF` row. `no_ufRowEdge_of_rowsClosed` is this at one rebuild
fixpoint; `execM_viewRowsRooted` is it at the state `execM` returned. -/
def FDatabase.ViewRowsRooted (d : FDatabase) (P : Program) : Prop :=
  ∀ (f : FnName) (k : Nat), (f, k) ∈ P.ctors → ∀ (as : List Term) (e pf : Term),
    (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows → d.UFRowRoot e

/-- **A writer that changes no row carries it**, hypothesis and conclusion alike: both read
`rows`. This is the whole of the `Cmd.rule` and `Cmd.decl` cases. -/
theorem FDatabase.ViewRowsRooted.of_rows_eq {d D : FDatabase} {P : Program}
    (h : d.ViewRowsRooted P) (hrows : D.rows = d.rows) : D.ViewRowsRooted P := by
  intro f k hfk as e pf hrow y hedge
  obtain ⟨⟨q, hq⟩, hne⟩ := hedge
  exact h f k hfk as e pf (hrows ▸ hrow) y ⟨⟨q, hrows ▸ hq⟩, hne⟩

/-- **What the fixpoint's roots argument asks of the state a block starts at**, bundled so
that the block induction carries one thing. Each field is already run-wide on its own
(`execM_encode_encBase`, `execM_encode_valued`, `execM_ufRowsDescend`); what the bundle buys
is that the induction below does not have to re-derive them at every intermediate state. -/
structure FDatabase.RebuildBase (d : FDatabase) (P : Program) : Prop where
  /-- The structural half of an aligned run. -/
  base : d.EncBase P (encodeSig P)
  /-- Every term the state holds is one a rule variable may be bound to. -/
  valued : d.Valued
  /-- Every live `@UF` row runs `ordering-max ↦ ordering-min`. -/
  descend : d.UFRowsDescend

/-- The fourth cost of the e-class rule's firing, out of the bundle. -/
theorem FDatabase.RebuildBase.rowColumnsValued {d : FDatabase} {P : Program}
    (h : d.RebuildBase P) : d.RowColumnsValued :=
  h.valued.rowColumnsValued h.base.eqsRefl h.base.subtermClosed h.base.inv.index

/-- **A block of encoded commands keeps the bundle**, one `execProgramM` lemma per field. -/
theorem FDatabase.RebuildBase.execProgramM {P : Program} (hdom : P.EncodeDomain) {p : Program}
    (hro : ∀ c ∈ p, Cmd.RulesEncodedOk P c) (huf : ∀ c ∈ p, c.UnionFree)
    (hnd : ∀ c ∈ p, c.NoDecl) (hwl : ∀ c ∈ p, c.WriteLegal (encodeSig P))
    (hok : ∀ c ∈ p, c.UFWriteOk) (hlet : ∀ c ∈ p, c.NoAtLet)
    {d D : FDatabase} (h : d.RebuildBase P) (hs : d.execProgramM p = some D) :
    D.RebuildBase P where
  base := FDatabase.EncBase.execProgramM hro huf hnd hwl hlet h.base hs
  valued := FDatabase.EncBase.execProgramM_valued hro huf hnd hwl hlet h.base h.valued hs
  descend := FDatabase.EncBase.execProgramM_ufRowsDescend (encodeSig_mergeOf_ufName hdom)
    hro huf hnd hwl hok hlet h.base h.descend hs

/-- **The bundle across any part of one source command's block.** Stated over a sublist so
that the action case, whose block is a run of `Cmd.action`s followed by the rebuild, can use
it at the prefix as well as at the whole. -/
theorem rebuildBase_encodeCmd {P : Program} (hdom : P.EncodeDomain) {c : Cmd} (hc : c ∈ P)
    {G : List (Var × Expr)} {n i : Nat} {q : Program} (hq : ∀ c' ∈ q, c' ∈ (encodeCmd G c n i).1)
    {d D : FDatabase} (h : d.RebuildBase P) (hs : d.execProgramM q = some D) :
    D.RebuildBase P :=
  FDatabase.RebuildBase.execProgramM hdom
    (fun c' hc' => rulesEncodedOk_encodeCmd hc G n i c' (hq c' hc'))
    (fun c' hc' => encodeCmd_unionFree G c n i c' (hq c' hc'))
    (fun c' hc' => noDecl_encodeCmd G c n i c' (hq c' hc'))
    (fun c' hc' => encodedWriteLegal hdom hdom.aritiesAgree' c hc G n i c' (hq c' hc'))
    (fun c' hc' => ufWriteOk_encodeCmd G c n i c' (hq c' hc'))
    (fun c' hc' => noAtLet_encodeCmd hdom G c hc n i c' (hq c' hc')) h hs

/-- **One rebuild fixpoint delivers the roots.** `no_ufRowEdge_of_rowsClosed` at the state
`Cmd.saturate rebuildRuleset` returned: `FDatabase.runSaturateM_rowsClosed` is the fixpoint on
`rows`, `FDatabase.runSaturateM_settled` the round it still has to run, and
`FDatabase.runSaturateM_settled'` the merge fixpoint the row-uniqueness half wants. -/
theorem viewRowsRooted_of_runSaturateM {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d e : FDatabase} (h : d.RebuildBase P)
    (hs : d.execCmdM (Cmd.saturate rebuildRuleset) = some e) : e.ViewRowsRooted P := by
  have hs' : d.runSaturateM rebuildRuleset runFuel = some e := hs
  have hbe : e.EncBase P (encodeSig P) :=
    h.base.execCmdM (c := Cmd.saturate rebuildRuleset) trivial trivial trivial trivial trivial hs
  have hve : e.Valued := FDatabase.EncBase.runSaturateM_valued runFuel h.base h.valued hs'
  have hdese : e.UFRowsDescend :=
    h.base.execCmdM_ufRowsDescend (encodeSig_mergeOf_ufName hdom)
      (c := Cmd.saturate rebuildRuleset) trivial trivial trivial trivial h.descend hs
  obtain ⟨e', hround, -⟩ := FDatabase.runSaturateM_settled runFuel hs'
  intro f k hfk as x pf hrow y hedge
  exact no_ufRowEdge_of_rowsClosed hdom hbe hsy htr
    (hve.rowColumnsValued hbe.eqsRefl hbe.subtermClosed hbe.inv.index)
    (FDatabase.runSaturateM_settled' runFuel hs') hdese
    (FDatabase.runSaturateM_rowsClosed hs') hround hfk hrow hedge

/-- **The two shapes a source command's block has.** Three of the five end with
`Cmd.saturate rebuildRuleset`; the other two change no row — a `Cmd.rule` only registers
itself and a `Cmd.decl` emits nothing at all. -/
theorem encodeCmd_rebuilds_or_rowsFixed (G : List (Var × Expr)) (c : Cmd) (n i : Nat) :
    (∃ q, (encodeCmd G c n i).1 = q ++ [Cmd.saturate rebuildRuleset]) ∨
      ∀ {d D : FDatabase}, d.execProgramM (encodeCmd G c n i).1 = some D → D.rows = d.rows := by
  cases c with
  | action a => exact Or.inl ⟨_, encodeCmd_action_fst G a n i⟩
  | run R => exact Or.inl ⟨[Cmd.run R], rfl⟩
  | saturate R => exact Or.inl ⟨[Cmd.saturate R], rfl⟩
  | rule r =>
      refine Or.inr fun {d D} hs => ?_
      rw [encodeCmd_rule_fst, FDatabase.execProgramM, FDatabase.execCmdM, Option.bind_some,
        FDatabase.execProgramM, Option.some.injEq] at hs
      exact hs ▸ rfl
  | decl f dc =>
      refine Or.inr fun {d D} hs => ?_
      rw [show (encodeCmd G (Cmd.decl f dc) n i).1 = ([] : Program) from rfl,
        FDatabase.execProgramM, Option.some.injEq] at hs
      exact hs ▸ rfl

/-- **One source command's block keeps the roots.** -/
theorem viewRowsRooted_encodeCmd {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {c : Cmd} (hc : c ∈ P) (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase}
    (h : d.RebuildBase P)
    (hr : d.ViewRowsRooted P) (hs : d.execProgramM (encodeCmd G c n i).1 = some D) :
    D.ViewRowsRooted P := by
  rcases encodeCmd_rebuilds_or_rowsFixed G c n i with ⟨q, hq⟩ | hfix
  · rw [hq] at hs
    obtain ⟨d₂, h₂, h₃⟩ := FDatabase.execProgramM_append hs
    have hbase₂ : d₂.RebuildBase P :=
      rebuildBase_encodeCmd hdom hc
        (fun c' hc' => by rw [hq]; exact List.mem_append_left _ hc') h h₂
    have hsat : d₂.execCmdM (Cmd.saturate rebuildRuleset) = some D := by
      rw [FDatabase.execProgramM] at h₃
      obtain ⟨x, hx, hx'⟩ := Option.bind_eq_some_iff.mp h₃
      rw [FDatabase.execProgramM, Option.some.injEq] at hx'
      exact hx' ▸ hx
    exact viewRowsRooted_of_runSaturateM hdom hsy htr hbase₂ hsat
  · exact hr.of_rows_eq (hfix hs)

/-- **And the whole aligned run.** -/
theorem viewRowsRooted_encodeCmds {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName) :
    ∀ (p : Program) {R : Program}, (∀ c ∈ p, c ∈ P) →
      ∀ (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase},
      d.RebuildBase P → d.ViewRowsRooted P →
      d.execProgramM (encodeCmds R G p n i).1 = some D → D.ViewRowsRooted P := by
  intro p
  induction p with
  | nil =>
    intro R _ G n i d D _ hr hs
    rw [show (encodeCmds R G ([] : Program) n i).1 = ([] : Program) from rfl,
      FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hr
  | cons c cs ih =>
    intro R hp G n i d D h hr hs
    rw [encodeCmds_cons_fst] at hs
    obtain ⟨d₁, h₁, h₂⟩ := FDatabase.execProgramM_append hs
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) _ _ _
      (rebuildBase_encodeCmd hdom (hp c List.mem_cons_self) (fun _ hc' => hc') h h₁)
      (viewRowsRooted_encodeCmd hdom hsy htr (hp c List.mem_cons_self) G n i h hr h₁) h₂

/-- **The fixpoint's roots at the state `execM` returned**: no e-class column a view row of an
encoded run's target records has an outgoing `@UF` row.

This is `no_ufRowEdge_of_rowsClosed` with its three fixpoint hypotheses discharged, and it is
the condition the residue's second obligation was left carrying: the encoding emits a rebuild
after an action, a run and a saturate and after neither a `Cmd.rule` nor a `Cmd.decl`, so a
program ending in one of those two leaves a target no fixpoint lemma reaches directly.
Neither writer changes a row, and `Program.EncodeDomain.noAt` keeps a source rule out of
`@rebuild`, so the property is carried across them rather than re-established. -/
theorem execM_viewRowsRooted {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.ViewRowsRooted P := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) :=
    (encOk_preludeState hdom hdom.aritiesAgree' hprel).base
  have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  have hrows₀ : d₀.rows = [] := by
    rw [hdata.2.1]; rfl
  have h₀ : d₀.RebuildBase P := by
    refine ⟨hb₀, ⟨fun t ht => ?_, fun b hb => ?_⟩, ?_⟩
    · rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at ht
      exact absurd ht (by simp)
    · rw [hdata.2.2.2, show FDatabase.empty.env = ([] : Env) from rfl] at hb
      exact absurd hb (by simp)
    · refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
      rw [hrows₀] at hmem
      exact absurd hmem (by simp)
  have hr₀ : d₀.ViewRowsRooted P := by
    intro f k _ as e pf hrow
    rw [hrows₀] at hrow
    exact absurd hrow (by simp)
  exact viewRowsRooted_encodeCmds hdom hsy htr P (fun _ hc => hc) [] 0 0 h₀ hr₀ hcmds



/-! ## The merge fixpoint at a view key, run-wide

`FDatabase.row_unique_of_settled` is what identifies two rows one view key carries, and it reads
`FDatabase.settled` — the merge fixpoint. `encode` emits `Cmd.saturate rebuildRuleset` after an
action, a run and a saturate and after neither a `Cmd.rule` nor a `Cmd.decl`, so the property is
*established* at the end of the first three blocks and *carried* across the other two, which
change no row at all. This is `viewRowsRooted_encodeCmd`'s carry read at the other fixpoint
fact, and `FDatabase.runSaturateM_settled'` again costs it nothing.

**The carry is of what `FDatabase.settled` delivers and not of `FDatabase.settled` itself.**
`settled` compares the state against `FDatabase.mergeRound`, which is a function of the *whole*
state, so a `Cmd.rule` — which changes `rules` and nothing else — would have to be shown not to
move a fold over `FDatabase.mergeOneWith`. What the clauses spend is the reading over `rows`,
and there the carry is a rewrite. -/

/-- **What the merge fixpoint leaves at a view key, as a property of a state**: a view key
carries at most one row. -/
def FDatabase.ViewRowUnique (d : FDatabase) (P : Program) : Prop :=
  ∀ (f : FnName) (k : Nat), (f, k) ∈ P.ctors → ∀ (as vs ws : List Term),
    (⟨viewName f, as, vs⟩ : Row) ∈ d.rows → (⟨viewName f, as, ws⟩ : Row) ∈ d.rows → vs = ws

/-- **A writer that changes no row carries it**, hypothesis and conclusion alike: both read
`rows`. This is the whole of the `Cmd.rule` and `Cmd.decl` cases. -/
theorem FDatabase.ViewRowUnique.of_rows_eq {d D : FDatabase} {P : Program}
    (h : d.ViewRowUnique P) (hrows : D.rows = d.rows) : D.ViewRowUnique P :=
  fun f k hfk as vs ws h₁ h₂ => h f k hfk as vs ws (hrows ▸ h₁) (hrows ▸ h₂)

/-- **One `Cmd.saturate rebuildRuleset` delivers it.** `FDatabase.runSaturateM_settled'` reads
the merge fixpoint off the branch the saturating run returned from, and
`FDatabase.row_unique_of_settled` is that fixpoint at a view table. -/
theorem viewRowUnique_of_runSaturateM {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d e : FDatabase} (h : d.RebuildBase P)
    (hs : d.execCmdM (Cmd.saturate rebuildRuleset) = some e) : e.ViewRowUnique P := by
  have hs' : d.runSaturateM rebuildRuleset runFuel = some e := hs
  have hb : e.EncBase P (encodeSig P) :=
    h.base.execCmdM (c := Cmd.saturate rebuildRuleset) trivial trivial trivial trivial trivial hs
  intro f k hfk as vs ws h₁ h₂
  have hsigd : e.sig = encodeSig P := hb.sig
  have hdecl : (encodeSig P) (viewName f) = some (viewDecl k) :=
    (encodeSig_tables hdom hdom.aritiesAgree' hfk).1
  have hdcm : (viewDecl k).merge = some (MergeSpec.merge mergeBody mergeResult) := rfl
  have hmgne : e.sig.mergeOf (viewName f) ≠ none := by
    rw [Signature.mergeOf, hsigd, hdecl, Option.bind_some, hdcm]; simp
  exact FDatabase.row_unique_of_settled (FDatabase.runSaturateM_settled' runFuel hs')
    (by rw [hsigd]; exact hb.shape) (by rw [hsigd]; exact hb.merges) hb.inv
    (fun p hp => diag_closureF hb.eqsRefl hp) (by rw [hsigd]; exact hsy)
    (by rw [hsigd]; exact htr) (by rw [hsigd]; exact hdecl) hdcm
    (fun hc => viewName_ne_ufName hc)
    (rowArgs_mem_closureF hb.eqsRefl hb.inv.index hb.subtermClosed
      ⟨viewName f, as, vs⟩ h₁ hmgne)
    h₁ h₂

/-- **One source command's block keeps it.** -/
theorem viewRowUnique_encodeCmd {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {c : Cmd} (hc : c ∈ P) (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase}
    (h : d.RebuildBase P)
    (hr : d.ViewRowUnique P) (hs : d.execProgramM (encodeCmd G c n i).1 = some D) :
    D.ViewRowUnique P := by
  rcases encodeCmd_rebuilds_or_rowsFixed G c n i with ⟨q, hq⟩ | hfix
  · rw [hq] at hs
    obtain ⟨d₂, h₂, h₃⟩ := FDatabase.execProgramM_append hs
    have hbase₂ : d₂.RebuildBase P :=
      rebuildBase_encodeCmd hdom hc
        (fun c' hc' => by rw [hq]; exact List.mem_append_left _ hc') h h₂
    have hsat : d₂.execCmdM (Cmd.saturate rebuildRuleset) = some D := by
      rw [FDatabase.execProgramM] at h₃
      obtain ⟨x, hx, hx'⟩ := Option.bind_eq_some_iff.mp h₃
      rw [FDatabase.execProgramM, Option.some.injEq] at hx'
      exact hx' ▸ hx
    exact viewRowUnique_of_runSaturateM hdom hsy htr hbase₂ hsat
  · exact hr.of_rows_eq (hfix hs)

/-- **And the whole aligned run.** -/
theorem viewRowUnique_encodeCmds {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName) :
    ∀ (p : Program) {R : Program}, (∀ c ∈ p, c ∈ P) →
      ∀ (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase},
      d.RebuildBase P → d.ViewRowUnique P →
      d.execProgramM (encodeCmds R G p n i).1 = some D → D.ViewRowUnique P := by
  intro p
  induction p with
  | nil =>
    intro R _ G n i d D _ hr hs
    rw [show (encodeCmds R G ([] : Program) n i).1 = ([] : Program) from rfl,
      FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hr
  | cons c cs ih =>
    intro R hp G n i d D h hr hs
    rw [encodeCmds_cons_fst] at hs
    obtain ⟨d₁, h₁, h₂⟩ := FDatabase.execProgramM_append hs
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) _ _ _
      (rebuildBase_encodeCmd hdom (hp c List.mem_cons_self) (fun _ hc' => hc') h h₁)
      (viewRowUnique_encodeCmd hdom hsy htr (hp c List.mem_cons_self) G n i h hr h₁) h₂

/-- **The merge fixpoint at a view key, at the state `execM` returned**: one view key of an
encoded run's target carries at most one row. This is the run-wide `FDatabase.settled` carry
that `Database.RebuildClosed`'s `edged` clause was left waiting on — it is what identifies the
two rows the bridge produces for two readings of one source term once the column rules have
moved both keys onto the common root tuple. -/
theorem execM_viewRowUnique {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.ViewRowUnique P := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) :=
    (encOk_preludeState hdom hdom.aritiesAgree' hprel).base
  have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  have hrows₀ : d₀.rows = [] := by
    rw [hdata.2.1]; rfl
  have h₀ : d₀.RebuildBase P := by
    refine ⟨hb₀, ⟨fun t ht => ?_, fun b hb => ?_⟩, ?_⟩
    · rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at ht
      exact absurd ht (by simp)
    · rw [hdata.2.2.2, show FDatabase.empty.env = ([] : Env) from rfl] at hb
      exact absurd hb (by simp)
    · refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
      rw [hrows₀] at hmem
      exact absurd hmem (by simp)
  have hr₀ : d₀.ViewRowUnique P := by
    intro f k _ as vs ws hrow
    rw [hrows₀] at hrow
    exact absurd hrow (by simp)
  exact viewRowUnique_encodeCmds hdom hsy htr P (fun _ hc => hc) [] 0 0 h₀ hr₀ hcmds

/-- **Non-vacuous at the run**, at the program whose rebuild really re-keys a row. -/
theorem execM_viewRowUnique_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) : tgt.ViewRowUnique ncProgram :=
  execM_viewRowUnique ncProgram_encodeDomain ncProgram_isCtor_symName
    ncProgram_isCtor_transName htgt

/-! ## The column rules at their fixpoint, run-wide

`execM_viewRowsRooted` is the e-class rule's fixpoint fact: a live view row's e-class column is a
root. The column rules' fixpoint fact is **not** its analogue at the key — a superseded key is
never vacated, since only a collision at *one* key removes a row, so a live view row's key column
need not be a root and the column rule's conclusion sits at a different key from its premise.
What the fixpoint delivers instead is a **closure**: the row at the moved key is one the state
already holds.

The establishment is `columnRule_fires` pushed through the merge phase by
`mergeSaturateF_rowsCarryUF` and back to the state it started at by
`FDatabase.runSaturateM_roundFixed` — which is `FDatabase.runSaturateM_settled'`'s branch read
for the round rather than for `FDatabase.settled`, and is what replaces `FDatabase.RowsClosed`
here: a firing's row has to come back at the **same** state for the closure to be about that
state's rows. The carry across the two block shapes that run no rebuild is
`encodeCmd_rebuilds_or_dataFixed`, at the three fields `Database.UFReach` reads and not at `rows`
alone.

The walk is then the closure iterated: `execM_columnRow_step` makes the e-class column *exact*
rather than merely reachable — both ends are e-class columns of live view rows, so
`execM_viewRowsRooted` makes both `@UF` row roots and `execM_ufRowRoot_of_ufReach` identifies
them — `execM_columnRow_walk` follows one column's chain, and
`execM_viewRow_of_rowReachList` moves every column at once.

**What this settles of `Database.RebuildClosed`.** It is stated over `FDatabase.UFRowReach`,
over live `@UF` **rows**, because that is what a firing can read; both clauses are stated over
`Database.Lands`, whose reachability half is `Database.UFReach`, over `@UF` **entries**. So what
the walk delivers for a tuple `es` is the row at the pointwise-**root** tuple and not the row at
an arbitrary landing site, and `Database.LandsRoot` is that restriction written into the
clauses: `execM_rebuildColumn` is `column` at a rooted tuple and `execM_rootAgree` is `edged`'s
root agreement, both out of this walk. Rooting `column` is what makes "a landing site of a live
key column is itself an `@UF` row root" — which `Database.Absorbs` cannot supply, being an
entry-level property over terms no writer removes — an assumption rather than an obligation. -/

/-- **The column rules' closure as a property of a state**: a live view row's key column may be
moved along a live `@UF` row, and the row at the moved key is one the state already holds, at an
e-class column the union-find reaches from the one the row started with. -/
def FDatabase.ViewRowsColumnClosed (d : FDatabase) (P : Program) : Prop :=
  ∀ (f : FnName) (k : Nat), (f, k) ∈ P.ctors → ∀ (as : List Term) (e pf : Term),
    (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows → ∀ (i : Nat) (ci x : Term),
      as[i]? = some ci → d.UFRowEdge ci x →
      ∃ e' pf', (⟨viewName f, as.set i x, [e', pf']⟩ : Row) ∈ d.rows ∧
        d.toDatabase.UFReach e e'

/-- **A writer that changes no row, term or equation carries it.** -/
theorem FDatabase.ViewRowsColumnClosed.of_data_eq {d D : FDatabase} {P : Program}
    (h : d.ViewRowsColumnClosed P) (hrows : D.rows = d.rows) (hterms : D.terms = d.terms)
    (heqs : D.eqs = d.eqs) : D.ViewRowsColumnClosed P := by
  intro f k hfk as e pf hrow i ci x hci hedge
  obtain ⟨⟨q, hq⟩, hne⟩ := hedge
  obtain ⟨e', pf', hrow', hreach⟩ :=
    h f k hfk as e pf (hrows ▸ hrow) i ci x hci ⟨⟨q, hrows ▸ hq⟩, hne⟩
  refine ⟨e', pf', hrows ▸ hrow', Database.UFReach.mono (fun t ht => ?_) (fun p hp => ?_) hreach⟩
  · rw [hterms]; exact ht
  · rw [heqs]; exact hp

/-- **One rebuild fixpoint delivers the column closure.** `columnRule_fires` at the state
`Cmd.saturate rebuildRuleset` returned, pushed through the merge phase by
`mergeSaturateF_rowsCarryUF` and back to the state it started at by
`FDatabase.runSaturateM_roundFixed`. -/
theorem viewRowsColumnClosed_of_roundFixed {P : Program} {d : FDatabase} (hdom : P.EncodeDomain)
    (hb : d.EncBase P (encodeSig P))
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    (hcv : d.RowColumnsValued) (hround : d.runRoundM rebuildRuleset = some d) :
    d.ViewRowsColumnClosed P := by
  intro f k hfk as e pf hrow i ci x hci hedge
  have hsigd : d.sig = encodeSig P := hb.sig
  have hdecl : (encodeSig P) (viewName f) = some (viewDecl k) :=
    (encodeSig_tables hdom hdom.aritiesAgree' hfk).1
  have hmgne : d.sig.mergeOf (viewName f) ≠ none := by
    rw [Signature.mergeOf, hsigd, hdecl, Option.bind_some,
      show (viewDecl k).merge = some (MergeSpec.merge mergeBody mergeResult) from rfl]
    simp
  have hlen : as.length = k :=
    (hb.inv.index.width ⟨viewName f, as, [e, pf]⟩ hrow (viewDecl k)
      (by rw [hsigd]; exact hdecl) hmgne).1
  have hi : i < k := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hci).1
  obtain ⟨q, hufrow⟩ := hedge.1
  have hfired : (⟨viewName f, as.set i x, [e, columnProof k i pf q]⟩ : Row) ∈
      (execRunRules rebuildRuleset d).rows :=
    columnRule_fires hb hcv htr hsy hfi (hcg f k hfk (by omega)) hfk
      (by rw [Option.isSome_iff_ne_none]; exact hmgne)
      (by
        rw [Option.isSome_iff_ne_none, Signature.mergeOf, hsigd, encodeSig_ufName hdom,
          Option.bind_some]
        simp [ufDecl])
      hlen hi hci hrow hufrow
  have hsigR : (execRunRules rebuildRuleset d).sig = d.sig := FDatabase.execRunRules_fields.1
  rw [FDatabase.runRoundM] at hround
  have hcarry := mergeSaturateF_rowsCarryUF mergeFuel
    (by rw [hsigR, hsigd]; exact hb.shape) (by rw [hsigR, hsigd]; exact hb.merges)
    (hb.inv.execRunRules hb.wl') (execRunRules_noUnions hb.nounions) hround
  obtain ⟨v, lo, hv, hreach⟩ :=
    hcarry (viewName f) (as.set i x) e (columnProof k i pf q) hfired
  exact ⟨v, lo, hv, hreach⟩


/-- **One `Cmd.saturate rebuildRuleset` delivers the column closure.** -/
theorem viewRowsColumnClosed_of_runSaturateM {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d e : FDatabase} (h : d.RebuildBase P)
    (hs : d.execCmdM (Cmd.saturate rebuildRuleset) = some e) : e.ViewRowsColumnClosed P := by
  have hs' : d.runSaturateM rebuildRuleset runFuel = some e := hs
  have hbe : e.EncBase P (encodeSig P) :=
    h.base.execCmdM (c := Cmd.saturate rebuildRuleset) trivial trivial trivial trivial trivial hs
  have hve : e.Valued := FDatabase.EncBase.runSaturateM_valued runFuel h.base h.valued hs'
  exact viewRowsColumnClosed_of_roundFixed hdom hbe htr hsy hfi hcg
    (hve.rowColumnsValued hbe.eqsRefl hbe.subtermClosed hbe.inv.index)
    (FDatabase.runSaturateM_roundFixed runFuel hs')

/-- **The two shapes a source command's block has**, at the three fields `Database.UFReach`
reads as well as at `rows`. `encodeCmd_rebuilds_or_rowsFixed` is the same case split; a
`Cmd.rule` registers a rule and a `Cmd.decl` emits nothing, so neither touches any of them. -/
theorem encodeCmd_rebuilds_or_dataFixed (G : List (Var × Expr)) (c : Cmd) (n i : Nat) :
    (∃ q, (encodeCmd G c n i).1 = q ++ [Cmd.saturate rebuildRuleset]) ∨
      ∀ {d D : FDatabase}, d.execProgramM (encodeCmd G c n i).1 = some D →
        D.rows = d.rows ∧ D.terms = d.terms ∧ D.eqs = d.eqs := by
  cases c with
  | action a => exact Or.inl ⟨_, encodeCmd_action_fst G a n i⟩
  | run R => exact Or.inl ⟨[Cmd.run R], rfl⟩
  | saturate R => exact Or.inl ⟨[Cmd.saturate R], rfl⟩
  | rule r =>
      refine Or.inr fun {d D} hs => ?_
      rw [encodeCmd_rule_fst, FDatabase.execProgramM, FDatabase.execCmdM, Option.bind_some,
        FDatabase.execProgramM, Option.some.injEq] at hs
      exact hs ▸ ⟨rfl, rfl, rfl⟩
  | decl f dc =>
      refine Or.inr fun {d D} hs => ?_
      rw [show (encodeCmd G (Cmd.decl f dc) n i).1 = ([] : Program) from rfl,
        FDatabase.execProgramM, Option.some.injEq] at hs
      exact hs ▸ ⟨rfl, rfl, rfl⟩

/-- **One source command's block keeps the column closure.** -/
theorem viewRowsColumnClosed_encodeCmd {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {c : Cmd} (hc : c ∈ P) (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase}
    (h : d.RebuildBase P)
    (hr : d.ViewRowsColumnClosed P) (hs : d.execProgramM (encodeCmd G c n i).1 = some D) :
    D.ViewRowsColumnClosed P := by
  rcases encodeCmd_rebuilds_or_dataFixed G c n i with ⟨q, hq⟩ | hfix
  · rw [hq] at hs
    obtain ⟨d₂, h₂, h₃⟩ := FDatabase.execProgramM_append hs
    have hbase₂ : d₂.RebuildBase P :=
      rebuildBase_encodeCmd hdom hc
        (fun c' hc' => by rw [hq]; exact List.mem_append_left _ hc') h h₂
    have hsat : d₂.execCmdM (Cmd.saturate rebuildRuleset) = some D := by
      rw [FDatabase.execProgramM] at h₃
      obtain ⟨x, hx, hx'⟩ := Option.bind_eq_some_iff.mp h₃
      rw [FDatabase.execProgramM, Option.some.injEq] at hx'
      exact hx' ▸ hx
    exact viewRowsColumnClosed_of_runSaturateM hdom htr hsy hfi hcg hbase₂ hsat
  · obtain ⟨h₁, h₂, h₃⟩ := hfix hs
    exact hr.of_data_eq h₁ h₂ h₃

/-- **And the whole aligned run.** -/
theorem viewRowsColumnClosed_encodeCmds {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 →
      (encodeSig P).IsCtor (congrName k)) :
    ∀ (p : Program) {R : Program}, (∀ c ∈ p, c ∈ P) →
      ∀ (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase},
      d.RebuildBase P → d.ViewRowsColumnClosed P →
      d.execProgramM (encodeCmds R G p n i).1 = some D → D.ViewRowsColumnClosed P := by
  intro p
  induction p with
  | nil =>
    intro R _ G n i d D _ hr hs
    rw [show (encodeCmds R G ([] : Program) n i).1 = ([] : Program) from rfl,
      FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hr
  | cons c cs ih =>
    intro R hp G n i d D h hr hs
    rw [encodeCmds_cons_fst] at hs
    obtain ⟨d₁, h₁, h₂⟩ := FDatabase.execProgramM_append hs
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) _ _ _
      (rebuildBase_encodeCmd hdom (hp c List.mem_cons_self) (fun _ hc' => hc') h h₁)
      (viewRowsColumnClosed_encodeCmd hdom htr hsy hfi hcg (hp c List.mem_cons_self) G n i h hr
        h₁) h₂

/-- **The column rules' closure at the state `execM` returned**: a key column of a live view row
may be moved along a live `@UF` row, and the row at the moved key is one the target holds. -/
theorem execM_viewRowsColumnClosed {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.ViewRowsColumnClosed P := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) :=
    (encOk_preludeState hdom hdom.aritiesAgree' hprel).base
  have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
  have hrows₀ : d₀.rows = [] := by rw [hdata.2.1]; rfl
  have h₀ : d₀.RebuildBase P := by
    refine ⟨hb₀, ⟨fun t ht => ?_, fun b hb => ?_⟩, ?_⟩
    · rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at ht
      exact absurd ht (by simp)
    · rw [hdata.2.2.2, show FDatabase.empty.env = ([] : Env) from rfl] at hb
      exact absurd hb (by simp)
    · refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
      rw [hrows₀] at hmem
      exact absurd hmem (by simp)
  have hr₀ : d₀.ViewRowsColumnClosed P := by
    intro f k _ as e pf hrow
    rw [hrows₀] at hrow
    exact absurd hrow (by simp)
  exact viewRowsColumnClosed_encodeCmds hdom htr hsy hfi hcg P (fun _ hc => hc) [] 0 0 h₀ hr₀ hcmds

/-- **One column step at the target, with the e-class column unmoved.** The closure alone leaves
the new row's e-class column only `Database.UFReach`-reachable from the old one; both are e-class
columns of live view rows, so `execM_viewRowsRooted` makes both `@UF` row **roots** and
`execM_ufRowRoot_of_ufReach` identifies them. -/
theorem execM_columnRow_step {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ tgt.rows) {i : Nat} {ci x : Term}
    (hci : as[i]? = some ci) (hedge : tgt.UFRowEdge ci x) :
    ∃ pf', (⟨viewName f, as.set i x, [e, pf']⟩ : Row) ∈ tgt.rows := by
  obtain ⟨e', pf', hrow', hreach⟩ :=
    execM_viewRowsColumnClosed hdom htr hsy hfi hcg htgt f k hfk as e pf hrow i ci x hci hedge
  have hre : tgt.UFRowRoot e := execM_viewRowsRooted hdom hsy htr htgt f k hfk as e pf hrow
  have hre' : tgt.UFRowRoot e' :=
    execM_viewRowsRooted hdom hsy htr htgt f k hfk (as.set i x) e' pf' hrow'
  have heq : e = e' :=
    execM_ufRowRoot_of_ufReach hdom hsy htr htgt hreach e e' .refl hre .refl hre'
  exact ⟨pf', heq ▸ hrow'⟩

/-- **A whole chain of column steps.** One firing moves one column one step; this walks the
`@UF` row chain to wherever it goes, and the e-class column is unmoved at every step. -/
theorem execM_columnRow_walk {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ tgt.rows) {i : Nat} {ci r : Term}
    (hci : as[i]? = some ci) (hreach : tgt.UFRowReach ci r) :
    ∃ pf', (⟨viewName f, as.set i r, [e, pf']⟩ : Row) ∈ tgt.rows := by
  induction hreach with
  | refl =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hci
    exact ⟨pf, by rw [List.set_getElem_self hi]; exact hrow⟩
  | tail _ hstep ih =>
    obtain ⟨pf', hrow'⟩ := ih
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hci
    obtain ⟨pf'', hrow''⟩ :=
      execM_columnRow_step hdom htr hsy hfi hcg htgt hfk hrow' (i := i)
        (List.getElem?_set_self hi) hstep
    exact ⟨pf'', by rwa [List.set_set] at hrow''⟩

/-- **Every column at once**, walked left to right: a prefix already moved, the head moved by one
chain, and the rest by the recursion. -/
theorem execM_columnRow_walkList {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {e : Term} :
    ∀ (ps as bs : List Term), bs.length = as.length →
      (∀ (j : Nat) (hj : j < as.length) (hj' : j < bs.length),
        tgt.UFRowReach (as[j]) (bs[j])) →
      (∃ pf, (⟨viewName f, ps ++ as, [e, pf]⟩ : Row) ∈ tgt.rows) →
      ∃ pf, (⟨viewName f, ps ++ bs, [e, pf]⟩ : Row) ∈ tgt.rows
  | _, [], [], _, _, h => h
  | _, [], _ :: _, hlen, _, _ => by simp at hlen
  | _, _ :: _, [], hlen, _, _ => by simp at hlen
  | ps, a :: as, b :: bs, hlen, hj, ⟨pf, hrow⟩ => by
      obtain ⟨pf', hrow'⟩ :=
        execM_columnRow_walk hdom htr hsy hfi hcg htgt hfk hrow (i := ps.length) (ci := a)
          (by simp) (hj 0 (by simp) (by simp))
      rw [show (b :: bs)[0] = b from rfl,
        show (ps ++ a :: as).set ps.length b = ps ++ b :: as by simp] at hrow'
      obtain ⟨pf'', hrow''⟩ :=
        execM_columnRow_walkList hdom htr hsy hfi hcg htgt hfk (ps ++ [b]) as bs
          (by simpa using hlen)
          (fun j hj' hj'' => hj (j + 1) (by simpa using hj') (by simpa using hj''))
          ⟨pf', by simpa using hrow'⟩
      exact ⟨pf'', by simpa using hrow''⟩

/-- **The column rules at their fixpoint, for a key tuple**: a live view row's key may be moved
onto any tuple its columns reach along live `@UF` rows, and the row at the moved key is one the
target holds, at the very e-class column it started with. This is the mechanism
`Database.RebuildClosed`'s `edged` and `column` clauses were left waiting on. -/
theorem execM_viewRow_of_rowReachList {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as bs : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ tgt.rows) (hlen : bs.length = as.length)
    (hj : ∀ (j : Nat) (hj : j < as.length) (hj' : j < bs.length),
      tgt.UFRowReach (as[j]) (bs[j])) :
    ∃ pf', (⟨viewName f, bs, [e, pf']⟩ : Row) ∈ tgt.rows := by
  obtain ⟨pf', hrow'⟩ :=
    execM_columnRow_walkList hdom htr hsy hfi hcg htgt hfk [] as bs hlen hj
      ⟨pf, by simpa using hrow⟩
  exact ⟨pf', by simpa using hrow'⟩

/-- **Non-vacuous at the rule**: `columnRule` is the rule `rebuildRules` emits, spelled out at
`Encoding/Match.lean`'s witness constructor. -/
theorem columnRule_eq_wRebuildFCol : columnRule "F" 1 0 = wRebuildFCol := rfl

theorem ncProgram_isCtor_fiatName : (encodeSig ncProgram).IsCtor fiatName := by decide

theorem ncProgram_isCtor_congrName : ∀ (g : FnName) (k : Nat), (g, k) ∈ ncProgram.ctors →
    k ≠ 0 → (encodeSig ncProgram).IsCtor (congrName k) :=
  have h : ∀ p ∈ ncProgram.ctors, p.2 ≠ 0 → (encodeSig ncProgram).IsCtor (congrName p.2) := by
    decide
  fun g k hgk => h (g, k) hgk

/-- **Non-vacuous at the run**: every hypothesis of `execM_viewRowsColumnClosed` holding together,
at the program whose rule really fires. -/
theorem execM_viewRowsColumnClosed_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt) : tgt.ViewRowsColumnClosed ncProgram :=
  execM_viewRowsColumnClosed ncProgram_encodeDomain ncProgram_isCtor_transName
    ncProgram_isCtor_symName ncProgram_isCtor_fiatName ncProgram_isCtor_congrName htgt

/-! ## What the source run owes the literal exclusion

`execM_viewJoined_false` is `Database.RebuildClosed` **false** at an `execM` target of a program
every clause of `Program.EncodeDomain` admits: `ltuProgram` is a top-level `union` on two
literals, `encodeAction` writes `@UF (ordering-max 1 2) ↦ (ordering-min 1 2, @Fiat)`, and
`Database.RebuildClosed.eclass` asks the edge's two ends for a common landing site that would
have to be two different literals at once. `ProgramStep Database.empty P src` is the repair, and
what it owes the proof is the target-side reading of `Database.WF.litsIsolated`.

**The mechanism is vacuity at the source, and it is checked below.** `evalAction` refuses a
`union` on a literal, so `ltuProgram` has no source state at all — `ltuProgram_no_programStep`
— and the claim is about nothing there.

**And half of what the target side owes is already paid, by descent.**
`Term.blt` puts every literal below every application, so an `@UF` entry out of a literal points
at a term strictly below it and nothing below a literal is an application: the clause reduces to
"no `@UF` entry between two **distinct** literals" (`ufLitsIsolated_of_no_lit_lit`). That is the
form `execM_ufTermsDescend` buys, and it leaves one obligation rather than two — the *value*
clause, at the four writers of an `@UF` entry rather than at the key. -/

/-- **A top-level `union` on a literal has no source step at all.** `evalAction`'s `union` case
returns `none` when either operand is a literal, and `cmdReach` at a `Cmd.action` *is*
`evalAction`, so `CmdStep` is uninhabited there and so is `ProgramStep`. -/
theorem ltuProgram_no_programStep {src : Database} :
    ¬ ProgramStep Database.empty ltuProgram src := by
  intro h
  obtain ⟨d, hstep, -⟩ := h.cons_inv
  obtain ⟨m, hreach, -⟩ := hstep
  have hd : evalAction Database.empty
      (Action.union (.lit (.int 1)) (.lit (.int 2))) = some m := hreach
  simp [evalAction, Expr.eval, Term.isLit] at hd

/-- **And the operands of one that does are not literals**, which is the same refusal read
forwards: it is what the encoded `@UF` write's two endpoints are, since `encodeBuild_fst` makes
the target evaluate the source's own expressions. -/
theorem cmdStep_union_notLit {sd sd' : Database} {e₁ e₂ : Expr}
    (hstep : CmdStep sd (Cmd.action (Action.union e₁ e₂)) sd') :
    ∃ t₁ t₂, e₁.eval sd.sig sd.env = some t₁ ∧ e₂.eval sd.sig sd.env = some t₂ ∧
      t₁.isLit = false ∧ t₂.isLit = false := by
  obtain ⟨m, hreach, -⟩ := hstep
  have hd : evalAction sd (Action.union e₁ e₂) = some m := hreach
  rcases evalAction_eq_some hd with ⟨e, t, hc, -, -⟩ | ⟨v, e, t, hc, -, -⟩ |
    ⟨f₁, f₂, t₁, t₂, hc, h₁, h₂, hnl, -⟩ | ⟨f, args, out, as, vs, hc, -, -, -⟩
  · exact absurd hc (by simp)
  · exact absurd hc (by simp)
  · obtain ⟨rfl, rfl⟩ : e₁ = f₁ ∧ e₂ = f₂ := by
      constructor <;> [exact (Action.union.inj hc).1; exact (Action.union.inj hc).2]
    exact ⟨t₁, t₂, h₁, h₂, by simpa using (not_or.mp hnl).1, by simpa using (not_or.mp hnl).2⟩
  · exact absurd hc (by simp)

/-- **The target-side reading of `Database.WF.litsIsolated`**: no `@UF` entry of the target is
keyed on a literal it does not equal. This is what `Database.RebuildClosed.eclass` consumes at a
literal — `ViewRepr d (.lit l) e` forces `e = .lit l`, so a landing site of a literal is that
literal and an edge out of one has nowhere else to go. -/
def FDatabase.UFLitsIsolated (d : FDatabase) : Prop :=
  ∀ (l : Lit) (b pf : Term), Term.app ufName [Term.lit l, b, pf] ∈ d.terms → b = Term.lit l

/-- **Descent pays the key half.** `Term.blt` orders literals below applications, so an `@UF`
entry out of a literal points at a literal: what is left is that the two are the same one. -/
theorem ufLitsIsolated_of_no_lit_lit {d : FDatabase} (hdes : d.UFTermsDescend)
    (h : ∀ (l m : Lit) (pf : Term),
      Term.app ufName [Term.lit l, Term.lit m, pf] ∈ d.terms → m = l) :
    d.UFLitsIsolated := by
  intro l b pf hmem
  rcases FDatabase.ufTermsDescend_iff.mp hdes (Term.lit l) b pf hmem with hb | hlt
  · exact hb
  · cases b with
    | lit m => exact congrArg Term.lit (h l m pf hmem)
    | app g bs => exact absurd hlt (by simp [Term.blt])

/-- **A literal is its own `@UF` row root**, which is the form `Database.Absorbs` consumes: a
row is an entry (`FDatabase.IndexOk.entry`), so the entry-valued clause covers the rows too. -/
theorem FDatabase.UFLitsIsolated.ufRowRoot {d : FDatabase} (h : d.UFLitsIsolated)
    (hr : d.EqsRefl) (hidx : d.IndexOk) (hmg : d.sig.mergeOf ufName ≠ none) (l : Lit) :
    d.UFRowRoot (Term.lit l) := by
  intro b hedge
  obtain ⟨pf, hmem⟩ := hedge.1
  have hterm : Term.app ufName ([Term.lit l] ++ [b, pf]) ∈ d.terms :=
    mem_terms_of_indexOk hr hidx (r := ⟨ufName, [Term.lit l], [b, pf]⟩) hmem hmg
  exact hedge.2 (h l b pf (by simpa using hterm))


/-! ## A view head the target holds is a source constructor

`Database.Absorbs`' **application** case reads a view entry the target holds and then has to
apply the rules to it — the rebuild rules, whose premise is the view's own read, and the
declaration widths `Signature.MergeShape` and `Signature.MergesLegal` are stated at. All of
those are keyed on `tgt.sig (viewName f) = some (viewDecl k)`, and nothing said that a view a
target *holds an entry of* is one the prelude declared: `encodeSig_tables` answers from
`Program.ctors`, which is read off the source program's syntax, and the entry is a fact about
`tgt.terms`.

The bridge between the two is the completeness half's own invariant. `execM_soundTerms` says
every view entry term claims a source application — `EntrySound`, whose witness is a term the
*source* holds at the entry's key width — and `ctorsIn_of_programStep` says every application
a source run holds is one the program makes. So the chain is: entry term, source term,
`Program.ctors`, declaration. No new invariant on the target, and no clause of the domain. -/

/-- **A view entry term names a source constructor, at its own key width.** The source run is
the hypothesis that supplies it, through the completeness half's `FDatabase.SoundTerms` — the
same `hsrc` `execM_rebuildClosed` already takes. -/
theorem execM_viewDecl_of_mem_terms {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {f : FnName} {es : List Term} {e pf : Term}
    (hmem : Term.app (viewName f) (es ++ [e, pf]) ∈ tgt.terms) :
    tgt.sig (viewName f) = some (viewDecl es.length) ∧
      tgt.sig (termName f) = some (termDecl es.length) := by
  obtain ⟨as, hasrc, hcl, -⟩ := (execM_soundTerms hdom hsrc htgt).1 f es e pf hmem
  have hlen : as.length = es.length := hcl.length_eq
  have hctor : (f, es.length) ∈ P.ctors := by
    rw [← hlen]; exact ctorsIn_of_programStep hdom hsrc f as hasrc
  have hsig : tgt.sig = encodeSig P := (execM_encode_encBase hdom hdom.aritiesAgree' htgt).sig
  rw [hsig]
  exact encodeSig_tables hdom hdom.aritiesAgree' hctor

/-- **And the view carries a `:merge`**, which is what every reader of a view row spends:
`FDatabase.IndexOk.entry` reads a row as an entry only at a merge function, and
`Signature.MergeShape` is stated at the declaration. -/
theorem execM_mergeOf_viewName_of_mem_terms {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {f : FnName} {es : List Term} {e pf : Term}
    (hmem : Term.app (viewName f) (es ++ [e, pf]) ∈ tgt.terms) :
    tgt.sig.mergeOf (viewName f) ≠ none := by
  rw [Signature.mergeOf, (execM_viewDecl_of_mem_terms hdom hsrc htgt hmem).1]
  simp [viewDecl]

/-- **Non-vacuous at positive arity, and at the entry's own width.** `rbProgram` builds
`(W (A))`, so `Program.ctors` carries `("W", 1)` (`rbSrc_ctorsIn_W`) and the prelude declared
the view at width **one** — the width a `@WView` entry's key has, not the nullary width every
constructor-only program's prelude also installs. -/
theorem rbProgram_viewDecl_W :
    ("W", 1) ∈ rbProgram.ctors ∧ encodeSig rbProgram (viewName "W") = some (viewDecl 1) :=
  ⟨rbSrc_ctorsIn_W.2,
    (encodeSig_tables rbProgram_encodeDomain rbProgram_encodeDomain.aritiesAgree'
      rbSrc_ctorsIn_W.2).1⟩

/-! ## The literal-value clause's source-side half

`FDatabase.UFLitsIsolated`'s remaining obligation is a run-wide two-clause invariant over the
four writers of an `@UF` entry — no `@UF` row records a literal value, no view row records a
literal e-class column — and one of the four is the **top-level source `union`**, which no
syntactic clause of the domain excludes. What excludes it is the source run, and the step from
the source's own refusal (`cmdStep_union_notLit`) to the encoded block's write is exactly the
environment alignment: `encodeBuild_fst` makes the block evaluate the source's own two
expressions, `execM_env` and `envAligned_step` make it do so in the source's own environment,
and `Expr.eval_sigIndep` says the two signatures cannot disagree about the value.

That step is below, standalone. The three remaining writers — a rule head's `union`
(`Program.EncodeDomain.noLitUnion`), `mergeBody` at either table, and `pathCompressRule` — are
what the two-clause induction still owes. -/

/-- **The encoded block's `@UF` endpoints are the source's own two terms, and neither is a
literal.** The `union` head the encoder emits is
`set @UF [ordering-max e₁ e₂] [ordering-min e₁ e₂, @Fiat]` over the *source* expressions
(`encodeBuild_fst`), so this is `cmdStep_union_notLit` transported along the alignment. -/
theorem union_target_notLit {sd sd' : Database} {sig : Signature} {σ : Env} {e₁ e₂ : Expr}
    {t₁ t₂ : Term}
    (hstep : CmdStep sd (Cmd.action (Action.union e₁ e₂)) sd') (henv : σ = sd.env)
    (h₁ : e₁.eval sig σ = some t₁) (h₂ : e₂.eval sig σ = some t₂) :
    t₁.isLit = false ∧ t₂.isLit = false := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hl₁, hl₂⟩ := cmdStep_union_notLit hstep
  rw [← henv] at hu₁ hu₂
  exact ⟨by rw [Expr.eval_sigIndep e₁ h₁ hu₁]; exact hl₁,
    by rw [Expr.eval_sigIndep e₂ h₂ hu₂]; exact hl₂⟩

/-- **And the `@UF` entry it writes is between those two**, so a top-level `union` writes no
`@UF` edge with a literal at either end. `out_uf_of_execProgramM` is the read-back; the
orientation is `ordering-max`'s and is existential for the reason it is there. -/
theorem union_out_uf_notLit {sd sd' : Database} {td D : FDatabase} {e₁ e₂ : Expr} {t₁ t₂ : Term}
    {p : Program}
    (hstep : CmdStep sd (Cmd.action (Action.union e₁ e₂)) sd') (henv : td.env = sd.env)
    (hrun : td.execProgramM
      (Cmd.action (.set ufName [maxE e₁ e₂] [minE e₁ e₂, fiatE]) :: p) = some D)
    (h₁ : e₁.eval td.sig td.env = some t₁) (h₂ : e₂.eval td.sig td.env = some t₂) :
    ((∃ pf, D.toDatabase.Out ufName [t₁] [t₂, pf]) ∨
        ∃ pf, D.toDatabase.Out ufName [t₂] [t₁, pf]) ∧
      t₁.isLit = false ∧ t₂.isLit = false :=
  ⟨out_uf_of_execProgramM hrun h₁ h₂, union_target_notLit hstep henv h₁ h₂⟩

/-- **The last command of `uProgram` is a top-level `union`**, which is what makes the two
theorems above about something. -/
theorem uSrcBase_cmdStep_union :
    CmdStep uSrcBase (Cmd.action (Action.union (.app "A" []) (.app "B" []))) uSrcD := by
  refine ⟨uSrcD, ?_, .refl⟩
  change cmdEffect _ (.action (.union (.app "A" []) (.app "B" []))) = some uSrcD
  simp only [cmdEffect, evalAction, Expr.eval, Expr.evalList, uSrcD, uA, uB]
  rfl

/-- **And the transport is non-vacuous**, at the *encoded* signature and not at the source's:
`uSig` is what the prelude of `encode uProgram` installs, `(A)` and `(B)` evaluate there too,
and neither is a literal. -/
theorem uSrc_union_target_notLit :
    (Expr.app "A" []).eval uSig uSrcBase.env = some uA ∧
      (Expr.app "B" []).eval uSig uSrcBase.env = some uB ∧
      uA.isLit = false ∧ uB.isLit = false := by
  have hA : (Expr.app "A" []).eval uSig uSrcBase.env = some uA := rfl
  have hB : (Expr.app "B" []).eval uSig uSrcBase.env = some uB := rfl
  exact ⟨hA, hB, union_target_notLit uSrcBase_cmdStep_union rfl hA hB⟩

/-! ## The command induction's rule-firing case

`Egglog.UnionsFire` is stated in `Encoding/Correspond.lean`, where the invariant it feeds is,
and answered here, because everything a worked target firing reads is below that file:
`patternHolds_values_of_mem_rows` is the only route from a row to an atom,
`mem_matchQuery_of_lookup` the only route from atoms to the enumerator, and `eclassRule_fires`
the one worked composition of the two. Nothing above moved and `Encoding/Match.lean`'s
expression induction is not duplicated. -/

/-- **A query every atom of which is an entry read that a live row answers is one the
enumerator offers**, at the substitution the rows' own columns determine. `eclassRule_fires` is
this composition at a rule of fixed shape; here the shape is the hypothesis, so it applies to
the view reads `encodeQueryExpr` emits for a source query as well as to a maintenance rule's.

No congruence closure is asked of anything: `patternHolds_values_of_mem_rows` needs only
reflexive pairs. That is what keeps `Signature.AllConstructors` — and with it
`execRunRules_RunRules`, which an encoded target cannot satisfy — off the route entirely. -/
theorem mem_matchQuery_of_rows {d : FDatabase} (hcv : d.RowColumnsValued) {q : Query} {τ : Env}
    (hdef : ∀ v ∈ Query.freeVars q d.env, (Env.lookup v τ).isSome = true)
    (hval : ∀ v ∈ Query.freeVars q d.env, ∀ t, Env.lookup v τ = some t → t ∈ d.valueTerms)
    (hrow : ∀ p ∈ q, ∃ vs f as ts us, p = Pattern.values vs f as ∧
      (d.sig.mergeOf f).isSome = true ∧
      Expr.evalList d.sig as (d.env ++ Env.canon (p.freeVars d.env) τ) = some ts ∧
      Expr.evalList d.sig vs (d.env ++ Env.canon (p.freeVars d.env) τ) = some us ∧
      (⟨f, ts, us⟩ : Row) ∈ d.rows) :
    Env.canon (Query.freeVars q d.env) τ ∈ matchQuery d q := by
  refine mem_matchQuery_of_lookup hdef hval fun p hp => ?_
  obtain ⟨vs, f, as, ts, us, rfl, hmg, hats, hvus, hr⟩ := hrow p hp
  exact patternHolds_values_of_mem_rows hmg hats hvus hr
    (fun c hc => FDatabase.mem_terms_of_mem_valueTerms (hcv _ hr c hc))

/-! ### The reading through rows

`ViewRepr` ends in `Database.Out`, which reads entry **terms**; an encoded rule reads
`FDatabase.rows`. The two are not the same reading, and this is the one the atoms above
want. `Egglog.RowRepr` is stated in `Encoding/Correspond.lean`, where `Egglog.UnionsFire`
can name it; what is checked here is that it is a strengthening of `UnionsInv.readsAt`. -/

mutual

/-- **A row reading is an entry reading.** `mem_terms_of_indexOk` is the row's own entry term
and `FDatabase.EqsRefl` makes `Database.Out` read it at the key it sits at.
`ViewRepr.of_rowRepr_of_indexOk` is the same reduction off `FDatabase.IndexOk` alone, which is
the form `RowMech` spends.

The converse does not hold at the same ids: `FDatabase.EntryRowsUF` answers an entry with a row
whose e-class column is only `Database.UFReach`-reachable from the entry's, while a parent read
is keyed on its children's columns on the nose. It holds at the pointwise `@UF` row **root**,
which is `encReached_rowRepr_of_viewRepr`. -/
theorem ViewRepr.of_rowRepr {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    (hcv : d.RowColumnsValued) (hmg : ∀ g : FnName, d.sig.mergeOf (viewName g) ≠ none) :
    ∀ {t e : Term}, RowRepr d t e → ViewRepr d.toDatabase t e
  | _, _, .lit => .lit
  | _, _, @RowRepr.app _ f _ es e pf hl hrow => by
      have hout : d.toDatabase.Out (viewName f) es [e, pf] := by
        refine ⟨es, CongList.refl (fun a ha => ?_), ?_⟩
        · rw [FDatabase.toDatabase_terms]
          exact FDatabase.mem_terms_of_mem_valueTerms
            (hcv _ hrow a (List.mem_append_left _ ha))
        · rw [FDatabase.toDatabase_terms]
          exact mem_terms_of_indexOk hr hidx hrow (hmg _)
      exact .app (ViewReprList.of_rowReprList hr hidx hcv hmg hl) hout

@[inherit_doc ViewRepr.of_rowRepr]
theorem ViewReprList.of_rowReprList {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    (hcv : d.RowColumnsValued) (hmg : ∀ g : FnName, d.sig.mergeOf (viewName g) ≠ none) :
    ∀ {ts es : List Term}, RowReprList d ts es → ViewReprList d.toDatabase ts es
  | _, _, .nil => .nil
  | _, _, .cons h hl =>
      .cons (ViewRepr.of_rowRepr hr hidx hcv hmg h)
        (ViewReprList.of_rowReprList hr hidx hcv hmg hl)

end

/-! ### The chain, run end to end

At `ncTgt`, which is the state `Database.ReadsSelf` is refuted at (`ncTgt_not_readsSelf`) and
`Database.UnionsJoined` holds at (`ncTgt_unionsJoined`). The source rule fired at `x := (B)`
and built `(F (B))`; the encoded rule fires at the **id** `(A)`, because `mergeResult` keeps
`ordering-min` and the `@FView` row sits at the leader. Nothing here is decided: `closureF` does
not reduce in the kernel, so the match is *proved*, through `mem_matchQuery_of_rows`. -/

/-- The encoding of the source rule `ncProgram` installs. -/
def ncEncRule : Rule := (encodeRule 0 ncRule 0).1

/-- Its query: one view read, with the source variable in the key column and the read's two
generated columns. -/
theorem ncEncRule_query :
    ncEncRule.query = [Pattern.values [.var "@v0", .var "@v1"] (viewName "F") [.var "x"]] := rfl

/-- Its head: `encodeBuild`'s two `set`s for `(F x)`, the view entry under `@Fiat`. -/
theorem ncEncRule_actions :
    ncEncRule.actions
      = [Action.set (termName "F") [.var "x", .app "F" [.var "x"]] [],
         Action.set (viewName "F") [.var "x"] [.app "F" [.var "x"], fiatE]] := rfl

theorem ncEncRule_mem : ncEncRule ∈ ncTgt.rules := List.mem_cons_self

theorem ncTgt_env : ncTgt.env = [] := rfl

theorem ncTgt_row_fview : (⟨viewName "F", [ncA], [ncFA, ncFiat]⟩ : Row) ∈ ncTgt.rows := by decide

theorem ncTgt_row_bview : (⟨viewName "B", [], [ncA, ncTFF]⟩ : Row) ∈ ncTgt.rows := by decide

theorem ncTgt_rowColumnsValued : ncTgt.RowColumnsValued := by
  change ∀ r ∈ ncTgt.rows, ∀ t ∈ r.args ++ r.out, t ∈ ncTgt.valueTerms
  decide

/-- **The id substitution.** The source rule fired at `x := (B)`; the encoded one fires at the
id `(A)` that `(B)`'s row records, and at the read's own two columns. -/
def ncIdSubst : Env := [("@v0", ncFA), ("@v1", ncFiat), ("x", ncA)]

theorem ncTgt_freeVars : Query.freeVars ncEncRule.query ncTgt.env = ["@v0", "@v1", "x"] := rfl

theorem ncTgt_canon :
    Env.canon (Query.freeVars ncEncRule.query ncTgt.env) ncIdSubst = ncIdSubst := rfl

/-- **The encoded query matches at the id substitution.** -/
theorem ncTgt_mem_matchQuery : ncIdSubst ∈ matchQuery ncTgt ncEncRule.query := by
  rw [← ncTgt_canon]
  refine mem_matchQuery_of_rows ncTgt_rowColumnsValued (fun v hv => ?_) (fun v hv t ht => ?_)
    (fun p hp => ?_)
  · rw [ncTgt_freeVars] at hv
    rcases (by simpa using hv : v = "@v0" ∨ v = "@v1" ∨ v = "x") with rfl | rfl | rfl <;> rfl
  · rw [ncTgt_freeVars] at hv
    rcases (by simpa using hv : v = "@v0" ∨ v = "@v1" ∨ v = "x") with rfl | rfl | rfl <;>
      · obtain rfl : t = _ := Option.some.inj ht.symm
        decide
  · obtain rfl : p = Pattern.values [.var "@v0", .var "@v1"] (viewName "F") [.var "x"] := by
      simpa [ncEncRule_query] using hp
    exact ⟨_, _, _, [ncA], [ncFA, ncFiat], rfl, by decide, rfl, rfl, ncTgt_row_fview⟩

/-- **The row reading at the member whose own row moved**: `(B)`'s view row was re-keyed onto
the leader `(A)`, so the id `(B)` reads to is `(A)`. -/
theorem ncTgt_rowRepr_B : RowRepr ncTgt ncB ncA := .app .nil ncTgt_row_bview

theorem ncTgt_row_aview : (⟨viewName "A", [], [ncA, ncFiat]⟩ : Row) ∈ ncTgt.rows := by decide

/-- **The leader's own reading**, off the row its build wrote and nothing displaced. -/
theorem ncTgt_rowRepr_A : RowRepr ncTgt ncA ncA := .app .nil ncTgt_row_aview

/-- **`FDatabase.RowJoined.edge` where it has content**: a real `@UF` edge, two **distinct**
source terms reading its two ends through entry terms, and one row reading for both.

This is the clause `unionsJoined_fire` turns `Database.UnionsJoined`'s edge between *ids* into
the equality an emitted `.eq` atom compares, and it is what `Database.ViewLeader` would have
given had it been true. It is not: `(B)` reads to `(B)` and to `(A)` through entries
(`ncTgt_ids_B`), so the entry reading has no representative here, while through live **rows**
both `(A)` and `(B)` read to `(A)` alone — the row a merge displaced is gone where its entry
term stays. `rbState2_rowJoined` is the same clause at the witness state, where `fn` carries
the content and this one is vacuous. -/
theorem ncTgt_rowJoined_edge :
    ncTgt.toDatabase.Out ufName [ncB] [ncA, ncFiat] ∧
      ViewRepr ncTgt.toDatabase ncB ncB ∧ ViewRepr ncTgt.toDatabase ncA ncA ∧ ncB ≠ ncA ∧
      RowRepr ncTgt ncB ncA ∧ RowRepr ncTgt ncA ncA :=
  ⟨ncTgt_out_uf, ncTgt_viewRepr_B, ncTgt_viewRepr_A, by simp [ncA, ncB],
   ncTgt_rowRepr_B, ncTgt_rowRepr_A⟩

/-- **And the term the source's firing built reads through it**, at the state where
`Database.ReadsSelf` fails: `(F (B))` reads to `(F (A))`, over `(B)`'s row and then the
`@FView` row keyed at `(A)`. -/
theorem ncTgt_rowRepr_FB : RowRepr ncTgt ncFB ncFA :=
  .app (.cons ncTgt_rowRepr_B .nil) ncTgt_row_fview

theorem ncTgt_isCtor_F : ncTgt.sig.IsCtor "F" := by decide

/-- The head's key and skolem, evaluated at the id substitution. -/
theorem ncTgt_evalList_head :
    Expr.evalList ncTgt.sig [Expr.var "x", .app "F" [.var "x"]] (ncTgt.env ++ ncIdSubst)
      = some [ncA, ncFA] := by
  have hx : Expr.eval ncTgt.sig (.var "x") (ncTgt.env ++ ncIdSubst) = some ncA := rfl
  simp only [Expr.evalList, hx, Option.bind_some, Option.map_some,
    Expr.eval_app_ctor (show Prim.ofName "F" = none from rfl) ncTgt_isCtor_F]
  rfl

/-- The state the encoded rule's own firing returns: the two `set`s its head emitted, at the
ids the match bound. -/
def ncFired : FDatabase :=
  { ((({ ncTgt with env := ncTgt.env ++ ncIdSubst } : FDatabase).addRow
        (termName "F") [ncA, ncFA] []).addRow (viewName "F") [ncA] [ncFA, ncFiat]) with
      env := ncTgt.env, rules := ncTgt.rules }

theorem ncFired_row : (⟨viewName "F", [ncA], [ncFA, ncFiat]⟩ : Row) ∈ ncFired.rows :=
  @mem_addRow_rows_self
    ((({ ncTgt with env := ncTgt.env ++ ncIdSubst } : FDatabase).addRow
      (termName "F") [ncA, ncFA] [])) (viewName "F") [ncA] [ncFA, ncFiat]

/-- **The block evaluates**, which is the half of a firing a valid substitution is not. -/
theorem ncTgt_encRule_fired : Fired ncTgt ncEncRule ncIdSubst ncFired := by
  change execLocalActions ncTgt ncEncRule.actions ncIdSubst = some _
  rw [execLocalActions, ncEncRule_actions]
  simp only [execActions, Egglog.execAction, ncTgt_evalList_head, Option.bind_some]
  rfl

/-- **The chain, end to end**: the row makes the encoded atom hold, the atom makes the
enumerator offer the id substitution, the block evaluates, and the head's row is one the
round's post-state records. -/
theorem ncTgt_encRule_fires :
    (⟨viewName "F", [ncA], [ncFA, ncFiat]⟩ : Row) ∈ (execRunRules "r" ncTgt).rows :=
  mem_rows_execRunRules.mpr (Or.inr ⟨ncEncRule, ncEncRule_mem, rfl, ncIdSubst,
    ncTgt_mem_matchQuery, ncFired, ncTgt_encRule_fired, ncFired_row⟩)

/-! ### The forward mirror of `Encoding/Match.lean`

`Encoding/Match.lean` runs the query correspondence **target → source**: a match of the emitted
query becomes a source `ValidQuerySubst`. What a firing needs is the other direction — a source
reading, turned into a substitution the *emitted* query matches at — and that is this section.

Two features of `encodeQuery` are the whole of it.

**Flattening.** An application pattern becomes several atoms joined by intermediate variables,
so the reading has to bind not only the source query's variables but every generated one, each
to the id of the subterm at that position. `RowRead` is that reading, and it carries the ids
through **live rows**, which is what a query reads (`RowRepr` is the same shape over a source
term; `EncAtom` is what one emitted atom asks of a reading).

**The fresh-variable supply.** `encodeQuery` threads a counter, and one reading has to answer
every atom of the whole query at once. `FreshEnv` is the invariant that makes the blocks
compose: a block's bindings are numbered inside *its own* stretch of the counter, so two blocks'
domains are disjoint (`freshVar_inj`) and their concatenation binds each of them
(`Env.lookup_of_mem_nodup`). Non-collision with the source's own variables is the `@` prefix —
`atPrefix_freshVar` against `FDatabase.NoAtEnv` and the reading's own `hnoAtVar` — so the
source bindings sit in front of the generated ones and neither shadows the other. -/

/-- `encodeQueryExpr` returns a literal unchanged and emits no atom. -/
theorem encodeQueryExpr_lit {l : Lit} {n : Nat} :
    encodeQueryExpr (.lit l) n = (.lit l, [], n) := rfl

/-- An application consumes two generated variables past its arguments': an e-class and a
premise proof. -/
theorem encodeQueryExpr_app_next {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).2.2 = (encodeQueryArgs args n).2.2 + 2 := rfl

theorem encodeQueryArgs_nil {n : Nat} : encodeQueryArgs [] n = ([], [], n) := rfl

@[inherit_doc encodeQueryExpr_app_next]
theorem encodeQueryArgs_cons_next {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).2.2 = (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2 := rfl

@[inherit_doc encodeQueryExpr_app_next]
theorem encodePattern_expr_next {e : Expr} {n : Nat} :
    (encodePattern (.expr e) n).2 = (encodeQueryExpr e n).2.2 := rfl

@[inherit_doc encodeQueryExpr_app_next]
theorem encodePattern_eq_next {e₁ e₂ : Expr} {n : Nat} :
    (encodePattern (.eq e₁ e₂) n).2
      = (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).2.2 := rfl

@[inherit_doc encodeQueryExpr_app_next]
theorem encodeQuery_cons_next {p : Pattern} {ps : Query} {n : Nat} :
    (encodeQuery (p :: ps) n).2 = (encodeQuery ps (encodePattern p n).2).2 := rfl

mutual

/-- **The counter only ever advances.** What makes one block's stretch of generated variables
disjoint from the next's. -/
theorem le_encodeQueryExpr_next : ∀ (e : Expr) (n : Nat), n ≤ (encodeQueryExpr e n).2.2
  | .lit _, n => Nat.le_refl n
  | .var _, n => Nat.le_refl n
  | .app _ args, n => by
      rw [encodeQueryExpr_app_next]
      exact Nat.le_trans (le_encodeQueryArgs_next args n) (Nat.le_add_right _ 2)

@[inherit_doc le_encodeQueryExpr_next]
theorem le_encodeQueryArgs_next : ∀ (es : List Expr) (n : Nat), n ≤ (encodeQueryArgs es n).2.2
  | [], n => Nat.le_refl n
  | e :: es, n => by
      rw [encodeQueryArgs_cons_next]
      exact Nat.le_trans (le_encodeQueryExpr_next e n) (le_encodeQueryArgs_next es _)

end

@[inherit_doc le_encodeQueryExpr_next]
theorem le_encodePattern_next : ∀ (p : Pattern) (n : Nat), n ≤ (encodePattern p n).2
  | .values _ _ _, n => Nat.le_refl n
  | .expr e, n => by rw [encodePattern_expr_next]; exact le_encodeQueryExpr_next e n
  | .eq e₁ e₂, n => by
      rw [encodePattern_eq_next]
      exact Nat.le_trans (le_encodeQueryExpr_next e₁ n) (le_encodeQueryExpr_next e₂ _)

@[inherit_doc le_encodeQueryExpr_next]
theorem le_encodeQuery_next : ∀ (q : Query) (n : Nat), n ≤ (encodeQuery q n).2
  | [], n => Nat.le_refl n
  | p :: ps, n => by
      rw [encodeQuery_cons_next]
      exact Nat.le_trans (le_encodePattern_next p n) (le_encodeQuery_next ps _)

/-- **The supply is injective**, so two blocks numbered apart bind different variables.
`toString_nat_inj` is the digits, and `String.append` cancels the `"@v"`. -/
theorem freshVar_inj {i j : Nat} (h : freshVar i = freshVar j) : i = j := by
  have h2 : (freshVar i).toList = (freshVar j).toList := by rw [h]
  rw [freshVar, freshVar, String.toList_append, String.toList_append] at h2
  exact toString_nat_inj (String.toList_inj.mp (List.append_cancel_left h2))

/-- **And it is in the generated namespace**, which is what keeps it clear of the source's own
variables and of `FDatabase.NoAtEnv`'s environment. -/
theorem atPrefix_freshVar (n : Nat) : "@".isPrefixOf (freshVar n) = true := by
  rw [freshVar, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@v").toList = ['@', 'v'] from by decide]
  exact ⟨'v' :: (toString n).toList, rfl⟩

/-- A binding of an environment with distinct keys is the one `lookup` finds. -/
theorem Env.lookup_of_mem_nodup : ∀ {σ : Env} {b : Var × Term}, b ∈ σ →
    (Env.dom σ).Nodup → Env.lookup b.1 σ = some b.2
  | [], _, hb, _ => absurd hb (by simp)
  | c :: cs, b, hb, hnd => by
      rw [Env.dom_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hb with rfl | hb'
      · rw [Env.lookup_cons, if_pos rfl]
      · have hne : b.1 ≠ c.1 := fun hc => hnd.1 (hc ▸ Env.mem_dom_of_mem hb')
        rw [Env.lookup_cons, if_neg hne]
        exact Env.lookup_of_mem_nodup hb' hnd.2

/-- **What one emitted atom asks of a reading.** A view read wants a live row at the ids its
key columns evaluate to; an id comparison wants **one** id, because an encoded target asserts
nothing (`execM_encode_eqsRefl`) and there congruence is equality. `.expr` never occurs:
`encodePattern` emits only reads and comparisons. -/
def EncAtom (d : FDatabase) (ρ : Env) : Pattern → Prop
  | .values vs f as => (d.sig.mergeOf f).isSome = true ∧ ∃ ts us,
      Expr.evalList d.sig as ρ = some ts ∧ Expr.evalList d.sig vs ρ = some us ∧
      (⟨f, ts, us⟩ : Row) ∈ d.rows
  | .eq e₁ e₂ => ∃ i, Expr.eval d.sig e₁ ρ = some i ∧ Expr.eval d.sig e₂ ρ = some i ∧
      i ∈ d.terms
  | .expr _ => False

mutual

/-- **The forward mirror of `QueryRead`**: under the source reading `ρs` and the target reading
`ρt`, the source instance of `e` is `t` and the id the emitted reads bind it to is `i`, through
**live rows**.

`RowRepr` over the *shape of the pattern* rather than of a source term: the leaves are supplied
by the two environments, and a variable's id is the target reading's, which is what keeps one id
per variable across every atom that mentions it. -/
inductive RowRead (sig : Signature) (d : FDatabase) (ρs ρt : Env) :
    Expr → Term → Term → Prop where
  | lit {l : Lit} : RowRead sig d ρs ρt (.lit l) (.lit l) (.lit l)
  | var {v : Var} {t i : Term} :
      Env.lookup v ρs = some t → Env.lookup v ρt = some i → RowRead sig d ρs ρt (.var v) t i
  | app {f : FnName} {args : List Expr} {ts is : List Term} {i pf : Term} :
      Prim.ofName f = none → sig.IsCtor f →
      (d.sig.mergeOf (viewName f)).isSome = true →
      RowReadList sig d ρs ρt args ts is →
      (⟨viewName f, is, [i, pf]⟩ : Row) ∈ d.rows →
      RowRead sig d ρs ρt (.app f args) (.app f ts) i

/-- `RowRead` over an argument list. -/
inductive RowReadList (sig : Signature) (d : FDatabase) (ρs ρt : Env) :
    List Expr → List Term → List Term → Prop where
  | nil : RowReadList sig d ρs ρt [] [] []
  | cons {a : Expr} {t i : Term} {as : List Expr} {ts is : List Term} :
      RowRead sig d ρs ρt a t i → RowReadList sig d ρs ρt as ts is →
      RowReadList sig d ρs ρt (a :: as) (t :: ts) (i :: is)

end

/-- **The forward mirror of `PatternRead`.** A `.eq` reads **one** id for both sides, which is
what the emitted `.eq` atom compares, and it asks the target to hold it — the witness
`patternHolds` wants. There is no `.values` case: `Pattern.NoValues` is a domain condition and
`encodePattern` passes a source entry atom through unchanged. -/
inductive PatternRowRead (sig : Signature) (d : FDatabase) (ρs ρt : Env) : Pattern → Prop where
  | expr {e : Expr} {t i : Term} :
      RowRead sig d ρs ρt e t i → PatternRowRead sig d ρs ρt (.expr e)
  | eq {e₁ e₂ : Expr} {t₁ t₂ i : Term} :
      RowRead sig d ρs ρt e₁ t₁ i → RowRead sig d ρs ρt e₂ t₂ i → i ∈ d.terms →
      PatternRowRead sig d ρs ρt (.eq e₁ e₂)

mutual

/-- **The source instance the reading carries is the one the source evaluates**, which is what
ties a `RowRead` back to `Matches`. -/
theorem RowRead.eval_src {sig : Signature} {d : FDatabase} {ρs ρt : Env} :
    ∀ {e : Expr} {t i : Term}, RowRead sig d ρs ρt e t i → Expr.eval sig e ρs = some t
  | _, _, _, .lit => rfl
  | _, _, _, .var ht _ => by rw [Expr.eval_var]; exact ht
  | _, _, _, .app hp hc _ hl _ => by
      rw [Expr.eval, hp, if_pos hc, RowReadList.evalList_src hl]; rfl

@[inherit_doc RowRead.eval_src]
theorem RowReadList.evalList_src {sig : Signature} {d : FDatabase} {ρs ρt : Env} :
    ∀ {es : List Expr} {ts is : List Term}, RowReadList sig d ρs ρt es ts is →
      Expr.evalList sig es ρs = some ts
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hl => by
      rw [Expr.evalList_cons, h.eval_src, Option.bind_some, RowReadList.evalList_src hl]; rfl

end

/-- **The generated bindings one emitted block needs**: numbered inside the block's own stretch
`[n, m)` of the counter, distinct, and drawn from where the enumerator assigns. The three
clauses are what make the blocks compose — the range gives disjointness, `nodup` makes the
concatenation bind each of them, and `valued` is `matchQuery`'s own universe. -/
structure FreshEnv (d : FDatabase) (n m : Nat) (σ : Env) : Prop where
  /-- Every key is a generated variable of this block's stretch. -/
  fresh : ∀ b ∈ σ, ∃ k, n ≤ k ∧ k < m ∧ b.1 = freshVar k
  /-- No key twice. -/
  nodup : (Env.dom σ).Nodup
  /-- Every value is one `matchQuery` assigns. -/
  valued : ∀ b ∈ σ, b.2 ∈ d.valueTerms

theorem FreshEnv.nil {d : FDatabase} {n m : Nat} : FreshEnv d n m [] :=
  ⟨by simp, by simp [Env.dom], by simp⟩

theorem FreshEnv.mono {d : FDatabase} {n m n' m' : Nat} {σ : Env} (h : FreshEnv d n m σ)
    (hn : n' ≤ n) (hm : m ≤ m') : FreshEnv d n' m' σ :=
  ⟨fun b hb => (h.fresh b hb).imp fun _ hk =>
      ⟨Nat.le_trans hn hk.1, Nat.lt_of_lt_of_le hk.2.1 hm, hk.2.2⟩,
    h.nodup, h.valued⟩

/-- **Two adjacent blocks' bindings concatenate.** The `nodup` of the result is where
`freshVar_inj` is spent: the left block's keys are numbered below `m` and the right block's at
or above it, so no key of one is a key of the other. -/
theorem FreshEnv.append {d : FDatabase} {n m k : Nat} {σ₁ σ₂ : Env}
    (h₁ : FreshEnv d n m σ₁) (h₂ : FreshEnv d m k σ₂) (hnm : n ≤ m) (hmk : m ≤ k) :
    FreshEnv d n k (σ₁ ++ σ₂) := by
  refine ⟨fun b hb => ?_, ?_, fun b hb => ?_⟩
  · rcases List.mem_append.mp hb with hb' | hb'
    · exact (h₁.mono (Nat.le_refl n) hmk).fresh b hb'
    · exact (h₂.mono hnm (Nat.le_refl k)).fresh b hb'
  · rw [Env.dom, List.map_append]
    refine List.Nodup.append h₁.nodup h₂.nodup ?_
    intro v hv₁ hv₂
    obtain ⟨b₁, hb₁, rfl⟩ := List.mem_map.mp hv₁
    obtain ⟨b₂, hb₂, hb₂'⟩ := List.mem_map.mp hv₂
    obtain ⟨k₁, -, hk₁, he₁⟩ := h₁.fresh b₁ hb₁
    obtain ⟨k₂, hk₂, -, he₂⟩ := h₂.fresh b₂ hb₂
    have : k₂ = k₁ := freshVar_inj (he₂.symm.trans (hb₂'.trans he₁))
    omega
  · rcases List.mem_append.mp hb with hb' | hb'
    · exact h₁.valued b hb'
    · exact h₂.valued b hb'

mutual

/-- **The flattening, mirrored.** One source expression's reading produces the generated
bindings its emitted block wants, and then *any* reading extending them and the target
substitution answers every atom of the block with a live row and evaluates the naming
expression to the id.

Quantifying over the extension rather than fixing it is what lets the blocks be glued: the
whole query's reading is one environment, and each block only ever asks that its own bindings
survive in it. -/
theorem exists_freshEnv_encodeQueryExpr {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hcv : d.RowColumnsValued) :
    ∀ {e : Expr} {t i : Term}, RowRead sig d ρs ρt e t i → ∀ n : Nat,
      ∃ σ : Env, FreshEnv d n (encodeQueryExpr e n).2.2 σ ∧
        ∀ ρ : Env, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ (v : Var) (j : Term), Env.lookup v ρt = some j → Env.lookup v ρ = some j) →
          Expr.eval d.sig (encodeQueryExpr e n).1 ρ = some i ∧
          ∀ a ∈ (encodeQueryExpr e n).2.1, EncAtom d ρ a
  | _, _, _, .lit, _ =>
      ⟨[], FreshEnv.nil, fun _ _ _ => ⟨rfl, by intro a ha; cases ha⟩⟩
  | _, _, _, .var _ hi, _ =>
      ⟨[], FreshEnv.nil, fun _ _ hext => ⟨hext _ _ hi, by intro a ha; cases ha⟩⟩
  | _, _, _, @RowRead.app _ _ _ _ f args ts is i pf _ _ hmg hl hrow, n => by
      obtain ⟨σ₀, hf₀, hp₀⟩ := exists_freshEnv_encodeQueryArgs hcv hl n
      set m := (encodeQueryArgs args n).2.2 with hm
      have hcol : ∀ c ∈ is ++ [i, pf], c ∈ d.valueTerms := hcv _ hrow
      have hne : freshVar m ≠ freshVar (m + 1) := fun hc => by
        have := freshVar_inj hc; omega
      have htail : FreshEnv d m (m + 2) [(freshVar m, i), (freshVar (m + 1), pf)] := by
        refine ⟨fun b hb => ?_, ?_, fun b hb => ?_⟩
        · rcases (by simpa using hb : b = (freshVar m, i) ∨ b = (freshVar (m+1), pf)) with rfl|rfl
          · exact ⟨m, Nat.le_refl m, by omega, rfl⟩
          · exact ⟨m + 1, by omega, by omega, rfl⟩
        · simpa [Env.dom] using hne
        · rcases (by simpa using hb : b = (freshVar m, i) ∨ b = (freshVar (m+1), pf)) with rfl|rfl
          · exact hcol i (by simp)
          · exact hcol pf (by simp)
      refine ⟨σ₀ ++ [(freshVar m, i), (freshVar (m + 1), pf)], ?_, fun ρ hσ hext => ?_⟩
      · rw [encodeQueryExpr_app_next, ← hm]
        exact FreshEnv.append hf₀ htail (le_encodeQueryArgs_next args n) (by omega)
      · have hσ₀ : ∀ b ∈ σ₀, Env.lookup b.1 ρ = some b.2 :=
          fun b hb => hσ b (List.mem_append_left _ hb)
        have him : Env.lookup (freshVar m) ρ = some i := hσ (freshVar m, i) (by simp)
        have hpf : Env.lookup (freshVar (m + 1)) ρ = some pf := hσ (freshVar (m+1), pf) (by simp)
        obtain ⟨hargs, hatoms⟩ := hp₀ ρ hσ₀ hext
        refine ⟨by rw [encodeQueryExpr_app_expr, Expr.eval_var, ← hm]; exact him, fun a ha => ?_⟩
        rw [encodeQueryExpr_app_atoms] at ha
        rcases List.mem_append.mp ha with ha' | ha'
        · exact hatoms a ha'
        · obtain rfl : a = Pattern.values [.var (freshVar m), .var (freshVar (m + 1))]
              (viewName f) (encodeQueryArgs args n).1 := by simpa [hm] using ha'
          exact ⟨hmg, is, [i, pf], hargs, Expr.evalList_pair_var him hpf, hrow⟩

@[inherit_doc exists_freshEnv_encodeQueryExpr]
theorem exists_freshEnv_encodeQueryArgs {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hcv : d.RowColumnsValued) :
    ∀ {es : List Expr} {ts is : List Term}, RowReadList sig d ρs ρt es ts is → ∀ n : Nat,
      ∃ σ : Env, FreshEnv d n (encodeQueryArgs es n).2.2 σ ∧
        ∀ ρ : Env, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ (v : Var) (j : Term), Env.lookup v ρt = some j → Env.lookup v ρ = some j) →
          Expr.evalList d.sig (encodeQueryArgs es n).1 ρ = some is ∧
          ∀ a ∈ (encodeQueryArgs es n).2.1, EncAtom d ρ a
  | _, _, _, .nil, _ =>
      ⟨[], FreshEnv.nil, fun _ _ _ => ⟨rfl, by intro a ha; cases ha⟩⟩
  | _, _, _, @RowReadList.cons _ _ _ _ a t i as ts is h hl, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := exists_freshEnv_encodeQueryExpr hcv h n
      obtain ⟨σ₂, hf₂, hp₂⟩ := exists_freshEnv_encodeQueryArgs hcv hl (encodeQueryExpr a n).2.2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext => ?_⟩
      · rw [encodeQueryArgs_cons_next]
        exact FreshEnv.append hf₁ hf₂ (le_encodeQueryExpr_next a n)
          (le_encodeQueryArgs_next as _)
      · obtain ⟨he₁, ha₁⟩ := hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        obtain ⟨he₂, ha₂⟩ := hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext
        refine ⟨?_, fun x hx => ?_⟩
        · rw [encodeQueryArgs_cons_exprs, Expr.evalList_cons, he₁, Option.bind_some, he₂]; rfl
        · rw [encodeQueryArgs_cons_atoms] at hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact ha₁ x hx'
          · exact ha₂ x hx'

end

/-- **One source pattern's block, mirrored.** A `.expr` is its expression's reads; a `.eq` is
both sides' reads and then the comparison, which the single id `PatternRowRead.eq` carries
answers. -/
theorem exists_freshEnv_encodePattern {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hcv : d.RowColumnsValued) :
    ∀ {p : Pattern}, PatternRowRead sig d ρs ρt p → ∀ n : Nat,
      ∃ σ : Env, FreshEnv d n (encodePattern p n).2 σ ∧
        ∀ ρ : Env, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ (v : Var) (j : Term), Env.lookup v ρt = some j → Env.lookup v ρ = some j) →
          ∀ a ∈ (encodePattern p n).1, EncAtom d ρ a
  | _, @PatternRowRead.expr _ _ _ _ e _ _ h, n => by
      obtain ⟨σ, hf, hp⟩ := exists_freshEnv_encodeQueryExpr hcv h n
      refine ⟨σ, by rw [encodePattern_expr_next]; exact hf, fun ρ hσ hext a ha => ?_⟩
      rw [encodePattern_expr_atoms] at ha
      exact (hp ρ hσ hext).2 a ha
  | _, @PatternRowRead.eq _ _ _ _ e₁ e₂ _ _ i h₁ h₂ hi, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := exists_freshEnv_encodeQueryExpr hcv h₁ n
      obtain ⟨σ₂, hf₂, hp₂⟩ :=
        exists_freshEnv_encodeQueryExpr hcv h₂ (encodeQueryExpr e₁ n).2.2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext a ha => ?_⟩
      · rw [encodePattern_eq_next]
        exact FreshEnv.append hf₁ hf₂ (le_encodeQueryExpr_next e₁ n)
          (le_encodeQueryExpr_next e₂ _)
      · obtain ⟨he₁, ha₁⟩ := hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        obtain ⟨he₂, ha₂⟩ := hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext
        rw [encodePattern_eq_atoms] at ha
        rcases List.mem_append.mp ha with ha' | ha'
        · rcases List.mem_append.mp ha' with ha'' | ha''
          · exact ha₁ a ha''
          · exact ha₂ a ha''
        · obtain rfl : a = Pattern.eq (encodeQueryExpr e₁ n).1
              (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1 := by simpa using ha'
          exact ⟨i, he₁, he₂, hi⟩

/-- **The whole query, mirrored**: one reading answering every emitted atom at once. -/
theorem exists_freshEnv_encodeQuery {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hcv : d.RowColumnsValued) :
    ∀ {q : Query}, (∀ p ∈ q, PatternRowRead sig d ρs ρt p) → ∀ n : Nat,
      ∃ σ : Env, FreshEnv d n (encodeQuery q n).2 σ ∧
        ∀ ρ : Env, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ (v : Var) (j : Term), Env.lookup v ρt = some j → Env.lookup v ρ = some j) →
          ∀ a ∈ (encodeQuery q n).1, EncAtom d ρ a
  | [], _, _ => ⟨[], FreshEnv.nil, fun _ _ _ => by intro a ha; cases ha⟩
  | p :: ps, hq, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := exists_freshEnv_encodePattern hcv (hq p List.mem_cons_self) n
      obtain ⟨σ₂, hf₂, hp₂⟩ := exists_freshEnv_encodeQuery hcv
        (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (encodePattern p n).2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext a ha => ?_⟩
      · rw [encodeQuery_cons_next]
        exact FreshEnv.append hf₁ hf₂ (le_encodePattern_next p n) (le_encodeQuery_next ps _)
      · rw [encodeQuery_cons_atoms] at ha
        rcases List.mem_append.mp ha with ha' | ha'
        · exact hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext a ha'
        · exact hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext a ha'

/-! #### From the atoms to the enumerator

`mem_matchQuery_of_lookup` wants three things of the substitution — every free variable bound,
every value one `assignments` draws, and `patternHolds` per atom under the atom's own
restriction. All three come off `EncAtom`: the evaluations it carries bind the variables, the
row columns are `FDatabase.RowColumnsValued`, and `Env.canon` is invisible to an atom because a
variable it drops is one the environment already binds. -/

mutual

/-- **A variable of an expression that evaluates is bound.** `Expr.lookup_isSome_of_mem_evalList`
at every variable rather than only at a top-level one. -/
theorem Expr.lookup_isSome_of_mem_vars {sig : Signature} {ρ : Env} {v : Var} :
    ∀ {e : Expr} {t : Term}, Expr.eval sig e ρ = some t → v ∈ e.vars →
      (Env.lookup v ρ).isSome
  | .lit _, _, _, hv => by simp [Expr.vars] at hv
  | .var w, _, he, hv => by
      obtain rfl : v = w := by simpa [Expr.vars] using hv
      rw [Expr.eval_var] at he; rw [he]; rfl
  | .app f args, t, he, hv => by
      rw [Expr.vars] at hv
      have hl : ∃ ts, Expr.evalList sig args ρ = some ts := by
        rw [Expr.eval] at he
        split at he
        · obtain ⟨ts, hts, -⟩ := Option.bind_eq_some_iff.mp he; exact ⟨ts, hts⟩
        · split at he
          · obtain ⟨ts, hts, -⟩ := Option.map_eq_some_iff.mp he; exact ⟨ts, hts⟩
          · exact absurd he (by simp)
      obtain ⟨ts, hts⟩ := hl
      exact Expr.lookup_isSome_of_mem_varsList hts hv

@[inherit_doc Expr.lookup_isSome_of_mem_vars]
theorem Expr.lookup_isSome_of_mem_varsList {sig : Signature} {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      v ∈ Expr.varsList es → (Env.lookup v ρ).isSome
  | [], _, _, hv => by simp [Expr.varsList] at hv
  | e :: es, _, he, hv => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨t, ht, he'⟩ := he
      obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp he'
      rw [Expr.varsList, List.mem_union_iff] at hv
      exact hv.elim (fun h => Expr.lookup_isSome_of_mem_vars ht h)
        (fun h => Expr.lookup_isSome_of_mem_varsList hus h)

end

mutual

/-- **A free variable is a variable the environment does not bind.** -/
theorem Expr.mem_vars_of_mem_freeVars {σ : Env} :
    ∀ {e : Expr} {v : Var}, v ∈ e.freeVars σ → v ∈ e.vars ∧ Env.lookup v σ = none
  | .lit _, _, hv => by simp [Expr.freeVars] at hv
  | .var w, v, hv => by
      rw [Expr.freeVars] at hv
      split at hv
      · exact absurd hv (by simp)
      · next hn =>
        obtain rfl : v = w := by simpa using hv
        exact ⟨by simp [Expr.vars], Option.not_isSome_iff_eq_none.mp hn⟩
  | .app _ args, _, hv => Expr.mem_varsList_of_mem_freeVarsList hv

@[inherit_doc Expr.mem_vars_of_mem_freeVars]
theorem Expr.mem_varsList_of_mem_freeVarsList {σ : Env} :
    ∀ {es : List Expr} {v : Var}, v ∈ Expr.freeVarsList es σ →
      v ∈ Expr.varsList es ∧ Env.lookup v σ = none
  | [], _, hv => by simp [Expr.freeVarsList] at hv
  | e :: es, v, hv => by
      rw [Expr.freeVarsList, List.mem_union_iff] at hv
      rw [Expr.varsList]
      rcases hv with hv | hv
      · exact ⟨List.mem_union_iff.mpr (Or.inl (Expr.mem_vars_of_mem_freeVars hv).1),
          (Expr.mem_vars_of_mem_freeVars hv).2⟩
      · exact ⟨List.mem_union_iff.mpr (Or.inr (Expr.mem_varsList_of_mem_freeVarsList hv).1),
          (Expr.mem_varsList_of_mem_freeVarsList hv).2⟩

end

@[inherit_doc Expr.mem_vars_of_mem_freeVars]
theorem Pattern.mem_vars_of_mem_freeVars {σ : Env} :
    ∀ {p : Pattern} {v : Var}, v ∈ p.freeVars σ → v ∈ p.vars ∧ Env.lookup v σ = none
  | .expr _, _, hv => Expr.mem_vars_of_mem_freeVars hv
  | .eq _ _, _, hv => by
      rw [Pattern.freeVars, List.mem_union_iff] at hv
      rw [Pattern.vars]
      rcases hv with hv | hv
      · exact ⟨List.mem_union_iff.mpr (Or.inl (Expr.mem_vars_of_mem_freeVars hv).1),
          (Expr.mem_vars_of_mem_freeVars hv).2⟩
      · exact ⟨List.mem_union_iff.mpr (Or.inr (Expr.mem_vars_of_mem_freeVars hv).1),
          (Expr.mem_vars_of_mem_freeVars hv).2⟩
  | .values _ _ _, _, hv => by
      rw [Pattern.freeVars, List.mem_union_iff] at hv
      rw [Pattern.vars]
      rcases hv with hv | hv
      · exact ⟨List.mem_union_iff.mpr (Or.inl (Expr.mem_varsList_of_mem_freeVarsList hv).1),
          (Expr.mem_varsList_of_mem_freeVarsList hv).2⟩
      · exact ⟨List.mem_union_iff.mpr (Or.inr (Expr.mem_varsList_of_mem_freeVarsList hv).1),
          (Expr.mem_varsList_of_mem_freeVarsList hv).2⟩

mutual

/-- **And an unbound variable is free.** -/
theorem Expr.mem_freeVars_of_mem_vars {σ : Env} :
    ∀ {e : Expr} {v : Var}, v ∈ e.vars → Env.lookup v σ = none → v ∈ e.freeVars σ
  | .lit _, _, hv, _ => by simp [Expr.vars] at hv
  | .var w, v, hv, hn => by
      obtain rfl : v = w := by simpa [Expr.vars] using hv
      rw [Expr.freeVars, hn]; simp
  | .app _ args, _, hv, hn => Expr.mem_freeVarsList_of_mem_varsList (by rwa [Expr.vars] at hv) hn

@[inherit_doc Expr.mem_freeVars_of_mem_vars]
theorem Expr.mem_freeVarsList_of_mem_varsList {σ : Env} :
    ∀ {es : List Expr} {v : Var}, v ∈ Expr.varsList es → Env.lookup v σ = none →
      v ∈ Expr.freeVarsList es σ
  | [], _, hv, _ => by simp [Expr.varsList] at hv
  | e :: es, _, hv, hn => by
      rw [Expr.varsList, List.mem_union_iff] at hv
      rw [Expr.freeVarsList, List.mem_union_iff]
      exact hv.imp (fun h => Expr.mem_freeVars_of_mem_vars h hn)
        (fun h => Expr.mem_freeVarsList_of_mem_varsList h hn)

end

@[inherit_doc Expr.mem_freeVars_of_mem_vars]
theorem Pattern.mem_freeVars_of_mem_vars {σ : Env} :
    ∀ {p : Pattern} {v : Var}, v ∈ p.vars → Env.lookup v σ = none → v ∈ p.freeVars σ
  | .expr _, _, hv, hn => Expr.mem_freeVars_of_mem_vars hv hn
  | .eq _ _, _, hv, hn => by
      rw [Pattern.vars, List.mem_union_iff] at hv
      rw [Pattern.freeVars, List.mem_union_iff]
      exact hv.imp (fun h => Expr.mem_freeVars_of_mem_vars h hn)
        (fun h => Expr.mem_freeVars_of_mem_vars h hn)
  | .values _ _ _, _, hv, hn => by
      rw [Pattern.vars, List.mem_union_iff] at hv
      rw [Pattern.freeVars, List.mem_union_iff]
      exact hv.imp (fun h => Expr.mem_freeVarsList_of_mem_varsList h hn)
        (fun h => Expr.mem_freeVarsList_of_mem_varsList h hn)

/-- **An answered atom binds every variable it mentions.** -/
theorem EncAtom.lookup_isSome {d : FDatabase} {ρ : Env} {a : Pattern} (h : EncAtom d ρ a)
    {v : Var} (hv : v ∈ a.vars) : (Env.lookup v ρ).isSome := by
  cases a with
  | expr _ => exact absurd h id
  | eq e₁ e₂ =>
      obtain ⟨i, h₁, h₂, -⟩ := h
      rw [Pattern.vars, List.mem_union_iff] at hv
      exact hv.elim (fun hx => Expr.lookup_isSome_of_mem_vars h₁ hx)
        (fun hx => Expr.lookup_isSome_of_mem_vars h₂ hx)
  | values vs f as =>
      obtain ⟨-, ts, us, hts, hus, -⟩ := h
      rw [Pattern.vars, List.mem_union_iff] at hv
      exact hv.elim (fun hx => Expr.lookup_isSome_of_mem_varsList hus hx)
        (fun hx => Expr.lookup_isSome_of_mem_varsList hts hx)

/-- **Restricting the substitution is invisible where the environment answers or the
restriction keeps.** The two cases of `Env.canon` under `d.env`: a variable the environment
binds is read off the environment either way, and one it does not is one the restriction
retains. -/
theorem lookup_canon_agree {d : FDatabase} {τ : Env} {vs : List Var} (hnd : vs.Nodup)
    {v : Var} (hv : Env.lookup v d.env = none → v ∈ vs) :
    Env.lookup v (d.env ++ Env.canon vs τ) = Env.lookup v (d.env ++ τ) := by
  cases hd : Env.lookup v d.env with
  | some t => rw [Env.lookup_append_of_some hd, Env.lookup_append_of_some hd]
  | none =>
      rw [Env.lookup_append_of_none hd, Env.lookup_append_of_none hd,
        Env.lookup_canon hnd (hv hd)]

/-- **The link at the substitution the enumerator offers.** What a rule head reads is
`Env.canon`-restricted, and this is `lookup_canon_agree` in the form the head consumes. -/
theorem lookup_canon_of_mem_freeVars {d : FDatabase} {q : Query} {τ : Env} {v : Var} {j : Term}
    (hv : (Env.lookup v d.env).isSome ∨ v ∈ Query.freeVars q d.env)
    (h : Env.lookup v (d.env ++ τ) = some j) :
    Env.lookup v (d.env ++ Env.canon (Query.freeVars q d.env) τ) = some j := by
  rw [lookup_canon_agree (Query.freeVars_nodup q d.env)
    (fun hd => hv.resolve_left (by rw [hd]; simp))]
  exact h

/-- **An answered atom is one `patternHolds` accepts.** A read is
`patternHolds_values_of_mem_rows` at the row's own columns; a comparison is the one id, whose
reflexive pair the target's own closure has because the target holds it. -/
theorem patternHolds_of_encAtom {d : FDatabase} {τ : Env} {a : Pattern}
    (hcv : d.RowColumnsValued) (h : EncAtom d (d.env ++ τ) a) :
    patternHolds d a (Env.canon (a.freeVars d.env) τ) = true := by
  have hagree : ∀ v ∈ a.vars, Env.lookup v (d.env ++ Env.canon (a.freeVars d.env) τ)
      = Env.lookup v (d.env ++ τ) := fun v hv =>
    lookup_canon_agree (Pattern.freeVars_nodup a d.env)
      (fun hd => Pattern.mem_freeVars_of_mem_vars hv hd)
  cases a with
  | expr _ => exact absurd h id
  | eq e₁ e₂ =>
      obtain ⟨i, h₁, h₂, hi⟩ := h
      have hv₁ : ∀ v ∈ e₁.vars, Env.lookup v (d.env ++ Env.canon _ τ)
          = Env.lookup v (d.env ++ τ) :=
        fun v hv => hagree v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inl hv))
      have hv₂ : ∀ v ∈ e₂.vars, Env.lookup v (d.env ++ Env.canon _ τ)
          = Env.lookup v (d.env ++ τ) :=
        fun v hv => hagree v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inr hv))
      have he₁ : Expr.eval d.sig e₁ (d.env ++ Env.canon ((Pattern.eq e₁ e₂).freeVars d.env) τ)
          = some i := by rw [Expr.eval_agreeOn e₁ hv₁]; exact h₁
      have he₂ : Expr.eval d.sig e₂ (d.env ++ Env.canon ((Pattern.eq e₁ e₂).freeVars d.env) τ)
          = some i := by rw [Expr.eval_agreeOn e₂ hv₂]; exact h₂
      have hmem : i ∈ ((d.addTerm i).addTerm i).terms := by
        simp only [FDatabase.mem_addTerm_terms]; exact Or.inr (Or.inr hi)
      have hcl : (i, i) ∈ ((d.addTerm i).addTerm i).closureF :=
        FDatabase.mem_closureF_iff.mpr (Cong.assert (Or.inl ⟨rfl, hmem⟩))
      simp only [patternHolds, he₁, he₂]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcl, decide_eq_true ⟨i, hi, hcl⟩⟩
  | values vs f as =>
      obtain ⟨hmg, ts, us, hts, hus, hrow⟩ := h
      have hva : ∀ v ∈ Expr.varsList as, Env.lookup v (d.env ++ Env.canon _ τ)
          = Env.lookup v (d.env ++ τ) :=
        fun v hv => hagree v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inr hv))
      have hvv : ∀ v ∈ Expr.varsList vs, Env.lookup v (d.env ++ Env.canon _ τ)
          = Env.lookup v (d.env ++ τ) :=
        fun v hv => hagree v (by rw [Pattern.vars]; exact List.mem_union_iff.mpr (Or.inl hv))
      refine patternHolds_values_of_mem_rows hmg ?_ ?_ hrow ?_
      · rw [Expr.evalList_agreeOn as hva]; exact hts
      · rw [Expr.evalList_agreeOn vs hvv]; exact hus
      · exact fun c hc => FDatabase.mem_terms_of_mem_valueTerms (hcv _ hrow c hc)

/-- **The forward mirror.** A source query read forward — one `PatternRowRead` per pattern —
is a substitution the **emitted** query matches at, with the target reading of every source
variable preserved.

The substitution is the source variables' reading in front of the generated bindings, and it is
consistent by construction: the generated ones are numbered per block and the source ones are
not `@`-prefixed, so neither family shadows the other (`atPrefix_freshVar`,
`FDatabase.NoAtEnv`, `hnoAtVar`).

`hglob` is the one thing the *environment* has to say: `matchQuery` reads `d.env ++ σ`, so a
source variable a global binds is read off the environment and not off the substitution, and
the reading has to agree with it there. `lookup_canon_of_mem_freeVars` moves the link onto the
restricted substitution a rule head runs at. -/
theorem mem_matchQuery_encodeQuery {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hcv : d.RowColumnsValued) (hnoat : d.NoAtEnv)
    (hnoAtVar : ∀ b ∈ ρt, ¬ "@".isPrefixOf b.1 = true)
    (hglob : ∀ (v : Var) (j t : Term), Env.lookup v ρt = some j →
      Env.lookup v d.env = some t → t = j)
    (hvt : ∀ (v : Var) (j : Term), Env.lookup v ρt = some j → j ∈ d.valueTerms)
    {q : Query} (hq : ∀ p ∈ q, PatternRowRead sig d ρs ρt p) (n : Nat) :
    ∃ τ : Env,
      Env.canon (Query.freeVars (encodeQuery q n).1 d.env) τ
        ∈ matchQuery d (encodeQuery q n).1 ∧
      ∀ (v : Var) (j : Term), Env.lookup v ρt = some j →
        Env.lookup v (d.env ++ τ) = some j := by
  obtain ⟨σ, hf, hp⟩ := exists_freshEnv_encodeQuery hcv hq n
  have hext : ∀ (v : Var) (j : Term), Env.lookup v ρt = some j →
      Env.lookup v (d.env ++ (ρt ++ σ)) = some j := by
    intro v j hj
    cases hd : Env.lookup v d.env with
    | some t =>
        obtain rfl : t = j := hglob v j t hj hd
        exact Env.lookup_append_of_some hd
    | none =>
        rw [Env.lookup_append_of_none hd]
        exact Env.lookup_append_of_some hj
  have hσρ : ∀ b ∈ σ, Env.lookup b.1 (d.env ++ (ρt ++ σ)) = some b.2 := by
    intro b hb
    obtain ⟨k, -, -, hk⟩ := hf.fresh b hb
    have hde : Env.lookup b.1 d.env = none :=
      hk ▸ lookup_env_eq_none hnoat (atPrefix_freshVar k)
    have hρt : Env.lookup b.1 ρt = none :=
      Env.lookup_eq_none_iff.mpr fun hc => by
        obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hc
        exact hnoAtVar (b.1, t) ht (hk ▸ atPrefix_freshVar k)
    rw [Env.lookup_append_of_none hde, Env.lookup_append_of_none hρt]
    exact Env.lookup_of_mem_nodup hb hf.nodup
  have hatoms := hp (d.env ++ (ρt ++ σ)) hσρ hext
  refine ⟨ρt ++ σ, mem_matchQuery_of_lookup (fun v hv => ?_) (fun v hv t ht => ?_)
    (fun a ha => patternHolds_of_encAtom hcv (hatoms a ha)), hext⟩
  · obtain ⟨a, ha, hva⟩ := Query.mem_freeVars.mp hv
    obtain ⟨hvars, hnone⟩ := Pattern.mem_vars_of_mem_freeVars hva
    have := (hatoms a ha).lookup_isSome hvars
    rwa [Env.lookup_append_of_none hnone] at this
  · rcases hlk : Env.lookup v ρt with _ | j
    · rw [Env.lookup_append_of_none hlk] at ht
      exact hf.valued (v, t) (Env.mem_of_lookup ht)
    · rw [Env.lookup_append_of_some hlk] at ht
      exact (Option.some.inj ht) ▸ hvt v j hlk

/-! #### The mirror, run at the instance

At `ncTgt` again, and at the source rule's own query: the source read `x := (B)` and the
target's reading of it is the id `(A)`, because `mergeResult` keeps `ordering-min` and the
`@FView` row sits at the leader. `RowRead.eval_src` is the source instance the reading carries
— `(F (B))`, the term the source's firing built — and `ncTgt_mirror` is the emitted query
matching at the substitution the mirror produces, which is `ncIdSubst`. -/

/-- The source signature `ncProgram` installs, as far as `Expr.eval` reads it. -/
def ncSrcSig : Signature := fun f =>
  if f = "F" then some { arity := 1, outArity := 1, merge := none }
  else if f = "A" ∨ f = "B" then some { arity := 0, outArity := 1, merge := none }
  else none

/-- The source rule's own substitution: the class member `(B)`. -/
def ncSrcSubst : Env := [("x", ncB)]

/-- Its target reading: the leader's id `(A)`, which is where the row is. -/
def ncTgtSubst : Env := [("x", ncA)]

theorem ncSrcSig_isCtor_F : ncSrcSig.IsCtor "F" := by decide

/-- **The reading, at the source rule's query expression.** -/
theorem ncTgt_rowRead :
    RowRead ncSrcSig ncTgt ncSrcSubst ncTgtSubst (.app "F" [.var "x"]) ncFB ncFA :=
  .app rfl ncSrcSig_isCtor_F (by decide) (.cons (.var rfl rfl) .nil) ncTgt_row_fview

/-- **And the source instance it carries is the term the source's firing built.** -/
theorem ncTgt_rowRead_src :
    Expr.eval ncSrcSig (.app "F" [.var "x"]) ncSrcSubst = some ncFB :=
  ncTgt_rowRead.eval_src

theorem ncTgt_patternRowRead : ∀ p ∈ ncRule.query,
    PatternRowRead ncSrcSig ncTgt ncSrcSubst ncTgtSubst p := by
  intro p hp
  obtain rfl : p = Pattern.expr (.app "F" [.var "x"]) := by simpa [ncRule] using hp
  exact .expr ncTgt_rowRead

theorem ncEncRule_query_eq : (encodeQuery ncRule.query 0).1 = ncEncRule.query := rfl

theorem ncTgt_noAtEnv : ncTgt.NoAtEnv := by
  intro b hb; rw [ncTgt_env] at hb; cases hb

theorem ncTgtSubst_noAt : ∀ b ∈ ncTgtSubst, ¬ "@".isPrefixOf b.1 = true := by
  intro b hb
  obtain rfl : b = ("x", ncA) := by simpa [ncTgtSubst] using hb
  exact (by decide +kernel : ¬ "@".isPrefixOf "x" = true)

theorem ncTgtSubst_glob : ∀ (v : Var) (j t : Term), Env.lookup v ncTgtSubst = some j →
    Env.lookup v ncTgt.env = some t → t = j := by
  intro v j t _ ht
  rw [ncTgt_env] at ht
  exact absurd ht (by simp [Env.lookup])

theorem ncTgtSubst_valued : ∀ (v : Var) (j : Term), Env.lookup v ncTgtSubst = some j →
    j ∈ ncTgt.valueTerms := by
  intro v j hj
  rw [ncTgtSubst, Env.lookup] at hj
  split at hj
  · obtain rfl : ncA = j := Option.some.inj hj
    decide
  · exact absurd hj (by simp [Env.lookup])

/-- **The mirror at the instance, non-vacuously**: the encoded query matches at a substitution
that binds the source rule's variable to the id its reading gave, and it is the one
`ncTgt_mem_matchQuery` exhibits by hand. -/
theorem ncTgt_mirror :
    ∃ τ : Env, Env.canon (Query.freeVars ncEncRule.query ncTgt.env) τ
        ∈ matchQuery ncTgt ncEncRule.query ∧
      Env.lookup "x" (ncTgt.env ++ τ) = some ncA := by
  obtain ⟨τ, hm, hx⟩ := mem_matchQuery_encodeQuery (sig := ncSrcSig) (ρs := ncSrcSubst)
    ncTgt_rowColumnsValued ncTgt_noAtEnv ncTgtSubst_noAt ncTgtSubst_glob ncTgtSubst_valued
    ncTgt_patternRowRead 0
  exact ⟨τ, ncEncRule_query_eq ▸ hm, hx "x" ncA rfl⟩

/-! #### The reading, along the source's congruence

`Matches` relates a pattern's instance to a witness in `src.withOperands` — so the instance
need not be a source term at all, and two patterns of one query can be satisfied by two
*congruent* instances that the emitted `.eq` atom then compares as ids. Both are answered by
one transport: the row reading is constant on a `CongOn` class, and so total on it as soon as
the class meets `sd.terms`.

Three cases carry it. `Cong.assert` is the only one with content, and it is where
`FDatabase.RowJoined` is spent: `Database.UnionsJoined` hands the two endpoints' *ids* and an
`@UF` edge between them, and `edge` turns that into one row reading for both, while `fn` pins
every other reading of either endpoint to it. `Cong.congr` is `rowReprList_congr` — a parent
read is keyed on its children's columns on the nose, so equal child readings give the same key
and hence the same row. `Cong.symm` and `Cong.trans` are the statement being an *iff*, which is
why it is stated that way rather than as a function.

`Conservativity.mem_addTerms_eqs` is what makes `withOperands` free: it adds reflexive pairs
and nothing else, so the operands contribute only the diagonal. -/

/-- The transport read in the other direction, pointwise on an argument list. -/
theorem forall₂_rowRepr_iff_symm {d : FDatabase} {as bs : List Term}
    (h : List.Forall₂ (fun a b => ∀ r : Term, RowRepr d a r ↔ RowRepr d b r) as bs) :
    List.Forall₂ (fun a b => ∀ r : Term, RowRepr d a r ↔ RowRepr d b r) bs as := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (fun r => (hh r).symm) ih

/-- **The row reading is constant on a source congruence class**, at a state an encoded block
runs at. This is the clause the emitted `.eq` atom needs — it compares ids, and at a target
that asserts nothing (`execM_encode_eqsRefl`) that comparison is *equality*. -/
theorem rowRepr_congOn {sd : Database} {td : FDatabase} (hjoin : td.RowJoined)
    (hunion : td.toDatabase.UnionsJoined sd) (hread : ∀ t ∈ sd.terms, ∃ r, RowRepr td t r)
    {ts : List Term} {a b : Term} (hab : CongOn sd ts a b) (r : Term) :
    RowRepr td a r ↔ RowRepr td b r := by
  revert r
  refine Cong.le (db := sd.withOperands ts)
    (R := fun x y => ∀ r : Term, RowRepr td x r ↔ RowRepr td y r) ?_
    (fun _ _ h r => (h r).symm) (fun _ _ _ h₁ h₂ r => (h₁ r).trans (h₂ r)) ?_ hab
  · intro x y hxy
    rcases Conservativity.mem_addTerms_eqs ts sd (x, y) hxy with hxy' | hxy'
    · by_cases hne : x = y
      · subst hne; exact fun _ => Iff.rfl
      · obtain ⟨e₁, e₂, pf, hv₁, hv₂, hedge⟩ := hunion x y hxy' hne
        obtain ⟨rx, hrx⟩ := hread x (eqsInTerms_free (Cong.assert hxy')).1
        obtain ⟨ry, hry⟩ := hread y (eqsInTerms_free (Cong.assert hxy')).2
        have hxy2 : rx = ry := by
          rcases hedge with ho | ho
          · exact hjoin.edge e₁ e₂ pf x y rx ry ho hv₁ hv₂ hrx hry
          · exact (hjoin.edge e₂ e₁ pf y x ry rx ho hv₂ hv₁ hry hrx).symm
        exact fun r => ⟨fun h => by rw [hjoin.fn x r rx h hrx, hxy2]; exact hry,
          fun h => by rw [hjoin.fn y r ry h hry, ← hxy2]; exact hrx⟩
    · obtain rfl : x = y := hxy'
      exact fun _ => Iff.rfl
  · intro f as bs _ _ hl r
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with
      | app hrl hrow => exact .app (rowReprList_congr hl hrl) hrow
    · cases h with
      | app hrl hrow => exact .app (rowReprList_congr (forall₂_rowRepr_iff_symm hl) hrl) hrow

/-- **And so the reading is total on the class of any source term**, which is the `CongUp` a
`Matches` witness needs: the instance need not be held, only congruent to something that is. -/
theorem exists_rowRepr_congOn {sd : Database} {td : FDatabase} (hjoin : td.RowJoined)
    (hunion : td.toDatabase.UnionsJoined sd) (hread : ∀ t ∈ sd.terms, ∃ r, RowRepr td t r)
    {ts : List Term} {w t : Term} (hw : w ∈ sd.terms) (hcong : CongOn sd ts w t) :
    ∃ r, RowRepr td t r := by
  obtain ⟨r, hr⟩ := hread w hw
  exact ⟨r, (rowRepr_congOn hjoin hunion hread hcong r).mp hr⟩

/-- **The `.eq` atom's own clause**: two congruent instances read to *one* id, which is the
equality the emitted comparison performs. Gap (2) of the residue below, discharged. -/
theorem rowRepr_eq_of_congOn {sd : Database} {td : FDatabase} (hjoin : td.RowJoined)
    (hunion : td.toDatabase.UnionsJoined sd) (hread : ∀ t ∈ sd.terms, ∃ r, RowRepr td t r)
    {ts : List Term} {a b r s : Term} (hab : CongOn sd ts a b)
    (hr : RowRepr td a r) (hs : RowRepr td b s) : r = s :=
  hjoin.fn b r s ((rowRepr_congOn hjoin hunion hread hab r).mp hr) hs

/-! #### And the reading, at an expression

`RowRead` is `RowRepr` re-indexed on the *shape of a pattern* rather than of a term, which is
what the emitted query's generated variables are numbered against. The two are the same reading
wherever the source's own evaluation produces the term: a source variable's id is whatever the
environment `ρt` gives it, a literal is its own id, and an application's id is the value column
of the row its children's ids key — which is exactly `RowRepr.app`.

`Prim.ofName f = none` and `Signature.IsCtor f` are read back off the source evaluation
itself: `Expr.eval` takes the primitive branch when the name is one, and returns `none` at a
name the signature does not make a constructor, so an application that evaluated at all
supplies both. The `:merge` carry is `FDatabase.IndexOk` at the row, one step of
`encStep_ctorsIn_of_row`. -/

/-- **An application that evaluated at a non-primitive name is a constructor application**,
which is the pair of side conditions `RowRead.app` carries. `Prim.ofName f = none` is a
hypothesis rather than a conclusion: at a primitive `Expr.eval` takes the other branch, and
`Prim.apply`'s `if-then-else` can return an arbitrary operand, so nothing about the *result*
rules the branch out. `Program.EncodeDomain.noPrim` is where a source query's names get it. -/
theorem eval_app_inv {sig : Signature} {f : FnName} {args : List Expr} {ρ : Env} {t : Term}
    (hp : Prim.ofName f = none) (h : Expr.eval sig (.app f args) ρ = some t) :
    sig.IsCtor f ∧ ∃ ts, Expr.evalList sig args ρ = some ts ∧ t = Term.app f ts := by
  rw [Expr.eval, hp] at h
  by_cases hc : sig.IsCtor f
  · rw [if_pos hc, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    exact ⟨hc, ts, hts, rfl⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

mutual

/-- **A row reading of an evaluated expression is a `RowRead` of it**, which is the residue's
own premise in the shape `mem_matchQuery_encodeQuery` consumes. -/
theorem rowRead_of_rowRepr {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hfn : ∀ t r s : Term, RowRepr d t r → RowRepr d t s → r = s)
    (hmg : ∀ (f : FnName) (es : List Term) (e pf : Term),
      (⟨viewName f, es, [e, pf]⟩ : Row) ∈ d.rows → (d.sig.mergeOf (viewName f)).isSome = true)
    (hvar : ∀ (v : Var) (t : Term), Env.lookup v ρs = some t →
      ∃ i, Env.lookup v ρt = some i ∧ RowRepr d t i) :
    ∀ (e : Expr), (∀ g ∈ Expr.fns e, Prim.ofName g = none) → ∀ {t r : Term},
      Expr.eval sig e ρs = some t → RowRepr d t r → RowRead sig d ρs ρt e t r
  | .lit l, _, t, r, hev, hr => by
      obtain rfl : t = Term.lit l := Option.some.inj hev.symm
      cases hr; exact .lit
  | .var v, _, t, r, hev, hr => by
      obtain ⟨i, hi, hri⟩ := hvar v t hev
      obtain rfl : i = r := hfn t i r hri hr
      exact .var hev hi
  | .app f args, hpr, t, r, hev, hr => by
      have hp : Prim.ofName f = none := hpr f (by rw [Expr.fns]; exact List.mem_cons_self)
      obtain ⟨hc, ts, hts, rfl⟩ := eval_app_inv hp hev
      cases hr with
      | app hl hrow =>
        exact .app hp hc (hmg _ _ _ _ hrow)
          (rowReadList_of_rowReprList hfn hmg hvar args
            (fun g hg => hpr g (by rw [Expr.fns]; exact List.mem_cons_of_mem _ hg)) hts hl) hrow

@[inherit_doc rowRead_of_rowRepr]
theorem rowReadList_of_rowReprList {sig : Signature} {d : FDatabase} {ρs ρt : Env}
    (hfn : ∀ t r s : Term, RowRepr d t r → RowRepr d t s → r = s)
    (hmg : ∀ (f : FnName) (es : List Term) (e pf : Term),
      (⟨viewName f, es, [e, pf]⟩ : Row) ∈ d.rows → (d.sig.mergeOf (viewName f)).isSome = true)
    (hvar : ∀ (v : Var) (t : Term), Env.lookup v ρs = some t →
      ∃ i, Env.lookup v ρt = some i ∧ RowRepr d t i) :
    ∀ (es : List Expr), (∀ g ∈ Expr.fnsList es, Prim.ofName g = none) →
      ∀ {ts rs : List Term}, Expr.evalList sig es ρs = some ts → RowReprList d ts rs →
        RowReadList sig d ρs ρt es ts rs
  | [], _, ts, rs, hev, hl => by
      obtain rfl : ts = [] := Option.some.inj hev.symm
      cases hl; exact .nil
  | e :: es, hpr, ts, rs, hev, hl => by
      rw [Expr.evalList, Option.bind_eq_some_iff] at hev
      obtain ⟨u, hu, hev'⟩ := hev
      rw [Option.map_eq_some_iff] at hev'
      obtain ⟨us, hus, rfl⟩ := hev'
      cases hl with
      | cons ha hrest =>
        refine .cons (rowRead_of_rowRepr hfn hmg hvar e (fun g hg => hpr g ?_) hu ha)
          (rowReadList_of_rowReprList hfn hmg hvar es (fun g hg => hpr g ?_) hus hrest)
        · rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inl hg)
        · rw [Expr.fnsList]; exact List.mem_union_iff.mpr (Or.inr hg)

end
/-! #### And the reading, at a pattern

`Matches` and `PatternRowRead` are the same statement read on the two sides: the source
relates a pattern's instance to a **witness** it holds, up to congruence, and the target wants
that instance read through live rows at one id per position. `exists_rowRepr_congOn` is the
step between them — the witness has a reading and the class is constant — and the `.eq` case
is where the two clauses of `FDatabase.RowJoined` are both spent, since the instance's two
sides are congruent and the emitted atom compares their ids.

What is still a hypothesis here is `hvar`: the target reading of the environment the source
evaluated in. For a variable the query's own substitution binds this is the reading of the
term it is bound to; for one a **global** binds, `matchQuery` reads the value off `d.env`, so
the reading has to be the value itself — which is `mem_matchQuery_encodeQuery`'s `hglob`, and
the one thing this assembly does not settle. -/

/-- Every function name a pattern applies. Not in `Spec/`: only the encoding's own domain
condition (`Program.EncodeDomain.noPrim`) reads it. -/
def Pattern.fns : Pattern → List FnName
  | .expr e => e.fns
  | .eq e₁ e₂ => e₁.fns ∪ e₂.fns
  | .values vs _ as => Expr.fnsList vs ∪ Expr.fnsList as

/-- **A source match is a target reading**, given the reading of the environment it evaluated
in. Gaps (1), (2) and (3) of the residue below at one pattern: the instance need not be a
source term (`exists_rowRepr_congOn`), a variable gets one id (`FDatabase.RowJoined.fn`,
through `rowRead_of_rowRepr`), and the `.eq` atom's two sides get the *same* id
(`rowRepr_congOn`). -/
theorem patternRowRead_of_matches {sd : Database} {td : FDatabase} {σ ρt : Env}
    (hjoin : td.RowJoined) (hunion : td.toDatabase.UnionsJoined sd)
    (hread : ∀ t ∈ sd.terms, ∃ r, RowRepr td t r)
    (hmg : ∀ (f : FnName) (es : List Term) (e pf : Term),
      (⟨viewName f, es, [e, pf]⟩ : Row) ∈ td.rows → (td.sig.mergeOf (viewName f)).isSome = true)
    (hidTerm : ∀ t r : Term, RowRepr td t r → r ∈ td.terms)
    (hvar : ∀ (v : Var) (t : Term), Env.lookup v (sd.env ++ σ) = some t →
      ∃ i, Env.lookup v ρt = some i ∧ RowRepr td t i)
    {p : Pattern} (hnv : p.NoValues) (hprim : ∀ g ∈ p.fns, Prim.ofName g = none)
    (hm : Matches sd p σ) : PatternRowRead sd.sig td (sd.env ++ σ) ρt p := by
  cases hm with
  | expr hw hev hcong =>
      obtain ⟨r, hr⟩ := exists_rowRepr_congOn hjoin hunion hread hw hcong
      exact .expr (rowRead_of_rowRepr hjoin.fn hmg hvar _ hprim hev hr)
  | eq hw hev₁ hev₂ hcw hc12 =>
      obtain ⟨r, hr₁⟩ := exists_rowRepr_congOn hjoin hunion hread hw hcw
      have hr₂ : RowRepr td _ r := (rowRepr_congOn hjoin hunion hread hc12 r).mp hr₁
      exact .eq
        (rowRead_of_rowRepr hjoin.fn hmg hvar _
          (fun g hg => hprim g (List.mem_union_iff.mpr (Or.inl hg))) hev₁ hr₁)
        (rowRead_of_rowRepr hjoin.fn hmg hvar _
          (fun g hg => hprim g (List.mem_union_iff.mpr (Or.inr hg))) hev₂ hr₂)
        (hidTerm _ r hr₁)
  | values _ _ _ _ => exact hnv.elim

/-! #### The head the target cannot run

`Egglog.UnionsFire` quantifies over an arbitrary `td` under ten hypotheses, and **not one of
them is about `td.sig`**. Step 5 of the assembly — the encoded rule's block *evaluating* — is
the one that reads the target's signature: `Expr.eval` returns `none` at a name the signature
does not make a constructor, `execLocalActions` propagates that `none`, and `fireInto` then
**silently keeps the accumulator**. So an encoded rule can match, be offered by the
enumerator, and write nothing at all — which is exactly the falsity
`mem_terms_of_ruleFired`/`mem_eqs_of_ruleFired` record on the source side, now on the target's.

The witness makes the two runs disagree in one command:

```
(constructor H)  (rule () ((H)) :ruleset r)  (run r)
```

The source rule has an **empty query**, so `ValidQuerySubst cxfSrc [] []` holds outright and
its head builds `(H)`. The encoded rule's query is empty too (`encodeQuery [] 0 = ([], 0)`), so
`matchQuery` offers the same empty substitution — one candidate, no rows read, no congruence
closure to compute. Its head is `encodeBuild (.app "H" []) 0`, two `set`s over the skolem
`(H)`; `cxfTgt.sig` is the encoder's own signature with that one skolem withdrawn, so the
first `set`'s operand does not evaluate, the firing is dropped, and the round writes nothing.
Every hypothesis holds — vacuously where the source state is empty, and by computation on the
target side — and the conclusion's `reads` clause fails at the term the source's own firing
built. The source program is **in `encode`'s domain**, all nine clauses
(`cxfProgram_encodeDomain`), so no narrowing of the source language reaches this.

**This is a refutation of the residue's statement, not of the encoding.** A real encoded target
declares the skolem: `encodePrelude` emits `.decl f (skolemDecl k)` for every `(f, k) ∈ P.ctors`
and `encodeSig` records it, so `FDatabase.EncBase`'s `sig` clause is what a state the run
reaches carries and `encReached_encBase` is where it comes from. What the residue lacks is a
*derived* clause saying so — the shape `Egglog.RowMech` already has, threaded through
`unionsInv_step` and discharged from `EncStep` in this file.

**And the signature is not the only such clause.** Three more are missing for the same reason,
each identified by following the assembly's own route rather than compiled here:

* `FDatabase.RowColumnsValued` at `td`. `mem_matchQuery_of_rows` and
  `mem_matchQuery_encodeQuery` both take it, and they need it: `matchQuery` draws candidate
  bindings from `FDatabase.valueTerms`, so a row whose e-class column is not a value term is a
  row no substitution can name and the encoded rule does not fire.
* `FDatabase.NoAtEnv` at `td`. `matchQuery` reads `d.env ++ σ`, and `Query.freeVars` drops a
  variable the environment already binds, so an `@`-prefixed binding in `td.env` reroutes a
  *generated* variable to the environment's value. `hnoAtVar` and `hglob` are the same clause
  read at the source rule's own variables.
* A source-side domain clause on `sd.rules`. `patternRowRead_of_matches` takes `Pattern.NoValues`
  and `∀ g ∈ p.fns, Prim.ofName g = none`, and the second is refuting on its own: a source query
  applying `min` evaluates through `Prim.apply`, while `encodeQueryExpr` emits a view read of
  `@minView` — a table `encodeSig` declares (`Program.ctors` reads query names) and nothing ever
  writes a row into. The source fires and the target cannot. `Program.EncodeDomain.noPrim` and
  `queryEncodable` are where a program pays for this (`cxpProgram_not_encodeDomain`), and
  `UnionsFire` never sees the program.

`Egglog.unionsFireClaim_false` is the same finding one round earlier, at the clauses' *state*
rather than at the target's signature. -/

/-- The rule the refutation fires: an **empty** query, so both the source's `ValidQuerySubst`
and the target's `matchQuery` are the empty substitution, and a head that builds `(H)`. -/
def cxfRule : Rule :=
  { query := [], actions := [Action.expr (.app "H" [])], ruleset := "r" }

/-- Its program: one nullary constructor, the rule, one round. In `encode`'s domain
(`cxfProgram_encodeDomain`). -/
def cxfProgram : Program :=
  [.decl "H" { arity := 0, outArity := 1, merge := none }, .rule cxfRule, .run "r"]

/-- The signature the declaration installs. -/
def cxfSrcSig : Signature :=
  fun f => if f = "H" then some { arity := 0, outArity := 1, merge := none } else none

/-- **And the program is in `encode`'s domain**, all nine clauses — so the missing fact is
target-side outright, and no narrowing of the source language reaches it. -/
theorem cxfProgram_encodeDomain : cxfProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc
    simp only [cxfProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | h
    · exact rfl
    · trivial
    · trivial
    · exact absurd h (by simp)
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [cxfProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | h
    · trivial
    · exact ⟨by simp [cxfRule], by intro v hv; exact absurd hv (by simp [cxfRule, Query.vars])⟩
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inl (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

/-- The source state the round runs at: the rule registered and nothing built. -/
def cxfSrc : Database := { Database.empty with sig := cxfSrcSig, rules := {cxfRule} }

/-- And what the round reaches. `MergeStep` is vacuous on `Database.CtorState`, so the
command's merge phase is the identity and this is `CmdStep`'s whole post-state. -/
def cxfSrc' : Database := RunRules "r" cxfSrc

/-- The encoded rule, at the counters a first rule gets. -/
def cxfEncRule : Rule := (encodeRule 0 (cxfRule.substGlobals []) 0).1

/-- **The target: the encoder's own signature with the head's skolem withdrawn**, and nothing
else. No terms, no rows — every clause `UnionsFire` asks about the data is then either vacuous
or decided — and the one encoded rule the `hrules` clause requires. -/
def cxfTgt : FDatabase :=
  { sig := fun f => if f = "H" then none else encodeSig cxfProgram f,
    terms := [], rows := [], eqs := [], env := [], rules := [cxfEncRule] }

theorem cxfSrc_terms : cxfSrc.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [cxfSrc, Database.empty] at hu

theorem cxfSrc_notMem (t : Term) : t ∉ cxfSrc.terms := by
  rw [cxfSrc_terms]; exact Set.notMem_empty t

theorem cxfSrc_ctorState : cxfSrc.CtorState where
  wf :=
    { eqsRefl := fun t ht => absurd ht (cxfSrc_notMem t)
      subtermClosed := fun t ht => absurd ht (cxfSrc_notMem t)
      envInTerms := by intro b hb; exact absurd hb (by simp [cxfSrc, Database.empty])
      litsIsolated := by intro p hp; exact absurd hp (by simp [cxfSrc, Database.empty]) }
  sig := by
    intro f
    change (cxfSrcSig f).bind FnDecl.merge = none
    rw [cxfSrcSig]
    by_cases h : f = "H" <;> simp [h]

/-- **The source round is a `CmdStep`.** -/
theorem cxfSrc_cmdStep : CmdStep cxfSrc (.run "r") cxfSrc' := ⟨cxfSrc', rfl, .refl⟩

/-- The state the source's own firing returns: `(H)` recorded and the environment restored. -/
def cxfFired : Database :=
  { cxfSrc.addTerm (.app "H" []) with env := cxfSrc.env, rules := cxfSrc.rules }

theorem cxfFired_eq : evalLocalActions cxfSrc cxfRule.actions [] = some cxfFired := rfl

theorem cxfFired_mem : Term.app "H" [] ∈ cxfFired.terms :=
  Database.mem_addTerm (Term.app "H" []) cxfSrc

/-- **And the term it built is one the round's post-state holds.** -/
theorem cxfSrc'_mem_H : Term.app "H" [] ∈ cxfSrc'.terms :=
  mem_terms_of_ruleFired (R := "r") (Or.inl rfl) cxfSrc_cmdStep (r := cxfRule) rfl rfl
    ⟨[], List.Forall₂.nil, Env.UnionAll.nil⟩ cxfFired_eq cxfFired_mem

set_option maxRecDepth 10000 in
/-- **The encoded block runs, and writes nothing.** The encoded rule matches at the empty
substitution — the query is empty, so there is one candidate and no row to read — and its head
is stuck at the withdrawn skolem, which `fireInto` answers by returning the accumulator. -/
theorem cxfTgt_execProgramM :
    cxfTgt.execProgramM [Cmd.run "r", Cmd.saturate rebuildRuleset] = some cxfTgt := rfl

/-- **No term of the target is a `@HView` entry**, so nothing reads `(H)`. -/
theorem cxfTgt_no_viewRepr (e : Term) : ¬ ViewRepr cxfTgt.toDatabase (Term.app "H" []) e := by
  intro h
  cases h with
  | app _ hout =>
    obtain ⟨bs, -, hmem⟩ := hout
    exact absurd (FDatabase.mem_toDatabase_terms.mp hmem) (by simp [cxfTgt])

theorem cxfTgt_rowJoined : cxfTgt.RowJoined where
  fn := fun _ _ _ h₁ h₂ =>
    rowRepr_unique (fun _ _ _ _ _ _ hr _ => absurd hr (by simp [cxfTgt])) h₁ h₂
  edge := fun _ _ _ _ _ _ _ hout _ _ _ _ => by
    obtain ⟨bs, -, hmem⟩ := hout
    exact absurd (FDatabase.mem_toDatabase_terms.mp hmem) (by simp [cxfTgt])

theorem cxfTgt_viewRepr_of_rowRepr {t r : Term} (h : RowRepr cxfTgt t r) :
    ViewRepr cxfTgt.toDatabase t r :=
  ViewRepr.of_rowRepr_of_rowTerms (fun _ hr => absurd hr (by simp [cxfTgt]))
    (fun _ hr => absurd hr (by simp [cxfTgt])) h

/-- **`Egglog.UnionsFire` is false.** Ten hypotheses, all of them satisfied, and the `reads`
half of the conclusion failing at `(H)` — the term the source's own firing built and the
target's could not, because nothing in the residue's statement makes the encoded head
evaluate.

Not a refutation of `encode`: the missing fact is `FDatabase.EncBase`'s `sig` clause, which
every state an encoded run reaches carries (`encReached_encBase`). It is a refutation of the
residue as stated, and `unionsJoined_fire`'s `sorry` therefore stands at a **false**
obligation until the clause — and the three the docstring above names beside it — are threaded
in as derived clauses, the way `Egglog.RowMech` is. -/
theorem unionsFire_false : ¬ UnionsFire := by
  intro h
  obtain ⟨-, hreads⟩ :=
    h (R := "r") (c := Cmd.run "r") (Or.inl rfl) cxfSrc_cmdStep cxfTgt_execProgramM rfl
      cxfSrc_ctorState
      (fun r hr => ⟨[], 0, 0, by
        rw [show r = cxfRule from hr]; exact List.mem_cons_self⟩)
      (fun t ht => absurd ht (cxfSrc_notMem t))
      (fun a b hab _ => absurd hab (by simp [cxfSrc, Database.empty]))
      (fun t ht => absurd ht (cxfSrc_notMem t))
      cxfTgt_rowJoined
      (fun _ _ hr => cxfTgt_viewRepr_of_rowRepr hr)
  obtain ⟨e, he⟩ := hreads _ cxfSrc'_mem_H
  exact cxfTgt_no_viewRepr e he

/-! #### And a second one, at the encoder's own signature

The clause the refutation above names is target-side and `FDatabase.EncBase` supplies it, so
the obvious repair is to thread `EncBase`. **That is not enough.** `UnionsFire` quantifies over
`sd` too, and it says nothing about the rules the source state holds — while
`patternRowRead_of_matches`, the assembly's own step 3, takes `Pattern.NoValues` and
`∀ g ∈ p.fns, Prim.ofName g = none` at every pattern of the source query.

The second clause is refuting on its own. `Expr.eval` consults `Prim.ofName` **first**, so a
source query applying `min` computes through `Prim.apply`; `encodeQueryExpr` has no primitive
case and emits a view read of `@minView`, a table nothing ever writes a row into — `encodeBuild`
builds no `min` application, because the source never builds one either. So the source rule
matches and the encoded rule has no row to read:

```
(constructor H)  (1)  (rule ((min x x)) ((H)) :ruleset r)  (run r)
```

`Program.EncodeDomain.noPrim` is where a program pays for this — `Program.ctors` reads a
query's names as well as a head's, so `("min", 2)` lands in the census and the clause rejects
the program — and `queryEncodable` is where `Pattern.NoValues` is paid. `UnionsFire` never sees
the program, so neither clause reaches it.

**The target here is unmodified.** `cxpTgt.sig` is `encodeSig cxpProgram` on the nose, so
`FDatabase.EncBase`'s signature clause holds at it and the refutation above's missing fact is
present. What is absent is a row: the source's one term is the **literal** `1`, which
`ViewRepr.lit` and `RowRepr.lit` read with no target row at all, so both data clauses hold at a
target whose row list is empty — and an empty row list is an empty `FDatabase.valueTerms`, at
which `assignments` offers the encoded query's three variables nothing. `matchQuery` is `[]`,
the round writes nothing, and `(H)` again has no id.

Two independent clauses, then, one on each side of the correspondence, and
`FDatabase.RowColumnsValued` and `FDatabase.NoAtEnv` are two more the assembly's own lemmas
take. -/

/-- The source term: a literal, which both readings answer with no row. -/
def cxpLit : Term := .lit (.int 1)

/-- The rule the second refutation fires: a query that applies a **primitive**. -/
def cxpRule : Rule :=
  { query := [.expr (.app "min" [.var "x", .var "x"])],
    actions := [Action.expr (.app "H" [])], ruleset := "r" }

/-- Its program. Not in `encode`'s domain — `cxpProgram_not_encodeDomain` names the clause it
fails — which is the point: `UnionsFire` is not given the domain. -/
def cxpProgram : Program :=
  [.decl "H" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.lit (.int 1))), .rule cxpRule, .run "r"]

/-- **And this one is not**, at the clause the refutation turns on: `Program.ctors` reads a
query's names, so `("min", 2)` is in the census and `noPrim` rejects it. -/
theorem cxpProgram_not_encodeDomain : ¬ cxpProgram.EncodeDomain := by
  intro h
  exact absurd (h.noPrim ("min", 2) (by decide)) (by decide)

/-- The source state: the literal built and the rule registered. -/
def cxpSrc : Database :=
  { Database.empty.addTerm cxpLit with sig := cxfSrcSig, rules := {cxpRule} }

/-- What the round reaches. -/
def cxpSrc' : Database := RunRules "r" cxpSrc

/-- **The target, at the encoder's own signature**: no terms, no rows, and the encoded rule. -/
def cxpTgt : FDatabase :=
  { sig := encodeSig cxpProgram, terms := [], rows := [], eqs := [], env := [],
    rules := [(encodeRule 0 (cxpRule.substGlobals []) 0).1] }

/-- Every equation the source state asserts is reflexive, and every term it holds is the
literal. -/
theorem cxpSrc_eqs {p : Term × Term} (hp : p ∈ cxpSrc.eqs) : p.1 = p.2 ∧ p.1 = cxpLit := by
  have hp' : p ∈ (Database.empty.addTerm cxpLit).eqs := hp
  rw [Database.addTerm] at hp'
  rcases hp' with hp'' | ⟨s, hs, rfl⟩
  · exact absurd hp'' (by simp [Database.empty])
  · exact ⟨rfl, by simpa [cxpLit] using hs⟩

theorem cxpSrc_terms {t : Term} (ht : t ∈ cxpSrc.terms) : t = cxpLit := by
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  rcases hu with hu' | hu'
  · exact (cxpSrc_eqs hu').2
  · exact ((cxpSrc_eqs hu').1).symm.trans ((cxpSrc_eqs hu').2)

theorem cxpSrc_mem_lit : cxpLit ∈ cxpSrc.terms :=
  Cong.assert (Or.inr ⟨cxpLit, Term.self_mem_subterms _, rfl⟩)

theorem cxpSrc_ctorState : cxpSrc.CtorState where
  wf :=
    { eqsRefl := by
        intro t ht
        obtain rfl := cxpSrc_terms ht
        exact Or.inr ⟨cxpLit, Term.self_mem_subterms _, rfl⟩
      subtermClosed := by
        intro t ht s hs
        obtain rfl := cxpSrc_terms ht
        rw [cxpLit, Term.subterms_lit] at hs
        exact hs ▸ cxpSrc_mem_lit
      envInTerms := by intro b hb; exact absurd hb (by simp [cxpSrc, Database.empty])
      litsIsolated := fun p hp _ => (cxpSrc_eqs hp).1 }
  sig := cxfSrc_ctorState.sig

theorem cxpSrc_cmdStep : CmdStep cxpSrc (.run "r") cxpSrc' := ⟨cxpSrc', rfl, .refl⟩

/-- The substitution the source's own firing runs at: the primitive's operand. -/
def cxpSubst : Env := [("x", cxpLit)]

/-- **The source rule matches**, through `Prim.apply` — `min 1 1` is the literal the state
holds, and it is its own witness. -/
theorem cxpSrc_validQuerySubst : ValidQuerySubst cxpSrc cxpRule.query cxpSubst :=
  ⟨[cxpSubst], List.Forall₂.cons
    ⟨⟨List.Perm.refl _, by
        intro b hb
        obtain rfl : b = ("x", cxpLit) := by simpa [cxpSubst] using hb
        exact cxpSrc_mem_lit⟩,
      .expr cxpSrc_mem_lit rfl (Database.mem_addTerms (by simp [cxpLit]))⟩
    List.Forall₂.nil, .single _⟩

/-- The state the source's firing returns. -/
def cxpFired : Database :=
  { ({ cxpSrc with env := cxpSrc.env ++ cxpSubst }).addTerm (.app "H" []) with
      env := cxpSrc.env, rules := cxpSrc.rules }

theorem cxpFired_eq : evalLocalActions cxpSrc cxpRule.actions cxpSubst = some cxpFired := rfl

theorem cxpFired_mem : Term.app "H" [] ∈ cxpFired.terms :=
  Cong.assert (Or.inr ⟨Term.app "H" [], Term.self_mem_subterms _, rfl⟩)

theorem cxpSrc'_mem_H : Term.app "H" [] ∈ cxpSrc'.terms :=
  mem_terms_of_ruleFired (R := "r") (Or.inl rfl) cxpSrc_cmdStep (r := cxpRule) rfl rfl
    cxpSrc_validQuerySubst cxpFired_eq cxpFired_mem

set_option maxRecDepth 10000 in
/-- **The encoded block runs, and writes nothing.** The emitted query reads `@minView` at three
generated variables, and `FDatabase.valueTerms` is empty, so `assignments` offers no candidate
at all. -/
theorem cxpTgt_execProgramM :
    cxpTgt.execProgramM [Cmd.run "r", Cmd.saturate rebuildRuleset] = some cxpTgt := rfl

theorem cxpTgt_no_viewRepr (e : Term) : ¬ ViewRepr cxpTgt.toDatabase (Term.app "H" []) e := by
  intro h
  cases h with
  | app _ hout =>
    obtain ⟨bs, -, hmem⟩ := hout
    exact absurd (FDatabase.mem_toDatabase_terms.mp hmem) (by simp [cxpTgt])

theorem cxpTgt_rowJoined : cxpTgt.RowJoined where
  fn := fun _ _ _ h₁ h₂ =>
    rowRepr_unique (fun _ _ _ _ _ _ hr _ => absurd hr (by simp [cxpTgt])) h₁ h₂
  edge := fun _ _ _ _ _ _ _ hout _ _ _ _ => by
    obtain ⟨bs, -, hmem⟩ := hout
    exact absurd (FDatabase.mem_toDatabase_terms.mp hmem) (by simp [cxpTgt])

theorem cxpTgt_viewRepr_of_rowRepr {t r : Term} (h : RowRepr cxpTgt t r) :
    ViewRepr cxpTgt.toDatabase t r :=
  ViewRepr.of_rowRepr_of_rowTerms (fun _ hr => absurd hr (by simp [cxpTgt]))
    (fun _ hr => absurd hr (by simp [cxpTgt])) h

/-- **`Egglog.UnionsFire` is false a second time, at a target the encoder's own signature and
provenance would supply.** So the repair is not one derived clause but at least two, on
opposite sides of the correspondence: the target's signature, which `FDatabase.EncBase` has,
and the source rules' encodability, which `Program.EncodeDomain.noPrim` and `queryEncodable`
have and which no target-side clause can reach. -/
theorem unionsFire_false_encodeSig : ¬ UnionsFire := by
  intro h
  obtain ⟨-, hreads⟩ :=
    h (R := "r") (c := Cmd.run "r") (Or.inl rfl) cxpSrc_cmdStep cxpTgt_execProgramM rfl
      cxpSrc_ctorState
      (fun r hr => ⟨[], 0, 0, by
        rw [show r = cxpRule from hr]; exact List.mem_cons_self⟩)
      (fun t ht => by obtain rfl := cxpSrc_terms ht; exact ⟨cxpLit, .lit⟩)
      (fun a b hab hne => absurd (((cxpSrc_eqs hab).1)) hne)
      (fun t ht => by obtain rfl := cxpSrc_terms ht; exact ⟨cxpLit, .lit⟩)
      cxpTgt_rowJoined
      (fun _ _ hr => cxpTgt_viewRepr_of_rowRepr hr)
  obtain ⟨e, he⟩ := hreads _ cxpSrc'_mem_H
  exact cxpTgt_no_viewRepr e he


/-- **The command induction's rule-firing case. REFUTED, twice, and no longer at `Cmd.saturate`.**

Its statement, its five closed siblings and the refutation that fixed its hypotheses are in
`Encoding/Correspond.lean` (`Egglog.UnionsFire`, `unionsInv_step`, `unionsFireClaim_false`).
What is recorded here is what the route through this file settles and what it does not.

**The route is the enumerator's own, and no general converse is wanted.**
`execRunRules_RunRules` needs `Signature.AllConstructors`, which an encoded target fails at
`@UF` and at every view, so the two matchers do not coincide here and a `Spec/Match.lean`-level
converse would not close this. It is also not needed. `mem_matchQuery_of_rows` is the enumerator
lower bound directly, over `mem_matchQuery_of_lookup` and `patternHolds_values_of_mem_rows`, and
it asks the closure for reflexive pairs only. `ncTgt_encRule_fires` is the whole chain — rows,
`patternHolds`, `matchQuery`, the block evaluating (`ncTgt_encRule_fired`), the head's row in
the round's post-state — run at a **source** rule's encoding, at the state where
`Database.ReadsSelf` is refuted (`ncTgt_not_readsSelf`) and `Database.UnionsJoined` holds
(`ncTgt_unionsJoined`). Proved, not decided: `closureF` does not reduce in the kernel.

**And the enumerator's under-firing is not the obstruction.** The specification fires once per
*member* of a premise's congruence class and the enumerator once per row; the substitution
wanted is the row's. In the target rule the source's own variables *are* id variables —
`encodeQueryExpr` returns a source variable unchanged as the expression naming its e-class — so
what the match wants is an id per source variable and the read's own two columns per generated
pair. `ncIdSubst` is that substitution at the instance: the source rule fired at `x := (B)` and
the encoded one at the id `(A)`, because `mergeResult` keeps `ordering-min` and the `@FView` row
sits at the leader.

**The `rows` reading is no longer missing.** `UnionsInv.readsAt` is a `terms` fact — `ViewRepr`
ends in `Database.Out` — while every atom above wants a live row, and `RowRepr` is that reading.
It is not the same claim at the same ids: `FDatabase.EntryRowsUF` (proved, `execM_entryRowsUF`)
answers an entry with a row whose e-class column is only `Database.UFReach`-reachable from the
entry's, and a parent read is keyed on its children's columns **on the nose** — there is no
slack, because an encoded target asserts nothing (`execM_encode_eqsRefl`) and so `patternHolds`'
congruence is the identity.

**It is the same claim at the pointwise `@UF` row root, and that was the choice of tuple.**
`encReached_viewRow_at_root` answers the entry with a live row whose e-class column *is* the
root of the id the entry recorded; `encReached_exists_rootList` names each key column's root;
and `encReached_viewRow_of_rowReachList` walks the whole key onto that rooted tuple in one go,
at the very e-class column the row started with. The child column is a root because it is the
*value* column of a live view row, which is the instance `FDatabase.ViewRowsRooted` supplies —
and the one an arbitrary reading does not, which is what made this a choice rather than a
lemma. `encReached_rowRepr_of_viewRepr` is the induction and `encStep_exists_rowRepr` the form
this residue is handed.

**Stated one block short of the run's end, which is where the firing happens.**
`execM_rebuildClosed` is the obvious supplier and does not typecheck here: it takes
`execM (encode P) = some tgt` and `UnionsFire` quantifies over the state the *next* encoded
block starts at. That is the hazard `unionsFireClaim_false` already recorded — a clause at a
state the encoded rule does not run at — so the mechanism was restated at the state that does
run it rather than the hypothesis being bent to reach it. `EncReached` is the target-side
provenance, one whole `encodeCmd` block at a time (whole, because `FDatabase.ViewRowsRooted` is
established by the `Cmd.saturate rebuildRuleset` a block ends with and is false in the middle of
one); `EncStep` is the same chain with the source run alongside, which is what pays the two
clauses `EncReached` does not carry — a literal's rootness (`encStep_ufLitRoots`) and a view
entry's key width (`encStep_ctorsIn`), both through `FDatabase.SoundTerms`. `encStep_rowMech`
is `RowMech` discharged, and `unionsInv_step` spends it.

**The provenance itself is not a hypothesis of `UnionsFire`, and must not become one.**
`unionsJoined_fire_satisfiable` exhibits the hypotheses at `rbState2`, a state written by
`execActions` rather than by `encode`, and the kernel cannot run an encoded program — so
`EncReached rbProgram rbState2` is not available and an `EncReached` hypothesis would empty the
non-vacuity check. What `UnionsFire` takes is therefore the two *derived* clauses, `RowRepr`
at `td` and the read-back at `td'`, both of which the witness state really satisfies
(`rbState2_exists_rowRepr`, `rbState2_viewRepr_of_rowRepr`) and at positive arity.

**The forward query mirror is written.** `mem_matchQuery_encodeQuery` turns a source reading of
a query — one `PatternRowRead` per pattern — into a substitution the *emitted* query matches at,
over both features of `encodeQuery`. The **flattening**: `RowRead` carries an id per subterm
position through live rows, so the reading binds the generated variables as well as the
source's. The **fresh-variable supply**: `FreshEnv` numbers a block's generated bindings inside
its own stretch of the counter, so two blocks' domains are disjoint (`freshVar_inj`) and their
concatenation binds each of them; non-collision with the source's own variables is the `@`
prefix (`atPrefix_freshVar` against `FDatabase.NoAtEnv`), which is why the source bindings can
sit in front of the generated ones and neither shadow the other. `ncTgt_mirror` runs it at the
instance, and lands on the substitution `ncTgt_mem_matchQuery` exhibits by hand.

**The reading is written, and the three things it wanted are a derived clause.**
`FDatabase.RowJoined` is that clause — `fn`, the reading is a function; `edge`, an `@UF` edge
between two entry readings collapses the two row readings — threaded through `RowMech` and
`unionsInv_step` and discharged at `EncStep` by `encStep_rowJoined`, in the shape `RowMech`
already had and not as provenance, which would have emptied `unionsJoined_fire_satisfiable`.
It answers all three:

* **One id per source term** is `fn`, off `FDatabase.ViewRowUnique` (`encReached_viewRowUnique`)
  and a parent read being keyed on its children's columns on the nose (`rowRepr_unique`).
* **One id per congruence class** is `rowRepr_congOn`: the reading is constant on a `CongOn`
  class, by induction over `Cong` with `Database.UnionsJoined`'s edge between the two *ids*
  turned into one reading by `edge`, `rowReprList_congr` at `Cong.congr`, and
  `Conservativity.mem_addTerms_eqs` making `withOperands` contribute only the diagonal.
* **The pattern instance, not only a source term** is `exists_rowRepr_congOn`: the reading is
  total on the class of any source term, so a `Matches` witness carries its instance.

`patternRowRead_of_matches` is the three assembled at one pattern, over `rowRead_of_rowRepr`,
which is `RowRepr` re-indexed on the shape of the pattern. `Prim.ofName f = none` is a
hypothesis there and not a conclusion — `Prim.apply`'s `if-then-else` returns an operand, so
nothing about an evaluation's *result* rules the primitive branch out — and
`EncodeDomain.noPrim` is where a source query's names pay it.

**`Database.ViewLeader` is not what closed it, and could not have been.** It is the same claim
through entry **terms**, and it is false in general at states this development reaches
(`chainD_not_viewLeader`): an entry a merge displaced is never removed, so `Database.Out` keeps
reading it, and at `chainD` the ids ascend with upper bounds everywhere and no top. Through
live **rows** the displaced row is *gone*, and a state an encoded block runs at is rooted — a
live view row's e-class column has no outgoing `@UF` row (`encReached_viewRowsRooted`), a view
key carries at most one row, and entry-level `@UF` reachability lands on one row root
(`encReached_ufRowRoot_of_ufReach`). So the upper bound is a representative here and is not one
there; `uTgt_not_viewLeader` against `uRebuilt_viewLeader` is the same bracket one rebuild
firing apart, and `ncTgt_rowJoined_edge` is the instance: `(B)` reads to `(B)` and to `(A)`
through entries, to `(A)` alone through rows.

**What the reading owed was `hglob`, and the encoder is what paid it.** `matchQuery` reads a
variable a *global* binds off `d.env`, so `mem_matchQuery_encodeQuery` asks the target reading
of such a variable to be the bound value itself — `RowRepr td s s`, where
`UnionsInv.envReadsAt` supplies only `ViewRepr td s s`. The two part company exactly when a
later `union` moves the let-bound term's row off it: `mergeResult` keeps `ordering-min`, so
`(let x (A))` followed by a `union` with a `Term.blt`-smaller partner leaves `x` bound to a term
no live row is keyed at. That was a **defect in `encode`**, and it was measured:
`DiffTest.lean`'s eight `glob-*` cases are all in `encode`'s domain and all pass against real
egglog, and `difftest correspond 64` reported **7 LOST across 6 of them** where the whole corpus
reported 0. `glob-lost` is the minimal one, five commands:

```
(let $g (Zz))  (Wrapper (Aa))  (union (Zz) (Aa))  (rule ((Wrapper $g)) ((Hit)))  (run 1)
```

`Term.blt` orders applications by arity, then by name, so `(Aa)` is the `ordering-min` and
`(Zz)` is the union's loser. The source fires: `patternHolds` closes the instance
`(Wrapper (Zz))` into `d`'s congruence and finds `(Wrapper (Aa))`, which is what egglog does
too. The target could not: its one `@WrapperView` row was `((Aa)) ↦ (Wrapper (Aa))`, the
emitted atom was `(= (values @v0 @v1) (@WrapperView $g))` at a frozen `$g = (Zz)`, and
`rebuildRules`' column rule joins `@UF[@ci] ↦ (@x, @q)` and writes `@x` *into* the column, so
rows travel **towards** a leader and never back from one. `glob-keyed` and `glob-leader` were
the two controls that agreed throughout — a global whose key a build did write, and a global
bound to the union's *winner*.

**The fix is `Rule.substGlobals`**, and it is what egglog does by another route: a query that
names a global is encoded as if the source had written the global's *definition* out, so the
flattening reads the definition's own views and lands on its **current** e-class exactly as an
ordinary query does. egglog gets the same effect from a per-global table — `remove_globals`
desugars `(let $g e)` into a nullary function plus `(set ($g) e)` and rewrites a rule that reads
`$g` into one that joins on `($g)` — and under `--proofs` that table's value follows the
union-find forward (`proof_encoding.rs`'s `is_encoded_global`,
`proof_encoding_rebuild.rs:91-94`). Reading the definition instead reaches the same class
through the tables the `let`'s own build already wrote. `difftest correspond 64` now reports
**0 LOST**, with all eight `glob-*` cases agreeing.

So `hglob` is no longer the obstruction it was. What the residue would still have to prove at a
`Cmd.run` is `UnionsFire` itself: the rule the target holds is `encodeRule i (s.substGlobals G) n`
— `UnionsInv.rules` now says so — so the reading a firing has to mirror is the *substituted*
query's, `mem_matchQuery_encodeQuery` at `Query.substGlobals G s.query`, whose globals are
already flattened away and whose remaining variables the three clauses above answer for.

**`UnionsFire` was false, and the writer was `Cmd.saturate`.** `encodeCmd` gave a source
`.saturate R` the block `[.saturate R, .saturate rebuildRuleset]`, so the rebuild ran **once,
after the whole saturation**, and the target's second round of `R` read the first round's rows
un-re-keyed. The specification has no rebuild to miss — `Matches` closes over `Cong`, which
reads `eqs` — so its round 2 saw round 1's `union` and the target's did not. Five commands, all
of them in `encode`'s domain, and `DiffTest.lean`'s `sat-hit`:

```
(Wrapper (Zz))  (Aa)
(rule ((Aa)) ((union (Zz) (Aa))))
(rule ((Wrapper (Aa))) ((Hit)))
(run-schedule (saturate (run)))
```

Round 1 fires the first rule on both sides; round 2 fires the second on the source alone, over
the congruence `(Zz) = (Aa)` round 1 asserted, and builds `(Hit)`. In the target the union is an
`@UF` edge — `Term.blt` makes `(Aa)` the `ordering-min` — while `@WrapperView` still sat at the
key `[(Zz)]`, and the emitted atom for `(Wrapper (Aa))` asks for the key `[(Aa)]`. Nothing
joined them until the trailing `Cmd.saturate rebuildRuleset`, which is after `R` has saturated.
**Measured**: `exec P` held one `Hit` term and `execM (encode P)` held **no** `@HitView` entry
term at all, where the same program with the `saturate` replaced by two `Cmd.run`s **agreed** —
each round getting its own rebuild is what made the `run` form right. So
`encode_corresponds_forward` was false there too, at `a = b = (Hit)`, and this `sorry` was a
false obligation rather than an open one.

**The repair is in `Encoding/Encode.lean`, and it is what egglog does.** egglog instruments a
schedule node at a time: its `Run` case becomes `(seq <run> <rebuild>)`
(`egglog/src/proofs/proof_encoding.rs:1969`) and its `Saturate` case recurses *into* the loop
body (`:1978-1980`), so `(run-schedule (saturate R))` is instrumented to
`(saturate (seq (run R) <rebuild>))` — a rebuild after **every** iteration, which
`RUST_LOG=debug` prints as the schedule the loop runs. `Cmd` has no schedule nesting, so
`allMaintenanceRules` joins the maintenance rules to each ruleset a source `Cmd.saturate` names
as well as to `rebuildRuleset`; a round of `R` then re-keys the views the previous round moved,
and a fixpoint of the union of the two rulesets is a fixpoint of each. `sat-hit` now agrees —
one source `Hit`, one target `@HitView` — as do the four other `sat-*` cases, and
`difftest correspond 64` reports 0 LOST over 83 in-domain cases. **That writer is fixed, and the
obligation is false anyway** — for two reasons that have nothing to do with `Cmd.saturate` and
that the `Cmd.run` half fails at too: `unionsFire_false` and `unionsFire_false_encodeSig` above.

**What the corpus used to miss.** No case used a *source* `Cmd.saturate`: the only
`Cmd.saturate` in an encoded program was the encoder's own `rebuildRuleset` one, every curated
case ran its ruleset with `Cmd.run`, and both generators emitted
`List.replicate (rounds + 1) (Cmd.run "")`. `difftest correspond 64` agreeing on all 78
in-domain cases therefore measured the `Cmd.run` half and said nothing about the other. The
`sat-*` family and `genProgram`'s `genCollapseRules` tail are what close that: five curated
cases and, at the default 60 seeds, ten generated ones now run a source `saturate`, and with
the repair backed out the sweep reports 13 LOST across those 13 cases.

**That refutation was measured and not proved**, which is why no `unionsFire_false` ever stood
beside `unionsFireClaim_false`, and why the corpus is where the repair is checked. Refuting a
firing needs the enumerator's *completeness* at an encoded target — no substitution matches, so
nothing is written — and that is `execRunRules_RunRules`, which wants
`Signature.AllConstructors` and is unavailable at a target whose `@UF` and every `@fView` carry
`:merge`. The kernel cannot run the encoded program either.

**A valid substitution is still not a firing, and that is what refutes this.** `RuleResults` is
a substitution *and* a block that evaluates, which is the falsity
`mem_terms_of_ruleFired`/`mem_eqs_of_ruleFired` already cost once. `ncTgt_encRule_fired` is that
half exhibited on the target side, and `mem_rows_execRunRules` is where the head's writes are
read back. On the target the same gap is a *hole in this statement*: `Expr.eval` returns `none`
at a name the signature does not make a constructor, `execLocalActions` propagates it, and
`fireInto` answers a stuck firing by returning the accumulator unchanged — so `unionsFire_false`
runs the encoded rule at a `td` whose signature withholds the head's skolem and the round writes
nothing. `unionsFire_false_encodeSig` is the same conclusion at `encodeSig` itself, over a
source query that applies a primitive, so the second missing clause is on the **source** side
and no target-side provenance reaches it.

**What the repair is.** Four derived clauses, à la carte and threaded the way `Egglog.RowMech`
is — never as provenance, which `unionsJoined_fire_satisfiable` would not survive:

* the target's signature, in the form `∀ f, sd.sig.IsCtor f → td.sig.IsCtor f`,
  `td.sig.IsCtor fiatName`, and `td.sig.IsCtor (ruleName i)` at the index `hrules` names —
  `FDatabase.EncBase`'s `sig` clause and `encodeSig_isCtor_*` are where an encoded run has them
  (`encReached_encBase`), and each is decidable at `rbState2`;
* `FDatabase.RowColumnsValued` at `td`, which `mem_matchQuery_of_rows` and
  `mem_matchQuery_encodeQuery` both take: `matchQuery` draws its candidates from
  `FDatabase.valueTerms`, so a row column outside it is a row no substitution can name;
* `FDatabase.NoAtEnv` at `td`, with `hnoAtVar` and `hglob` at the source rule's own variables:
  `Query.freeVars` drops a variable the environment binds, so an `@`-prefixed binding reroutes
  a *generated* variable to the environment's value;
* the source rules' encodability — `Pattern.NoValues` and `∀ g ∈ p.fns, Prim.ofName g = none` at
  every pattern of every rule `sd.rules` holds, which `patternRowRead_of_matches` takes and
  which `Program.EncodeDomain.queryEncodable` and `noPrim` pay for at the program. This one
  wants a **source-run** invariant, since `UnionsFire` is given no program.

The `Cmd.saturate` half wants one thing more, and it is structural rather than a clause: the
source's rounds and the target's do not align, and the row clauses this residue is handed live
at `td` alone. The target's `.saturate R` fixpoint is where they would have to be re-established
— it is the only state in the block that is rebuild-closed, since a round fires the maintenance
rules against its own pre-state — and `FDatabase.ViewRowUnique` is established by a trailing
`Cmd.saturate rebuildRuleset` and by nothing in the middle of a block. -/
theorem unionsJoined_fire : UnionsFire := by
  sorry

/-! ## `Database.RebuildClosed`'s two remaining clauses, at the root tuple

The walk delivers a live view row at the pointwise-**root** key tuple, because
`FDatabase.UFRowReach` is what a firing can read; `edged` and `column` are stated over
`Database.Lands`, whose reachability half is `Database.UFReach`, over `@UF` **entries**, and
`execM_ufRowRoot_of_ufReach` identifies the two only at their *roots*. So `column`, quantified
over every landing site, owed that an arbitrary one of a live key column is itself an `@UF` row
root — which `Database.Absorbs` does not supply, since `Database.Out` reads entry terms and
those are never removed.

`Database.LandsRoot` is that obligation moved into the clause, where the walk pays it outright:
`column` is asked only at rooted tuples and `edged` delivers one, which is what keeps
`Database.RebuildClosed.reach_of_forall₂` — the only producer of `column`'s tuple — coherent.
`Database.RebuildClosed.of_strong` records the unrooted clause set as the trivial instance, and
`Database.RebuildClosed.of_strong_ufRoot` is the rooted reading of the same weakening. -/

/-- **A view entry term names a source constructor**, at the entry's own key width. The
*declaration* half is `execM_viewDecl_of_mem_terms`; this is the `Program.ctors` membership
itself, which is what every rebuild-rule firing lemma is keyed on. Same chain, same source
run: `execM_soundTerms` for the source application and `ctorsIn_of_programStep` for the
program that makes it. -/
theorem execM_ctorsIn_of_mem_terms {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {f : FnName} {es : List Term} {e pf : Term}
    (hmem : Term.app (viewName f) (es ++ [e, pf]) ∈ tgt.terms) : (f, es.length) ∈ P.ctors := by
  obtain ⟨as, hasrc, hcl, -⟩ := (execM_soundTerms hdom hsrc htgt).1 f es e pf hmem
  rw [← hcl.length_eq]
  exact ctorsIn_of_programStep hdom hsrc f as hasrc

/-- **A live view row is an entry the denotation reads, at the key it sits at.**
`mem_terms_of_indexOk` is the row's own entry term and `FDatabase.EqsRefl` makes `Database.Out`
read it on the nose. This is the direction the bridge does not go: `execM_entryRow_of_out`
answers an entry with a row only up to the union-find, and that asymmetry is why
`Database.Lands` is stated over entries at all. -/
theorem execM_out_of_viewRow {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors)
    {as : List Term} {e pf : Term} (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ tgt.rows) :
    tgt.toDatabase.Out (viewName f) as [e, pf] := by
  have hb : tgt.EncBase P (encodeSig P) := execM_encode_encBase hdom hdom.aritiesAgree' htgt
  have hcv : tgt.RowColumnsValued := execM_rowColumnsValued hdom htgt
  have hmgne : tgt.sig.mergeOf (viewName f) ≠ none := by
    rw [Signature.mergeOf, hb.sig, (encodeSig_tables hdom hdom.aritiesAgree' hfk).1,
      Option.bind_some]
    simp [viewDecl]
  refine ⟨as, CongList.refl (fun a ha => ?_), ?_⟩
  · rw [FDatabase.toDatabase_terms]
    exact FDatabase.mem_terms_of_mem_valueTerms (hcv _ hrow a (List.mem_append_left _ ha))
  · rw [FDatabase.toDatabase_terms]
    exact mem_terms_of_indexOk (execM_encode_eqsRefl htgt) hb.inv.index hrow hmgne

/-- **The bridge's answer is the root itself.** The row the bridge produces for a view entry has
an e-class column that `execM_viewRowsRooted` makes an `@UF` row root and
`execM_ufRowRoot_of_ufReach` identifies with the root of the id the entry recorded. So a reader
of an id is answered by a live row *at the root*, which is what both remaining clauses spend. -/
theorem execM_viewRow_at_root {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (htgt : execM (encode P) = some tgt) {f : FnName} {es : List Term} {x px r : Term}
    (ho : tgt.toDatabase.Out (viewName f) es [x, px])
    (hr : tgt.UFRowReach x r) (hrr : tgt.UFRowRoot r) :
    ∃ lo, (f, es.length) ∈ P.ctors ∧ (⟨viewName f, es, [r, lo]⟩ : Row) ∈ tgt.rows := by
  have hb : tgt.EncBase P (encodeSig P) := execM_encode_encBase hdom hdom.aritiesAgree' htgt
  have hmem : Term.app (viewName f) (es ++ [x, px]) ∈ tgt.terms := by
    obtain ⟨bs, hcl, hm⟩ := ho
    obtain rfl : es = bs := CongList.eq_of_eqsRefl (execM_encode_eqsRefl htgt).toDatabase hcl
    rw [FDatabase.toDatabase_terms] at hm
    exact hm
  have hfk : (f, es.length) ∈ P.ctors := execM_ctorsIn_of_mem_terms hdom hsrc htgt hmem
  obtain ⟨v, lo, hrow, hreach⟩ :=
    execM_entryRow_of_out hdom htgt (dc := viewDecl es.length)
      (by rw [hb.sig]; exact (encodeSig_tables hdom hdom.aritiesAgree' hfk).1)
      (body := mergeBody) (res := mergeResult) rfl rfl ho
  have hvroot : tgt.UFRowRoot v :=
    execM_viewRowsRooted hdom hsy htr htgt f es.length hfk es v lo hrow
  have heq : r = v :=
    execM_ufRowRoot_of_ufReach hdom hsy htr htgt hreach r v hr hrr .refl hvroot
  rw [← heq] at hrow
  exact ⟨lo, hfk, hrow⟩

/-- **Pointwise `@UF` row roots of a tuple**, which is the tuple the walk is pointed at. -/
theorem execM_exists_rootList {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : ∀ (es : List Term),
      ∃ rs, List.Forall₂ (fun a r => tgt.UFRowReach a r ∧ tgt.UFRowRoot r) es rs
  | [] => ⟨[], .nil⟩
  | a :: as => by
      obtain ⟨r, hr, hrr⟩ := execM_exists_ufRowRoot hdom htgt a
      obtain ⟨rs, hrs⟩ := execM_exists_rootList hdom htgt as
      exact ⟨r :: rs, .cons ⟨hr, hrr⟩ hrs⟩

/-- The walk's two hypotheses, read off such a tuple. -/
theorem rootList_reach {tgt : FDatabase} {es rs : List Term}
    (h : List.Forall₂ (fun a r => tgt.UFRowReach a r ∧ tgt.UFRowRoot r) es rs) :
    ∀ (j : Nat) (hj : j < es.length) (hj' : j < rs.length), tgt.UFRowReach (es[j]) (rs[j]) :=
  fun j hj hj' => by simpa using (h.get hj hj').1

/-- **The `column` clause at the state `execM` returned, and the restatement is exactly what
closes it.**

The bridge answers the entry with a live row at its own key; each key column reaches its rooted
landing site along live `@UF` **rows**, because `execM_ufRowRoot_of_ufReach` identifies entry
reachability with row reachability at the root and the clause now says the target *is* one; and
`execM_viewRow_of_rowReachList` moves the whole key onto it in one go, at the very e-class
column the row started with. `execM_out_of_viewRow` reads the moved row back as an entry.

Nothing here asks that a key column be a root — it is not one, and a view row at a superseded
key survives forever. What is asked is that the *destination* be one, which is what rows moving
only toward roots makes necessary and what the clause now supplies. -/
theorem execM_rebuildColumn {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 →
      (encodeSig P).IsCtor (congrName k))
    (htgt : execM (encode P) = some tgt) {f : FnName} {es ds : List Term} {e pf : Term}
    (ho : tgt.toDatabase.Out (viewName f) es [e, pf])
    (hl : List.Forall₂ (tgt.toDatabase.LandsRoot tgt.UFRowRoot) es ds) :
    ∃ e' pf', tgt.toDatabase.Out (viewName f) ds [e', pf'] := by
  obtain ⟨r, hr, hrr⟩ := execM_exists_ufRowRoot hdom htgt e
  obtain ⟨lo, hfk, hrow⟩ := execM_viewRow_at_root hdom hsrc hsy htr htgt ho hr hrr
  have hj : ∀ (j : Nat) (hj : j < es.length) (hj' : j < ds.length),
      tgt.UFRowReach (es[j]) (ds[j]) := by
    intro j hj hj'
    have hlr : tgt.toDatabase.LandsRoot tgt.UFRowRoot (es[j]) (ds[j]) := by
      simpa using hl.get hj hj'
    obtain ⟨s, hs, hsr⟩ := execM_exists_ufRowRoot hdom htgt (es[j])
    have heq : s = ds[j] :=
      execM_ufRowRoot_of_ufReach hdom hsy htr htgt hlr.1.1 s (ds[j]) hs hsr .refl hlr.2
    exact heq ▸ hs
  obtain ⟨pf', hrow'⟩ :=
    execM_viewRow_of_rowReachList hdom htr hsy hfi hcg htgt hfk hrow hl.length_eq.symm hj
  exact ⟨r, pf', execM_out_of_viewRow hdom htgt hfk hrow'⟩

mutual
/-- **Two readings of one source term have one `@UF` row root**, which is the whole of `edged`
once the landing site is the root.

Induction on the reading. At a **literal** both readings are the literal itself
(`ViewRepr.eq_of_lit`) and `execM_ufRowRoot_unique` closes it. At an **application** the two
readings sit at two id tuples that agree rootwise by the list case, so
`execM_viewRow_of_rowReachList` moves *both* rows onto that common root tuple — with the e-class
column unmoved, which is what `execM_columnRow_step` bought — and `execM_viewRowUnique`
identifies the two rows there. `execM_viewRow_at_root` is what says each row's e-class column
*is* the root of the id its entry recorded.

This is the run-wide merge-fixpoint carry's only consumer, and the reason it is wanted: without
row-uniqueness the two walks land at one key and say nothing about each other. -/
theorem execM_rootAgree {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 →
      (encodeSig P).IsCtor (congrName k))
    (htgt : execM (encode P) = some tgt) (huq : tgt.ViewRowUnique P) :
    ∀ {t e₁ : Term}, ViewRepr tgt.toDatabase t e₁ → ∀ {e₂ r₁ r₂ : Term},
      ViewRepr tgt.toDatabase t e₂ → tgt.UFRowReach e₁ r₁ → tgt.UFRowRoot r₁ →
        tgt.UFRowReach e₂ r₂ → tgt.UFRowRoot r₂ → r₁ = r₂
  | _, _, @ViewRepr.lit _ l, _, r₁, r₂, h₂, k₁, k₁', k₂, k₂' => by
      obtain rfl := h₂.eq_of_lit
      obtain ⟨_, -, -, huniq⟩ := execM_ufRowRoot_unique hdom hsy htr htgt (Term.lit l)
      rw [huniq r₁ k₁ k₁', huniq r₂ k₂ k₂']
  | _, _, @ViewRepr.app _ f as es₁ _ pf₁ hl₁ ho₁, _, r₁, r₂, h₂, k₁, k₁', k₂, k₂' => by
      cases h₂ with
      | app hl₂ ho₂ =>
        obtain ⟨lo₁, hfk₁, hrow₁⟩ := execM_viewRow_at_root hdom hsrc hsy htr htgt ho₁ k₁ k₁'
        obtain ⟨lo₂, hfk₂, hrow₂⟩ := execM_viewRow_at_root hdom hsrc hsy htr htgt ho₂ k₂ k₂'
        obtain ⟨rs, hrs₁⟩ := execM_exists_rootList hdom htgt es₁
        obtain ⟨rs', hrs₂⟩ := execM_exists_rootList hdom htgt _
        have hsame : rs = rs' :=
          execM_rootAgreeList hdom hsrc hsy htr hfi hcg htgt huq hl₁ hl₂ hrs₁ hrs₂
        obtain ⟨q₁, hq₁⟩ :=
          execM_viewRow_of_rowReachList hdom htr hsy hfi hcg htgt hfk₁ hrow₁
            hrs₁.length_eq.symm (rootList_reach hrs₁)
        obtain ⟨q₂, hq₂⟩ :=
          execM_viewRow_of_rowReachList hdom htr hsy hfi hcg htgt hfk₂ hrow₂
            hrs₂.length_eq.symm (rootList_reach hrs₂)
        rw [hsame] at hq₁
        exact (List.cons.inj (huq f _ hfk₂ rs' [r₁, q₁] [r₂, q₂] hq₁ hq₂)).1

@[inherit_doc execM_rootAgree]
theorem execM_rootAgreeList {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 →
      (encodeSig P).IsCtor (congrName k))
    (htgt : execM (encode P) = some tgt) (huq : tgt.ViewRowUnique P) :
    ∀ {ts es₁ : List Term}, ViewReprList tgt.toDatabase ts es₁ → ∀ {es₂ rs₁ rs₂ : List Term},
      ViewReprList tgt.toDatabase ts es₂ →
        List.Forall₂ (fun a r => tgt.UFRowReach a r ∧ tgt.UFRowRoot r) es₁ rs₁ →
        List.Forall₂ (fun a r => tgt.UFRowReach a r ∧ tgt.UFRowRoot r) es₂ rs₂ → rs₁ = rs₂
  | _, _, .nil, _, _, _, h₂, k₁, k₂ => by
      cases h₂; cases k₁; cases k₂; rfl
  | _, _, .cons ha hl, _, _, _, h₂, k₁, k₂ => by
      cases h₂ with
      | cons ha₂ hl₂ =>
        cases k₁ with
        | cons kh₁ kt₁ =>
          cases k₂ with
          | cons kh₂ kt₂ =>
            rw [execM_rootAgree hdom hsrc hsy htr hfi hcg htgt huq ha ha₂
                  kh₁.1 kh₁.2 kh₂.1 kh₂.2,
              execM_rootAgreeList hdom hsrc hsy htr hfi hcg htgt huq hl hl₂ kt₁ kt₂]
end

/-- **The residue, with the literal clause read at the rows and nothing else left.**

`eclass` and `edged` both answer with the id's own `@UF` row root: `execM_ufRowRoot_of_ufReach`
gives an `@UF` entry's two ends one root, `execM_rootAgree` gives two readings of one source term
one root, and `execM_viewRow_at_root` is the absorption — a reader of the id is answered by a
live row whose e-class column *is* that root, which `execM_out_of_viewRow` reads back as the
entry `Database.Absorbs` wants. `column` is `execM_rebuildColumn`.

**The one hypothesis is the literal reader.** `ViewRepr d (.lit l) a` forces `a = .lit l` with no
premise at all, so absorption asks that a literal be its own root — and at the *rows*, which is
the reading `FDatabase.UFLitsIsolated.ufRowRoot` produces from the entry-valued clause. That
clause's key half is paid (`ufLitsIsolated_of_no_lit_lit`, out of `execM_ufTermsDescend`) and its
value half is not: of its four writers a top-level source `union` is paid
(`union_target_notLit`, `union_out_uf_notLit`) and a rule head is excluded
(`Program.EncodeDomain.noLitUnion`), leaving `mergeBody` at both its tables and
`pathCompressRule`. -/
theorem execM_rebuildClosed_of_ufLitRoots {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 →
      (encodeSig P).IsCtor (congrName k))
    (htgt : execM (encode P) = some tgt) (hlit : ∀ l : Lit, tgt.UFRowRoot (Term.lit l)) :
    tgt.toDatabase.RebuildClosed tgt.UFRowRoot := by
  have hb : tgt.EncBase P (encodeSig P) := execM_encode_encBase hdom hdom.aritiesAgree' htgt
  have hufmg : tgt.sig.mergeOf ufName ≠ none := by
    rw [hb.sig]; exact encodeSig_mergeOf_ufName hdom
  have huq : tgt.ViewRowUnique P := execM_viewRowUnique hdom hsy htr htgt
  -- the id lands on its own `@UF` row root, at every reader
  have hlands : ∀ {a r : Term}, tgt.UFRowReach a r → tgt.UFRowRoot r →
      tgt.toDatabase.Lands a r := by
    intro a r hr hrr
    refine ⟨hr.toUFReach hb.inv.index hufmg, ?_⟩
    intro t ht
    cases t with
    | lit l =>
        obtain rfl := ht.eq_of_lit
        rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨b, hb', -⟩
        · exact ht
        · exact absurd hb' (hlit l b)
    | app g bs =>
        cases ht with
        | app hl ho =>
          obtain ⟨lo, hfk, hrow⟩ := execM_viewRow_at_root hdom hsrc hsy htr htgt ho hr hrr
          exact .app hl (execM_out_of_viewRow hdom htgt hfk hrow)
  refine ⟨fun a b hs => ?_, fun t e₁ e₂ h₁ h₂ => ?_,
    fun f es ds e pf ho hl => execM_rebuildColumn hdom hsrc hsy htr hfi hcg htgt ho hl⟩
  · obtain ⟨r, hr, hrr⟩ := execM_exists_ufRowRoot hdom htgt a
    obtain ⟨s, hs', hsr⟩ := execM_exists_ufRowRoot hdom htgt b
    obtain rfl : r = s :=
      execM_ufRowRoot_of_ufReach hdom hsy htr htgt hs.toReach r s hr hrr hs' hsr
    exact ⟨r, hlands hr hrr, hlands hs' hsr⟩
  · obtain ⟨r, hr, hrr⟩ := execM_exists_ufRowRoot hdom htgt e₁
    obtain ⟨s, hs, hsr⟩ := execM_exists_ufRowRoot hdom htgt e₂
    obtain rfl : r = s :=
      execM_rootAgree hdom hsrc hsy htr hfi hcg htgt huq h₁ h₂ hr hrr hs hsr
    exact ⟨r, ⟨hlands hr hrr, hrr⟩, ⟨hlands hs hsr, hrr⟩⟩

/-- **Non-vacuous at the run**: every hypothesis of `execM_rebuildClosed_of_ufLitRoots` but the
literal one holds together at `ncProgram`, whose rebuild really re-keys a view row — so the four
`Signature.IsCtor` carries and the source run are inhabited at a program the encoder runs, and
what separates this from `execM_rebuildClosed` is the literal clause alone. -/
theorem execM_rebuildClosed_of_ufLitRoots_witness {tgt : FDatabase}
    (htgt : execM (encode ncProgram) = some tgt)
    (hlit : ∀ l : Lit, tgt.UFRowRoot (Term.lit l)) :
    tgt.toDatabase.RebuildClosed tgt.UFRowRoot :=
  execM_rebuildClosed_of_ufLitRoots ncProgram_encodeDomain ncProgram_programStep
    ncProgram_isCtor_symName ncProgram_isCtor_transName ncProgram_isCtor_fiatName
    ncProgram_isCtor_congrName htgt hlit

/-! ## The forward half's residue, and the correspondence

`Database.RebuildClosed` and its four consumers are stated here and not in
`Encoding/Correspond.lean` because their proof reads this file: the bridge
(`execM_entryRowsUF`), the forest (`execM_ufRowRoot_unique`), the fixpoint's roots
(`no_ufRowEdge_of_rowsClosed`) and `encodeSig` itself. The definitions they are stated over,
the state-level reductions and the refutations stay upstream, which is why
`Encoding/Correspond.lean` is still all `DiffTest.lean` imports. -/

/-! ### The proof vocabulary is declared, at every program

`Database.Absorbs` and the rebuild firings are all keyed on `Signature.IsCtor` at the four
proof heads the maintenance rules apply, and `execM_rebuildClosed` cannot take those as
hypotheses because `encode_corresponds` does not. It does not have to: the signature is
`encodeSig P`, which `execM (encode P) = some tgt` pins, and `encodePrelude`'s `proofDecls`
declares all four.

**Shadowing is not an obstacle, because `Signature.IsCtor` reads only the `merge` field.**
`encodeSig` folds over the prelude alone (`encodeCmds` emits no declaration), and of the
prelude's declarations only `@UF` and each source constructor's view and term table carry a
`:merge`. A later `proofDecl` or `skolemDecl` at a proof head's name would change its arity
and leave it a constructor, so what has to be excluded is exactly `ufName`, `viewName f` and
`termName f` — three name separations, and no clause of `Program.EncodeDomain` is spent. -/

/-- **A term relation is never a fixed proof head**, by the last two characters — the
counterpart of `viewName_ne_symName` and its companions. -/
theorem termName_ne_symName {f : FnName} : termName f ≠ symName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [termName, symName, String.toList_append, List.reverse_append] at h2

@[inherit_doc termName_ne_symName]
theorem termName_ne_transName {f : FnName} : termName f ≠ transName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [termName, transName, String.toList_append, List.reverse_append] at h2

@[inherit_doc termName_ne_symName]
theorem termName_ne_fiatName {f : FnName} : termName f ≠ fiatName := by
  intro h
  have h2 := congrArg (fun s => (String.toList s).reverse) h
  simp [termName, fiatName, String.toList_append, List.reverse_append] at h2

/-- **A term relation is never a congruence head**, whatever the arity: `"@Term"` carries an
`'m'`, `"@Congr_"` does not, and `Nat.isDigit_of_mem_toDigits` says the arity suffix does not
either. Mirrors `viewName_ne_congrName`. -/
theorem termName_ne_congrName {f : FnName} {k : Nat} : termName f ≠ congrName k := by
  intro h
  have hw : 'm' ∈ (termName f).toList := by
    rw [termName, String.toList_append]
    exact List.mem_append_right _ (by decide)
  rw [h, congrName, String.toList_append] at hw
  rcases List.mem_append.mp hw with h1 | h1
  · exact absurd h1 (by decide)
  · have hd := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
      (show 'm' ∈ Nat.toDigits 10 k by rw [Nat.toString_eq_repr, Nat.toList_repr] at h1; exact h1)
    simp at hd

/-- **A fold over declarations answers `Signature.IsCtor`** as soon as the list declares the
name and no declaration of it carries a `:merge`: shadowing by a further constructor
declaration only changes the arity, which `Signature.IsCtor` does not read. -/
theorem isCtor_foldl_sigBind {n : FnName} : ∀ {p : Program},
    (∀ dc : FnDecl, Cmd.decl n dc ∈ p → dc.merge = none) →
    ∀ {sig : Signature}, (sig.IsCtor n ∨ ∃ dc, Cmd.decl n dc ∈ p) →
      (p.foldl (fun s c => c.sigBind s) sig).IsCtor n := by
  intro p
  induction p with
  | nil =>
    intro _ sig h
    exact h.resolve_right (by rintro ⟨dc, hdc⟩; exact absurd hdc (by simp))
  | cons c cs ih =>
    intro hp sig h
    refine ih (fun dc hdc => hp dc (List.mem_cons_of_mem c hdc)) ?_
    have hhere : ∀ dc, c = Cmd.decl n dc → (c.sigBind sig).IsCtor n := by
      rintro dc rfl
      exact ⟨dc, by simp [Cmd.sigBind], hp dc List.mem_cons_self⟩
    by_cases hcs : ∃ dc, Cmd.decl n dc ∈ cs
    · exact Or.inr hcs
    · refine Or.inl ?_
      rcases h with h | ⟨dc, hdc⟩
      · cases c with
        | decl f dc =>
          by_cases hf : f = n
          · exact hhere dc (by rw [hf])
          · obtain ⟨d, hd, hm⟩ := h
            refine ⟨d, ?_, hm⟩
            change Function.update sig f (some dc) n = some d
            rw [Function.update_of_ne (fun hc => hf hc.symm)]
            exact hd
        | _ => exact h
      · rcases List.mem_cons.mp hdc with rfl | hm
        · exact hhere dc rfl
        · exact absurd ⟨dc, hm⟩ hcs

/-- Every rule's justification head is declared as a `proofDecl`. -/
theorem merge_none_of_mem_ruleProofDecls :
    ∀ (R : Program) (G : List (Var × Expr)) (p : Program) (i : Nat) (g : FnName)
    (dc : FnDecl), Cmd.decl g dc ∈ ruleProofDecls R G p i → dc.merge = none := by
  intro R G p
  induction p generalizing G with
  | nil => intro i g dc h; exact absurd h (by simp [ruleProofDecls])
  | cons c cs ih =>
    intro i g dc h
    rw [ruleProofDecls] at h
    rcases List.mem_append.mp h with h' | h'
    · obtain ⟨r, -, he⟩ := mem_proofDeclOf h'
      injection he with _ h2; subst h2; rfl
    · exact ih _ _ g dc h'

@[inherit_doc merge_none_of_mem_ruleProofDecls]
theorem merge_none_of_mem_proofDecls {P : Program} {g : FnName} {dc : FnDecl}
    (h : Cmd.decl g dc ∈ proofDecls P) : dc.merge = none := by
  rw [proofDecls, List.mem_append, List.mem_append] at h
  rcases h with (h | h) | h
  · rcases List.mem_cons.mp h with h' | h'
    · injection h' with _ h2; subst h2; rfl
    rcases List.mem_cons.mp h' with h'' | h''
    · injection h'' with _ h2; subst h2; rfl
    rcases List.mem_cons.mp h'' with h''' | h'''
    · injection h''' with _ h2; subst h2; rfl
    · exact absurd h''' (by simp)
  · obtain ⟨k, -, hk⟩ := List.mem_map.mp h
    injection hk with _ h2; subst h2; rfl
  · exact merge_none_of_mem_ruleProofDecls _ _ _ _ _ _ h

/-- **The prelude's only `:merge`-carrying declarations are `@UF` and the two tables.** -/
theorem merge_none_of_mem_encodePrelude {P : Program} {n : FnName} {dc : FnDecl}
    (huf : n ≠ ufName) (hv : ∀ f, n ≠ viewName f) (ht : ∀ f, n ≠ termName f)
    (h : Cmd.decl n dc ∈ encodePrelude P) : dc.merge = none := by
  rw [encodePrelude] at h
  rcases List.mem_append.mp h with h₁ | h₁
  · rcases List.mem_append.mp h₁ with h₂ | h₂
    · exact merge_none_of_mem_proofDecls h₂
    · rcases List.mem_cons.mp h₂ with h₃ | h₃
      · injection h₃ with h₄ _; exact absurd h₄ huf
      · obtain ⟨fk, -, h₅⟩ := List.mem_flatMap.mp h₃
        have h₆ : Cmd.decl n dc = Cmd.decl fk.1 (skolemDecl fk.2) ∨
            Cmd.decl n dc = Cmd.decl (viewName fk.1) (viewDecl fk.2) ∨
            Cmd.decl n dc = Cmd.decl (termName fk.1) (termDecl fk.2) := by simpa using h₅
        rcases h₆ with h₇ | h₇ | h₇
        · injection h₇ with _ h₈; subst h₈; rfl
        · injection h₇ with h₈ _; exact absurd h₈ (hv fk.1)
        · injection h₇ with h₈ _; exact absurd h₈ (ht fk.1)
  · obtain ⟨r, -, hr⟩ := List.mem_map.mp h₁
    exact absurd hr.symm (by simp)

theorem mem_encodePrelude_of_mem_proofDecls {P : Program} {c : Cmd}
    (h : c ∈ proofDecls P) : c ∈ encodePrelude P := by
  rw [encodePrelude]
  exact List.mem_append_left _ (List.mem_append_left _ h)

/-- **A proof head the vocabulary declares is a constructor of `encodeSig P`**, provided it is
neither `@UF` nor a table name. -/
theorem encodeSig_isCtor_of_mem_proofDecls {P : Program} {n : FnName} {dc : FnDecl}
    (hmem : Cmd.decl n dc ∈ proofDecls P)
    (huf : n ≠ ufName) (hv : ∀ f, n ≠ viewName f) (ht : ∀ f, n ≠ termName f) :
    (encodeSig P).IsCtor n := by
  rw [encodeSig]
  exact isCtor_foldl_sigBind (fun dc' hdc' => merge_none_of_mem_encodePrelude huf hv ht hdc')
    (Or.inr ⟨dc, mem_encodePrelude_of_mem_proofDecls hmem⟩)

/-- Each fixed proof head, and each congruence head at a declared arity, is in the
vocabulary. -/
theorem mem_proofDecls_fiatName {P : Program} :
    Cmd.decl fiatName (proofDecl 0) ∈ proofDecls P := by
  rw [proofDecls]
  exact List.mem_append_left _ (List.mem_append_left _ (by simp))

@[inherit_doc mem_proofDecls_fiatName]
theorem mem_proofDecls_symName {P : Program} :
    Cmd.decl symName (proofDecl 1) ∈ proofDecls P := by
  rw [proofDecls]
  exact List.mem_append_left _ (List.mem_append_left _ (by simp))

@[inherit_doc mem_proofDecls_fiatName]
theorem mem_proofDecls_transName {P : Program} :
    Cmd.decl transName (proofDecl 2) ∈ proofDecls P := by
  rw [proofDecls]
  exact List.mem_append_left _ (List.mem_append_left _ (by simp))

@[inherit_doc mem_proofDecls_fiatName]
theorem mem_proofDecls_congrName {P : Program} {k : Nat} (hk : k ∈ congrArities P) :
    Cmd.decl (congrName k) (proofDecl k) ∈ proofDecls P := by
  rw [proofDecls]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hk))

/-- `congrArities` carries every positive arity of `Program.ctors`. -/
theorem mem_congrArities_of_mem_ctors {P : Program} {g : FnName} {k : Nat}
    (h : (g, k) ∈ P.ctors) (hk : k ≠ 0) : k ∈ congrArities P := by
  rw [congrArities, List.mem_filter]
  exact ⟨List.mem_dedup.mpr (List.mem_map.mpr ⟨(g, k), h, rfl⟩), by simpa using hk⟩

/-- **`@Sym` is a constructor of `encodeSig P`, at every program.** -/
theorem encodeSig_isCtor_symName (P : Program) : (encodeSig P).IsCtor symName :=
  encodeSig_isCtor_of_mem_proofDecls mem_proofDecls_symName (by decide)
    (fun _ h => viewName_ne_symName h.symm) (fun _ h => termName_ne_symName h.symm)

@[inherit_doc encodeSig_isCtor_symName]
theorem encodeSig_isCtor_transName (P : Program) : (encodeSig P).IsCtor transName :=
  encodeSig_isCtor_of_mem_proofDecls mem_proofDecls_transName (by decide)
    (fun _ h => viewName_ne_transName h.symm) (fun _ h => termName_ne_transName h.symm)

@[inherit_doc encodeSig_isCtor_symName]
theorem encodeSig_isCtor_fiatName (P : Program) : (encodeSig P).IsCtor fiatName :=
  encodeSig_isCtor_of_mem_proofDecls mem_proofDecls_fiatName (by decide)
    (fun _ h => viewName_ne_fiatName h.symm) (fun _ h => termName_ne_fiatName h.symm)

/-- **And `@Congr_k` is one at each positive arity a source constructor has** — which is
exactly the set `congrArities` declares. -/
theorem encodeSig_isCtor_congrName {P : Program} {g : FnName} {k : Nat}
    (h : (g, k) ∈ P.ctors) (hk : k ≠ 0) : (encodeSig P).IsCtor (congrName k) :=
  encodeSig_isCtor_of_mem_proofDecls (mem_proofDecls_congrName (mem_congrArities_of_mem_ctors h hk))
    (fun hc => ufName_ne_congrName hc.symm)
    (fun _ h' => viewName_ne_congrName h'.symm) (fun _ h' => termName_ne_congrName h'.symm)

/-! ### The literal clause, out of the completeness half

`FDatabase.SoundTerms`' second clause answers an `@UF` entry term with a source congruence,
and `Database.WF.litsIsolated` makes a literal's class a singleton there
(`Cong.eq_of_isLit`). So the run-wide invariant the entry-valued clause was estimated to cost
is already paid, by `execM_soundTerms` and the source run together, at all four writers at
once: `mergeBody` and `pathCompressRule` write only what the source justifies. -/

/-- **No `@UF` entry of the target is keyed on a literal it does not equal.** -/
theorem execM_ufLitsIsolated {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.UFLitsIsolated := by
  intro l b pf hmem
  exact (((execM_soundTerms hdom hsrc htgt).2 _ _ _ hmem).eq_of_isLit
    (hsrc.wf Database.WF.empty).litsIsolated (Or.inl rfl)).symm

/-- **A literal is its own `@UF` row root**, which is what `Database.Absorbs` asks at a
literal reader. -/
theorem execM_ufLitRoots {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (l : Lit) : tgt.UFRowRoot (Term.lit l) :=
  (execM_ufLitsIsolated hdom hsrc htgt).ufRowRoot (execM_encode_eqsRefl htgt)
    (execM_encode_encBase hdom hdom.aritiesAgree' htgt).inv.index
    (by rw [(execM_encode_encBase hdom hdom.aritiesAgree' htgt).sig]
        exact encodeSig_mergeOf_ufName hdom) l

/-! ### The mechanism at a state the run passes through

Everything above is stated at `execM (encode P) = some tgt`, and the residue's firing happens
one block short of that — at the state the *next* encoded block starts at, which is what
`Egglog.UnionsFire` quantifies over. The generalisation is not a different argument: each of
these is already a block induction, and `EncReached` is exactly the provenance those inductions
consume, one whole `encodeCmd` block at a time.

**What does not generalise for free is the source side.** `execM_ufLitRoots` and
`execM_ctorsIn_of_mem_terms` are the two facts the *source run* pays for, through
`execM_soundTerms`, and a reached state does not carry them: it knows nothing of a source. They
are hypotheses of this family, named where they are spent, and `EncStep` — the same chain with
the source run alongside — is what pays them, in the section below. -/

/-- **A run's own states are reached ones**, block by block. -/
theorem encReached_encodeCmds {P : Program} :
    ∀ (p : Program) {R : Program}, (∀ c ∈ p, c ∈ P) →
      ∀ (G : List (Var × Expr)) (n i : Nat) {d D : FDatabase},
      EncReached P d → d.execProgramM (encodeCmds R G p n i).1 = some D → EncReached P D := by
  intro p
  induction p with
  | nil =>
    intro R _ G n i d D h hs
    rw [show (encodeCmds R G ([] : Program) n i).1 = ([] : Program) from rfl,
      FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ h
  | cons c cs ih =>
    intro R hp G n i d D h hs
    rw [encodeCmds_cons_fst] at hs
    obtain ⟨d₁, h₁, h₂⟩ := FDatabase.execProgramM_append hs
    exact ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) _ _ _
      (.block h (hp c List.mem_cons_self) h₁) h₂

@[inherit_doc encReached_encodeCmds]
theorem execM_encReached {P : Program} {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : EncReached P tgt := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  exact encReached_encodeCmds P (fun _ hc => hc) [] 0 0 (.prelude hprel) hcmds

/-- **The structural bundle at every reached state**: the prelude's own instance, carried one
block at a time by `rebuildBase_encodeCmd`. -/
theorem encReached_rebuildBase {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.RebuildBase P := by
  induction h with
  | prelude hprel =>
    have hb₀ := (encOk_preludeState hdom hdom.aritiesAgree' hprel).base
    have hdata := execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel
    refine ⟨hb₀, ⟨fun t ht => ?_, fun b hb => ?_⟩, ?_⟩
    · rw [hdata.1, show FDatabase.empty.terms = ([] : List Term) from rfl] at ht
      exact absurd ht (by simp)
    · rw [hdata.2.2.2, show FDatabase.empty.env = ([] : Env) from rfl] at hb
      exact absurd hb (by simp)
    · refine FDatabase.ufRowsDescend_iff.mpr fun a b pf hmem => ?_
      rw [hdata.2.1, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
      exact absurd hmem (by simp)
  | block _ hc hb ih => exact rebuildBase_encodeCmd hdom hc (fun _ hc' => hc') ih hb

@[inherit_doc encReached_rebuildBase]
theorem encReached_encBase {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.EncBase P (encodeSig P) := (encReached_rebuildBase hdom h).base

@[inherit_doc encReached_rebuildBase]
theorem encReached_eqsRefl {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.EqsRefl := (encReached_encBase hdom h).eqsRefl

@[inherit_doc encReached_rebuildBase]
theorem encReached_rowColumnsValued {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.RowColumnsValued := (encReached_rebuildBase hdom h).rowColumnsValued

@[inherit_doc encReached_rebuildBase]
theorem encReached_ufRowsDescend {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.UFRowsDescend := (encReached_rebuildBase hdom h).descend

@[inherit_doc encReached_rebuildBase]
theorem encReached_exists_ufRowRoot {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) (a : Term) : ∃ r, d.UFRowReach a r ∧ d.UFRowRoot r :=
  FDatabase.exists_ufRowRoot (encReached_ufRowsDescend hdom h) a

/-- **The forest at every reached state.** -/
theorem encReached_ufRowsForest {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d) : d.UFRowsForest := by
  induction h with
  | prelude hprel =>
    have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
    intro a b c hb _
    obtain ⟨pf, hmem⟩ := hb.1
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hmem
    exact absurd hmem (by simp)
  | block hr hc hb ih =>
    exact FDatabase.EncBase.execProgramM_ufRowsForest (encodeSig_ufName hdom) hsy htr
      (fun c' hc' => rulesEncodedOk_encodeCmd hc _ _ _ c' hc')
      (fun c' hc' => encodeCmd_unionFree _ _ _ _ c' hc')
      (fun c' hc' => noDecl_encodeCmd _ _ _ _ c' hc')
      (fun c' hc' => encodedWriteLegal hdom hdom.aritiesAgree' _ hc _ _ _ c' hc')
      (fun c' hc' => ufWriteOk_encodeCmd _ _ _ _ c' hc')
      (fun c' hc' => noAtLet_encodeCmd hdom _ _ hc _ _ c' hc')
      (encReached_rebuildBase hdom hr).base (encReached_rebuildBase hdom hr).descend ih hb

/-- **The bridge at every reached state.** -/
theorem encReached_entryRowsUF {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.EntryRowsUF := by
  induction h with
  | prelude hprel =>
    have hterms := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).1
    intro f dc hdc body res hm as x pf hlen hmem
    rw [hterms, show FDatabase.empty.terms = ([] : List Term) from rfl] at hmem
    exact absurd hmem (by simp)
  | block hr hc hb ih =>
    exact FDatabase.EncBase.execProgramM_entryRowsUF hdom
      (fun c' hc' => rulesEncodedOk_encodeCmd hc _ _ _ c' hc')
      (fun c' hc' => encodeCmd_unionFree _ _ _ _ c' hc')
      (fun c' hc' => noDecl_encodeCmd _ _ _ _ c' hc')
      (fun c' hc' => encodedWriteLegal hdom hdom.aritiesAgree' _ hc _ _ _ c' hc')
      (fun c' hc' => entryWriteOk_encodeCmd hdom _ _ hc _ _ c' hc')
      (fun c' hc' => noAtLet_encodeCmd hdom _ _ hc _ _ c' hc')
      (encReached_rebuildBase hdom hr).base ih hb

/-- **Entry-term descent at every reached state.** -/
theorem encReached_ufTermsDescend {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : d.UFTermsDescend := by
  induction h with
  | prelude hprel =>
    have hterms := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).1
    refine FDatabase.ufTermsDescend_iff.mpr fun a b pf hmem => ?_
    rw [hterms, show FDatabase.empty.terms = ([] : List Term) from rfl] at hmem
    exact absurd hmem (by simp)
  | block hr hc hb ih =>
    exact FDatabase.EncBase.execProgramM_ufTermsDescend hdom
      (fun c' hc' => rulesEncodedOk_encodeCmd hc _ _ _ c' hc')
      (fun c' hc' => encodeCmd_unionFree _ _ _ _ c' hc')
      (fun c' hc' => noDecl_encodeCmd _ _ _ _ c' hc')
      (fun c' hc' => encodedWriteLegal hdom hdom.aritiesAgree' _ hc _ _ _ c' hc')
      (fun c' hc' => ufWriteOk_encodeCmd _ _ _ _ c' hc')
      (fun c' hc' => entryWriteOk_encodeCmd hdom _ _ hc _ _ c' hc')
      (fun c' hc' => noAtLet_encodeCmd hdom _ _ hc _ _ c' hc')
      (encReached_rebuildBase hdom hr).base (encReached_rebuildBase hdom hr).descend ih hb

/-- **The identification at every reached state**: entry reachability and row reachability land
on one `@UF` row root. -/
theorem encReached_ufRowRoot_of_ufReach {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d) {a b : Term} (hreach : d.toDatabase.UFReach a b) :
    ∀ r s, d.UFRowReach a r → d.UFRowRoot r → d.UFRowReach b s → d.UFRowRoot s → r = s :=
  FDatabase.ufRowRoot_of_ufReach (encReached_eqsRefl hdom h) (encReached_entryRowsUF hdom h)
    (by rw [(encReached_encBase hdom h).sig]; exact encodeSig_ufName hdom)
    (encReached_ufRowsDescend hdom h) (encReached_ufRowsForest hdom hsy htr h)
    (encReached_ufTermsDescend hdom h) hreach

/-- **The root is unique at every reached state.** -/
theorem encReached_ufRowRoot_unique {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d) (a : Term) :
    ∃ r, d.UFRowReach a r ∧ d.UFRowRoot r ∧
      ∀ s, d.UFRowReach a s → d.UFRowRoot s → s = r := by
  obtain ⟨r, hr, hrr⟩ := FDatabase.exists_ufRowRoot (encReached_ufRowsDescend hdom h) a
  exact ⟨r, hr, hrr, fun s hs hsr =>
    FDatabase.ufRowRoot_unique (encReached_ufRowsForest hdom hsy htr h) hs hsr hr hrr⟩

/-- **Pointwise roots of a tuple, at a reached state.** -/
theorem encReached_exists_rootList {P : Program} (hdom : P.EncodeDomain) {d : FDatabase}
    (h : EncReached P d) : ∀ (es : List Term),
      ∃ rs, List.Forall₂ (fun a r => d.UFRowReach a r ∧ d.UFRowRoot r) es rs
  | [] => ⟨[], .nil⟩
  | a :: as => by
      obtain ⟨r, hr, hrr⟩ := encReached_exists_ufRowRoot hdom h a
      obtain ⟨rs, hrs⟩ := encReached_exists_rootList hdom h as
      exact ⟨r :: rs, .cons ⟨hr, hrr⟩ hrs⟩

/-- **The fixpoint's roots at every reached state.** -/
theorem encReached_viewRowsRooted {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d) : d.ViewRowsRooted P := by
  induction h with
  | prelude hprel =>
    have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
    intro f k _ as e pf hrow
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hrow
    exact absurd hrow (by simp)
  | block hr hc hb ih =>
    exact viewRowsRooted_encodeCmd hdom hsy htr hc _ _ _ (encReached_rebuildBase hdom hr) ih hb

/-- **The merge fixpoint at a view key, at every reached state.** -/
theorem encReached_viewRowUnique {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d) : d.ViewRowUnique P := by
  induction h with
  | prelude hprel =>
    have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
    intro f k _ as vs ws hrow
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hrow
    exact absurd hrow (by simp)
  | block hr hc hb ih =>
    exact viewRowUnique_encodeCmd hdom hsy htr hc _ _ _ (encReached_rebuildBase hdom hr) ih hb

/-- **The column rules' closure at every reached state.** -/
theorem encReached_viewRowsColumnClosed {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d) : d.ViewRowsColumnClosed P := by
  induction h with
  | prelude hprel =>
    have hrows := (execProgramM_data_of_declOrRule (declOrRule_encodePrelude P) hprel).2.1
    intro f k _ as e pf hrow
    rw [hrows, show FDatabase.empty.rows = ([] : List Row) from rfl] at hrow
    exact absurd hrow (by simp)
  | block hr hc hb ih =>
    exact viewRowsColumnClosed_encodeCmd hdom htr hsy hfi hcg hc _ _ _
      (encReached_rebuildBase hdom hr) ih hb

/-- **One column step at a reached state.** -/
theorem encReached_columnRow_step {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows) {i : Nat} {ci x : Term}
    (hci : as[i]? = some ci) (hedge : d.UFRowEdge ci x) :
    ∃ pf', (⟨viewName f, as.set i x, [e, pf']⟩ : Row) ∈ d.rows := by
  obtain ⟨e', pf', hrow', hreach⟩ :=
    encReached_viewRowsColumnClosed hdom htr hsy hfi hcg h f k hfk as e pf hrow i ci x hci hedge
  have hre : d.UFRowRoot e := encReached_viewRowsRooted hdom hsy htr h f k hfk as e pf hrow
  have hre' : d.UFRowRoot e' :=
    encReached_viewRowsRooted hdom hsy htr h f k hfk (as.set i x) e' pf' hrow'
  have heq : e = e' :=
    encReached_ufRowRoot_of_ufReach hdom hsy htr h hreach e e' .refl hre .refl hre'
  exact ⟨pf', heq ▸ hrow'⟩

/-- **A whole chain of column steps, at a reached state.** -/
theorem encReached_columnRow_walk {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows) {i : Nat} {ci r : Term}
    (hci : as[i]? = some ci) (hreach : d.UFRowReach ci r) :
    ∃ pf', (⟨viewName f, as.set i r, [e, pf']⟩ : Row) ∈ d.rows := by
  induction hreach with
  | refl =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hci
    exact ⟨pf, by rw [List.set_getElem_self hi]; exact hrow⟩
  | tail _ hstep ih =>
    obtain ⟨pf', hrow'⟩ := ih
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hci
    obtain ⟨pf'', hrow''⟩ :=
      encReached_columnRow_step hdom htr hsy hfi hcg h hfk hrow' (i := i)
        (List.getElem?_set_self hi) hstep
    exact ⟨pf'', by rwa [List.set_set] at hrow''⟩

/-- **Every column at once, at a reached state.** -/
theorem encReached_columnRow_walkList {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {e : Term} :
    ∀ (ps as bs : List Term), bs.length = as.length →
      (∀ (j : Nat) (hj : j < as.length) (hj' : j < bs.length), d.UFRowReach (as[j]) (bs[j])) →
      (∃ pf, (⟨viewName f, ps ++ as, [e, pf]⟩ : Row) ∈ d.rows) →
      ∃ pf, (⟨viewName f, ps ++ bs, [e, pf]⟩ : Row) ∈ d.rows
  | _, [], [], _, _, hx => hx
  | _, [], _ :: _, hlen, _, _ => by simp at hlen
  | _, _ :: _, [], hlen, _, _ => by simp at hlen
  | ps, a :: as, b :: bs, hlen, hj, ⟨pf, hrow⟩ => by
      obtain ⟨pf', hrow'⟩ :=
        encReached_columnRow_walk hdom htr hsy hfi hcg h hfk hrow (i := ps.length) (ci := a)
          (by simp) (hj 0 (by simp) (by simp))
      rw [show (b :: bs)[0] = b from rfl,
        show (ps ++ a :: as).set ps.length b = ps ++ b :: as by simp] at hrow'
      obtain ⟨pf'', hrow''⟩ :=
        encReached_columnRow_walkList hdom htr hsy hfi hcg h hfk (ps ++ [b]) as bs
          (by simpa using hlen)
          (fun j hj' hj'' => hj (j + 1) (by simpa using hj') (by simpa using hj''))
          ⟨pf', by simpa using hrow'⟩
      exact ⟨pf'', by simpa using hrow''⟩

/-- **The column rules at their fixpoint, for a key tuple, at a reached state.** -/
theorem encReached_viewRow_of_rowReachList {P : Program} (hdom : P.EncodeDomain)
    (htr : (encodeSig P).IsCtor transName) (hsy : (encodeSig P).IsCtor symName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d)
    {f : FnName} {k : Nat} (hfk : (f, k) ∈ P.ctors) {as bs : List Term} {e pf : Term}
    (hrow : (⟨viewName f, as, [e, pf]⟩ : Row) ∈ d.rows) (hlen : bs.length = as.length)
    (hj : ∀ (j : Nat) (hj : j < as.length) (hj' : j < bs.length), d.UFRowReach (as[j]) (bs[j])) :
    ∃ pf', (⟨viewName f, bs, [e, pf']⟩ : Row) ∈ d.rows := by
  obtain ⟨pf', hrow'⟩ :=
    encReached_columnRow_walkList hdom htr hsy hfi hcg h hfk [] as bs hlen hj
      ⟨pf, by simpa using hrow⟩
  exact ⟨pf', by simpa using hrow'⟩

/-- **The bridge's answer is the root itself, at a reached state.** -/
theorem encReached_viewRow_at_root {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    {d : FDatabase} (h : EncReached P d)
    (hctors : ∀ (g : FnName) (cs : List Term) (v pv : Term),
      Term.app (viewName g) (cs ++ [v, pv]) ∈ d.terms → (g, cs.length) ∈ P.ctors)
    {f : FnName} {es : List Term} {x px r : Term}
    (ho : d.toDatabase.Out (viewName f) es [x, px])
    (hr : d.UFRowReach x r) (hrr : d.UFRowRoot r) :
    ∃ lo, (f, es.length) ∈ P.ctors ∧ (⟨viewName f, es, [r, lo]⟩ : Row) ∈ d.rows := by
  have hb : d.EncBase P (encodeSig P) := encReached_encBase hdom h
  have hmem : Term.app (viewName f) (es ++ [x, px]) ∈ d.terms := by
    obtain ⟨bs, hcl, hm⟩ := ho
    obtain rfl : es = bs := CongList.eq_of_eqsRefl (encReached_eqsRefl hdom h).toDatabase hcl
    rw [FDatabase.toDatabase_terms] at hm
    exact hm
  have hfk : (f, es.length) ∈ P.ctors := hctors f es x px hmem
  obtain ⟨v, lo, hrow, hreach⟩ :=
    (encReached_entryRowsUF hdom h).out (encReached_eqsRefl hdom h) (dc := viewDecl es.length)
      (by rw [hb.sig]; exact (encodeSig_tables hdom hdom.aritiesAgree' hfk).1)
      (body := mergeBody) (res := mergeResult) rfl rfl ho
  have hvroot : d.UFRowRoot v :=
    encReached_viewRowsRooted hdom hsy htr h f es.length hfk es v lo hrow
  have heq : r = v :=
    encReached_ufRowRoot_of_ufReach hdom hsy htr h hreach r v hr hrr .refl hvroot
  rw [← heq] at hrow
  exact ⟨lo, hfk, hrow⟩

/-! ### The reading, at the pointwise root

`RowRepr` is the reading through live **rows**, and the residue wants it where the invariant
supplies `ViewRepr` — a reading through entry **terms**. The two are not the same claim at the
same ids: `FDatabase.EntryRowsUF` answers an entry with a row whose e-class column is only
`Database.UFReach`-reachable from the entry's, and a parent read is keyed on its children's
columns on the nose.

**They are the same claim at the pointwise `@UF` row root, and that is the choice of tuple.**
`encReached_viewRow_at_root` answers the entry with a live row whose e-class column *is* the
root of the id the entry recorded, at the entry's own key; `encReached_exists_rootList` names
the root of each key column; and `encReached_viewRow_of_rowReachList` walks the whole key onto
that rooted tuple in one go, leaving the e-class column where it was. So the row the parent ends
at is keyed exactly on the roots its children's own rows sit at, which is what `RowRepr` demands
— and the child column is a root because it is the *value* column of a live view row, which is
the instance `FDatabase.ViewRowsRooted` supplies and the one an arbitrary reading does not.

The literal case is where the source run is spent: a literal is its own root (`hlit`) and roots
are unique, so a literal's rooted reading is the literal itself, which is the sole `RowRepr` a
literal has. -/

mutual

/-- **Every reading is a row reading, at the root of the id it names.** -/
theorem encReached_rowRepr_of_viewRepr {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d) (hlit : ∀ l : Lit, d.UFRowRoot (Term.lit l))
    (hctors : ∀ (g : FnName) (cs : List Term) (v pv : Term),
      Term.app (viewName g) (cs ++ [v, pv]) ∈ d.terms → (g, cs.length) ∈ P.ctors) :
    ∀ {t e : Term}, ViewRepr d.toDatabase t e → ∀ {r : Term},
      d.UFRowReach e r → d.UFRowRoot r → RowRepr d t r
  | _, _, @ViewRepr.lit _ l, r, hr, hrr => by
      obtain ⟨s, -, -, huniq⟩ := encReached_ufRowRoot_unique hdom hsy htr h (Term.lit l)
      obtain rfl : r = Term.lit l :=
        (huniq r hr hrr).trans (huniq (Term.lit l) .refl (hlit l)).symm
      exact .lit
  | _, _, @ViewRepr.app _ f as es _ _ hl ho, r, hr, hrr => by
      obtain ⟨_, hfk, hrow⟩ := encReached_viewRow_at_root hdom hsy htr h hctors ho hr hrr
      obtain ⟨rs, hrs⟩ := encReached_exists_rootList hdom h es
      obtain ⟨_, hrow'⟩ :=
        encReached_viewRow_of_rowReachList hdom htr hsy hfi hcg h hfk hrow
          hrs.length_eq.symm (rootList_reach hrs)
      exact .app
        (encReached_rowReprList_of_viewReprList hdom hsy htr hfi hcg h hlit hctors hl hrs) hrow'

@[inherit_doc encReached_rowRepr_of_viewRepr]
theorem encReached_rowReprList_of_viewReprList {P : Program} (hdom : P.EncodeDomain)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    {d : FDatabase} (h : EncReached P d) (hlit : ∀ l : Lit, d.UFRowRoot (Term.lit l))
    (hctors : ∀ (g : FnName) (cs : List Term) (v pv : Term),
      Term.app (viewName g) (cs ++ [v, pv]) ∈ d.terms → (g, cs.length) ∈ P.ctors) :
    ∀ {ts es : List Term}, ViewReprList d.toDatabase ts es → ∀ {rs : List Term},
      List.Forall₂ (fun a r => d.UFRowReach a r ∧ d.UFRowRoot r) es rs → RowReprList d ts rs
  | _, _, .nil, _, hx => by cases hx; exact .nil
  | _, _, .cons ha hl, _, hx => by
      cases hx with
      | cons hh ht =>
        exact .cons
          (encReached_rowRepr_of_viewRepr hdom hsy htr hfi hcg h hlit hctors ha hh.1 hh.2)
          (encReached_rowReprList_of_viewReprList hdom hsy htr hfi hcg h hlit hctors hl ht)

end

/-- **The tuple choice at the run's end**, where the source run pays the two clauses the reached
state does not carry: `execM_ufLitRoots` for the literal and `execM_ctorsIn_of_mem_terms` for the
key width. -/
theorem execM_rowRepr_of_viewRepr {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (hsy : (encodeSig P).IsCtor symName) (htr : (encodeSig P).IsCtor transName)
    (hfi : (encodeSig P).IsCtor fiatName)
    (hcg : ∀ (g : FnName) (k : Nat), (g, k) ∈ P.ctors → k ≠ 0 → (encodeSig P).IsCtor (congrName k))
    (htgt : execM (encode P) = some tgt) {t e : Term} (hv : ViewRepr tgt.toDatabase t e)
    {r : Term} (hr : tgt.UFRowReach e r) (hrr : tgt.UFRowRoot r) : RowRepr tgt t r :=
  encReached_rowRepr_of_viewRepr hdom hsy htr hfi hcg (execM_encReached htgt)
    (execM_ufLitRoots hdom hsrc htgt)
    (fun _ _ _ _ hmem => execM_ctorsIn_of_mem_terms hdom hsrc htgt hmem) hv hr hrr

/-! ### The two source-side clauses, at a state the run passes through

`EncReached` carries everything the *target* invariants say and nothing the source run pays for.
The two facts left over — a literal being its own `@UF` row root, and a view entry naming a
source constructor at its own key width — both go through `FDatabase.SoundTerms`, and
`FDatabase.EncOk.stepCmd` is what advances that in lockstep with the source. `EncStep` is that
lockstep, and `EncStep.program` is exactly the `hP` the step lemma locates its command by. -/

/-- **`Database.CtorsIn` off a prefix of the program**, which is `ctorsIn_of_programStep` with
the run's own command list replaced by a sublist of it — `programStep_ctorsIn` was already
stated that way. -/
theorem ctorsIn_of_prefixStep {P : Program} (hdom : P.EncodeDomain) {p : Program}
    (hsub : ∀ c ∈ p, c ∈ P) {sd : Database} (hstep : ProgramStep Database.empty p sd) :
    sd.CtorsIn P :=
  (programStep_ctorsIn Database.CtorState.empty Database.empty_ctorsInState
    (fun c hc => Cmd.CtorsIn.of_domain hdom (hsub c hc))
    (fun c hc => hdom.ctorsOnly c (hsub c hc)) hstep).terms

/-- The commands already run are the program's own. -/
theorem EncStep.mem {P pre suf : Program} {sd : Database} {d : FDatabase}
    {G : List (Var × Expr)} (h : EncStep P pre suf sd d G) : ∀ c ∈ pre, c ∈ P :=
  fun _ hc => by rw [h.program]; exact List.mem_append_left _ hc

/-- **The globals the chain carries are the ones the substitution may be read through**: both
clauses, at every state of the chain, by `globalsInline_step` one block at a time. -/
theorem encStep_globals {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)} (h : EncStep P pre suf sd d G) :
    sd.GlobalsInline G ∧ P.GlobalsOnce G := by
  induction h with
  | prelude _ =>
      exact ⟨by intro v e he; exact absurd he (by simp [Expr.lookupG]),
        by intro v he; exact absurd he (by simp [Expr.lookupG])⟩
  | @block pre' suf' sd₀ sd₁ d₀ D₀ c G' n i hs hstep _ ih =>
      exact globalsInline_step hdom hs.program
        (hs.src.ctorState Database.CtorState.empty
          (fun c' hc' => hdom.ctorsOnly c' (by rw [hs.program]; exact List.mem_append_left _ hc')))
        hs.src hstep ih.1 ih.2

/-- **The completeness half's invariant at every state of the chain**, source and target
together. -/
theorem encStep_encOk {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)} (h : EncStep P pre suf sd d G) :
    d.EncOk P (encodeSig P) sd := by
  induction h with
  | prelude hprel => exact encOk_preludeState hdom hdom.aritiesAgree' hprel
  | @block pre' suf' sd₀ sd₁ d₀ D₀ c G' n i hs hstep hb ih =>
    obtain ⟨hgi, hgo⟩ := encStep_globals hdom hs
    exact ih.stepCmd hdom (encodedHeadSound hdom hdom.aritiesAgree' hdom.headsScoped)
      (encodedActionSound hdom hdom.aritiesAgree')
      (encodedWriteLegal hdom hdom.aritiesAgree') hs.program hs.src hstep hgi hgo hb

@[inherit_doc encStep_encOk]
theorem encStep_soundTerms {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) : d.SoundTerms sd :=
  (encStep_encOk hdom h).sound

/-- **A view entry names a source constructor at its own key width**, at a state the run passes
through. -/
theorem encStep_ctorsIn {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)} (h : EncStep P pre suf sd d G)
    {f : FnName} {es : List Term} {e pf : Term}
    (hmem : Term.app (viewName f) (es ++ [e, pf]) ∈ d.terms) : (f, es.length) ∈ P.ctors := by
  obtain ⟨as, hasrc, hcl, -⟩ := (encStep_soundTerms hdom h).1 f es e pf hmem
  rw [← hcl.length_eq]
  exact ctorsIn_of_prefixStep hdom h.mem h.src f as hasrc

/-- **No `@UF` entry is keyed on a literal it does not equal**, at a state the run passes
through. -/
theorem encStep_ufLitsIsolated {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) : d.UFLitsIsolated := by
  intro l b pf hmem
  exact (((encStep_soundTerms hdom h).2 _ _ _ hmem).eq_of_isLit
    (h.src.wf Database.WF.empty).litsIsolated (Or.inl rfl)).symm

/-- **And so a literal is its own `@UF` row root there.** -/
theorem encStep_ufLitRoots {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) (l : Lit) :
    d.UFRowRoot (Term.lit l) :=
  (encStep_ufLitsIsolated hdom h).ufRowRoot (encReached_eqsRefl hdom h.reached)
    (encReached_encBase hdom h.reached).inv.index
    (by rw [(encReached_encBase hdom h.reached).sig]; exact encodeSig_mergeOf_ufName hdom) l

/-- **The tuple choice at a state the run passes through, with nothing left over.**

This is what `Egglog.UnionsFire` is missing and what `execM_rebuildClosed` could not supply:
`ViewRepr` is what the command induction carries and `RowRepr` is what a firing reads, and at
the pointwise `@UF` row root they are the same claim. The four `Signature.IsCtor` carries are
discharged from `encodePrelude`'s own vocabulary at an arbitrary program, so the whole thing
asks for the domain and the chain and nothing else. -/
theorem encStep_exists_rowRepr {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) {t e : Term}
    (hv : ViewRepr d.toDatabase t e) : ∃ r, RowRepr d t r := by
  obtain ⟨r, hr, hrr⟩ := encReached_exists_ufRowRoot hdom h.reached e
  exact ⟨r, encReached_rowRepr_of_viewRepr hdom (encodeSig_isCtor_symName P)
    (encodeSig_isCtor_transName P) (encodeSig_isCtor_fiatName P)
    (fun _ _ hgk hk => encodeSig_isCtor_congrName hgk hk) h.reached
    (encStep_ufLitRoots hdom h) (fun _ _ _ _ hmem => encStep_ctorsIn hdom h hmem) hv hr hrr⟩

/-- **A run's own states are chain states**, source and target advancing together. -/
theorem encStep_encodeCmds {P : Program} :
    ∀ (p : Program) {pre : Program} {sd src : Database} {d D : FDatabase}
      {G : List (Var × Expr)},
      EncStep P pre p sd d G → ProgramStep sd p src →
      ∀ (n i : Nat), d.execProgramM (encodeCmds P G p n i).1 = some D →
        ∃ G', EncStep P (pre ++ p) [] src D G' := by
  intro p
  induction p with
  | nil =>
    intro pre sd src d D G h hsrc n i hrun
    obtain rfl := hsrc.nil_inv
    rw [show (encodeCmds P G ([] : Program) n i).1 = ([] : Program) from rfl,
      FDatabase.execProgramM, Option.some.injEq] at hrun
    rw [List.append_nil]
    exact ⟨G, hrun ▸ h⟩
  | cons c cs ih =>
    intro pre sd src d D G h hsrc n i hrun
    obtain ⟨sd', hstep, hrest⟩ := hsrc.cons_inv
    rw [encodeCmds_cons_fst] at hrun
    obtain ⟨d₁, hb, hafter⟩ := FDatabase.execProgramM_append hrun
    obtain ⟨G', hnext⟩ := ih (.block h hstep hb) hrest _ _ hafter
    rw [List.append_assoc, List.cons_append, List.nil_append] at hnext
    exact ⟨G', hnext⟩

@[inherit_doc encStep_encodeCmds]
theorem execM_encStep {P : Program} {src : Database} {tgt : FDatabase}
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt) :
    ∃ G, EncStep P P [] src tgt G := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  obtain ⟨G, h⟩ := encStep_encodeCmds P (.prelude hprel) hsrc 0 0 hcmds
  rw [List.nil_append] at h
  exact ⟨G, h⟩

/-- **Non-vacuous at the run**: the chain reaches the run's end, so every source term the
invariant reads there has a row reading too — with the four `Signature.IsCtor` carries and both
source-side clauses discharged, which is what `execM_rowRepr_of_viewRepr` still takes by hand. -/
theorem execM_exists_rowRepr {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {t e : Term} (hv : ViewRepr tgt.toDatabase t e) :
    ∃ r, RowRepr tgt t r :=
  let ⟨_, h⟩ := execM_encStep hsrc htgt; encStep_exists_rowRepr hdom h hv

/-! ### And the reading is a function, because the state is rooted

`Database.ViewLeader` — a representative for the reading through **entry terms** — is false in
general at states this development reaches (`chainD_not_viewLeader`), and the reason is that an
entry a merge displaced is never removed, so `Database.Out` keeps reading it: at `chainD` the
ids ascend with upper bounds everywhere and no top, and there is no representative to pick.

Through live **rows** the same claim holds, and the difference is exactly rootedness. A state
an encoded block runs at is one a `Cmd.saturate rebuildRuleset` left, so a live view row's
e-class column has no outgoing `@UF` row (`encReached_viewRowsRooted`), a view key carries at
most one row (`encReached_viewRowUnique`), and entry-level `@UF` reachability lands on one row
root (`encReached_ufRowRoot_of_ufReach`). Tops exist, so the upper bound *is* a representative
— and `uTgt_not_viewLeader` against `uRebuilt_viewLeader` is the same bracket one rebuild
firing apart. `ncTgt_rowJoined_edge` is the instance: `(B)` reads to `(B)` and to `(A)` through
entries and to `(A)` alone through rows. -/

/-- **A live view row names a source constructor at its own key width.** `FDatabase.IndexOk`
turns the row into its entry term — `ctor` forces the row's function to carry a `:merge`, since
its output columns are not empty, and `entry` then reads the entry off `terms` — and
`encStep_ctorsIn` is the source-side half at that entry. -/
theorem encStep_ctorsIn_of_row {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)} (h : EncStep P pre suf sd d G)
    {f : FnName} {es : List Term} {e pf : Term}
    (hrow : (⟨viewName f, es, [e, pf]⟩ : Row) ∈ d.rows) : (f, es.length) ∈ P.ctors := by
  have hidx := (encReached_encBase hdom h.reached).inv.index
  have hmg : d.sig.mergeOf (viewName f) ≠ none := by
    intro hc
    have h0 := (hidx.ctor ⟨viewName f, es, [e, pf]⟩ hrow hc).1
    exact absurd h0 (by simp)
  obtain ⟨bs, hcl, hmem⟩ := hidx.entry ⟨viewName f, es, [e, pf]⟩ hrow hmg
  obtain rfl : es = bs :=
    CongList.eq_of_eqsRefl (encReached_eqsRefl hdom h.reached).toDatabase hcl
  exact encStep_ctorsIn hdom h (FDatabase.mem_toDatabase_terms.mp hmem)

/-- **The `:merge` carry, at a state the run passes through.** A live view row's function is a
merge function, because its output columns are not empty and `FDatabase.IndexOk.ctor` would
force them to be. This is the side condition `RowRead.app` carries. -/
theorem encStep_mergeOf_of_row {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)} (h : EncStep P pre suf sd d G)
    {f : FnName} {es : List Term} {e pf : Term}
    (hrow : (⟨viewName f, es, [e, pf]⟩ : Row) ∈ d.rows) :
    (d.sig.mergeOf (viewName f)).isSome = true := by
  rcases hmg : d.sig.mergeOf (viewName f) with _ | m
  · have h0 := ((encReached_encBase hdom h.reached).inv.index.ctor
      ⟨viewName f, es, [e, pf]⟩ hrow hmg).1
    exact absurd h0 (by simp)
  · rfl

/-- **Every id the reading produces is an `@UF` row root**, which is the whole of what
rootedness buys: `FDatabase.ViewRowsRooted` at an application and `encStep_ufLitRoots` at a
literal. -/
theorem encStep_rowRepr_root {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) {t r : Term}
    (hr : RowRepr d t r) : d.UFRowRoot r := by
  cases hr with
  | lit => exact encStep_ufLitRoots hdom h _
  | app _ hrow =>
      exact encReached_viewRowsRooted hdom (encodeSig_isCtor_symName P)
        (encodeSig_isCtor_transName P) h.reached _ _ (encStep_ctorsIn_of_row hdom h hrow)
        _ _ _ hrow

/-- **One term, one id**, at a state the run passes through: `rowRepr_unique` at the merge
fixpoint's own view-key clause. -/
theorem encStep_rowRepr_fn {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) {t r s : Term}
    (h₁ : RowRepr d t r) (h₂ : RowRepr d t s) : r = s :=
  rowRepr_unique (fun f as e₁ pf₁ e₂ pf₂ hr₁ hr₂ => by
    have hu := encReached_viewRowUnique hdom (encodeSig_isCtor_symName P)
      (encodeSig_isCtor_transName P) h.reached f as.length
      (encStep_ctorsIn_of_row hdom h hr₁) as [e₁, pf₁] [e₂, pf₂] hr₁ hr₂
    exact (by simpa using hu : _ ∧ _).1) h₁ h₂

/-- **The reading is the root of any id the entries record**, which is `RowRepr` and `ViewRepr`
identified: `encReached_rowRepr_of_viewRepr` answers the entry at the root, and the reading is a
function, so the two answers are the same term. -/
theorem encStep_rowRepr_eq_root {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) {t e r ρ : Term}
    (hv : ViewRepr d.toDatabase t e) (hr : RowRepr d t r)
    (hρ : d.UFRowReach e ρ) (hρr : d.UFRowRoot ρ) : ρ = r :=
  encStep_rowRepr_fn hdom h
    (encReached_rowRepr_of_viewRepr hdom (encodeSig_isCtor_symName P)
      (encodeSig_isCtor_transName P) (encodeSig_isCtor_fiatName P)
      (fun _ _ hgk hk => encodeSig_isCtor_congrName hgk hk) h.reached
      (encStep_ufLitRoots hdom h) (fun _ _ _ _ hmem => encStep_ctorsIn hdom h hmem) hv hρ hρr)
    hr

/-- **The derived clause, discharged.** `fn` is `rowRepr_unique` at
`FDatabase.ViewRowUnique`; `edge` is the root argument — each side's reading is the root of the
id its entry recorded, and an `@UF` entry edge puts the two ids in one component, whose root is
unique. Neither clause is `Database.ViewLeader`, which the same states refute. -/
theorem encStep_rowJoined {P : Program} (hdom : P.EncodeDomain) {pre suf : Program}
    {sd : Database} {d : FDatabase} {G : List (Var × Expr)}
    (h : EncStep P pre suf sd d G) : d.RowJoined where
  fn := fun _ _ _ h₁ h₂ => encStep_rowRepr_fn hdom h h₁ h₂
  edge := by
    intro x y pf t u r s hout hvt hvu hrt hru
    obtain ⟨ρx, hρx, hρxr⟩ := encReached_exists_ufRowRoot hdom h.reached x
    obtain ⟨ρy, hρy, hρyr⟩ := encReached_exists_ufRowRoot hdom h.reached y
    have hxr : ρx = r := encStep_rowRepr_eq_root hdom h hvt hrt hρx hρxr
    have hys : ρy = s := encStep_rowRepr_eq_root hdom h hvu hru hρy hρyr
    rw [← hxr, ← hys]
    exact encReached_ufRowRoot_of_ufReach hdom (encodeSig_isCtor_symName P)
      (encodeSig_isCtor_transName P) h.reached
      (Database.UFStep.toReach ⟨pf, hout⟩) ρx ρy hρx hρxr hρy hρyr

/-- **`Egglog.RowMech`, discharged.** The three clauses `Egglog.UnionsFire` takes about rows, at
every state one encoded run passes through: `encStep_exists_rowRepr` is the tuple choice — a
reading is a row reading, at the pointwise `@UF` row root — `ViewRepr.of_rowRepr_of_indexOk`
is the way back, off `FDatabase.IndexOk` alone, and `encStep_rowJoined` is the reading being a
function that collapses an `@UF` edge.

This is what `execM_rebuildClosed` could not be asked for. Its `edged` clause is stated at an
`execM` target and `UnionsFire` quantifies over the state the *next* block runs at, so the
mechanism had to be restated one block short of the end; `EncStep` is that restatement, and the
`encReached_*` family is the block inductions consuming it. Nothing was added to `UnionsFire`
that a firing cannot be handed — `unionsJoined_fire_satisfiable` carries all three clauses at
the witness state, non-vacuously and at positive arity. -/
theorem encStep_rowMech {P : Program} (hdom : P.EncodeDomain) : RowMech P :=
  fun h => ⟨fun _ _ hv => encStep_exists_rowRepr hdom h hv,
    fun _ _ hr =>
      ViewRepr.of_rowRepr_of_indexOk (encReached_encBase hdom h.reached).inv.index hr,
    encStep_rowJoined hdom h⟩

/-- **The residue of obligation `trans`, of the rebuild half of obligation `assert`'s `union`
case, and of the *key* half of obligation `congr`, at the rules it fires.**

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

* **The bridge**, run-wide: every merge-function entry term has a current row at its own key
  whose e-class column is `@UF`-reachable from the entry's. **Proved**, as `execM_entryRowsUF`.
  `FDatabase.IndexCurrent` is that claim without
  the "up to `@UF`", and `cxTgt_not_indexCurrent` refutes it; the weakened claim survives that
  very state, and `cxTgt_currentUF` is the compiled instance — the row the merge kept sits at
  the `@UF` parent of the entry it displaced.
* **The fixpoint's roots**: at a `FDatabase.RowsClosed` state no surviving view row's e-class
  column has an outgoing `@UF` row, since the e-class rule's own firing displaces it and the row
  list would move. One step, and the firing is now exhibited — `eclassRule_fires`, over
  `mem_matchQuery_of_lookup`, which is `cxRb_mem_matchQuery` generalised — together with
  `mergeResult`'s `ordering-min`. `no_ufRowEdge_of_rowsClosed`'s fourth hypothesis,
  `FDatabase.RowColumnsValued`, is `execM_rowColumnsValued`.
* **The `@UF` rows are a forest**, so that root is *unique* and every reader of an id therefore
  lands on the same one. `ufDecl`'s `identityVals := some 1` makes two rows at one key agree in
  their e-class column at a merge fixpoint, and every edge a `union` or `mergeBody` writes runs
  `ordering-max ↦ ordering-min`, so a row path strictly descends `Term.blt` inside a finite
  list.

The third is what the leader form of the clause had no way to reach and the landing-site form
does: two terms reading one id are two rows displaced independently, but at a fixpoint over a
forest both displacements end at the same root, and that root is a `Database.Lands` of the id.

**The third obligation's own argument is proved, and so is the fixpoint mechanism the second
and the first both spend.** In `Encoding/Correspond.lean`, at the merge phase:

* `FDatabase.exists_ufRowRoot` and `ufRowRoot_unique` are the forest: descent along
  `FDatabase.UFRowEdge` bounds a path by the `@UF` rows below its start and `rows` is a finite
  list, so a root exists; one outgoing edge per key makes it unique.
* **Both hypotheses are discharged**, at the state `execM` returns.
  `FDatabase.UFRowsDescend` is `execM_ufRowsDescend`, the run-wide induction over the three
  writers of an `@UF` row; `FDatabase.UFRowsForest` is `execM_encode_ufRowsForest`, whose
  state-level content is `ufRowsForest_of_settled`. `execM_ufRowRoot_unique` is the two of them
  together: every id of an encoded target reaches a **unique** `@UF` row root.
* `FDatabase.row_unique_of_settled` is the same fixpoint argument at the **views**: a
  `FDatabase.settled` state carries at most one row per view key, because
  `FDatabase.mergeOneOriented` deletes the arriving row of a collision whether or not the body
  runs, no firing anywhere adds a row at a view key, and `rebuild_diag` says the pass fires on
  the rows it started with. This is what identifies the two rows the bridge produces for two
  entries at **one** key, and what the second obligation contradicts against; the `@UF` version
  needed `ufMeasure`, since `mergeBody` writes into `@UF` and the per-key count is therefore no
  measure there.

**And one condition the three obligations do not name, now carried**:
`no_ufRowEdge_of_rowsClosed` reads a rebuild **fixpoint** — `FDatabase.RowsClosed`,
`FDatabase.settled`, and a round that returns — and `encode` emits `Cmd.saturate rebuildRuleset`
after an action, a run and a saturate but after neither a `Cmd.rule` nor a `Cmd.decl`
(`encodeCmd`), so a program ending in one of those two leaves a target no fixpoint lemma reaches
directly. `FDatabase.ViewRowsRooted` is the property stated over `rows` alone, which is what the
two writers with no rebuild after them carry by a rewrite, and `execM_viewRowsRooted` is it at
the state `execM` returned. `FDatabase.settled` costs the carry nothing:
`FDatabase.runSaturateM_settled'` reads the merge fixpoint off the branch a saturating run
returned from, with no hypothesis about the state that run started at.

**The second obligation is discharged, and it is reduced to the firing.**
`no_ufRowEdge_of_rowsClosed` is it, and **the firing is discharged**:
`eclassRule_fires` exhibits the e-class rule's conclusion as a row of the round's rule phase, the
merge phase leaves a row at that key whose e-class column is `Term.blt`-at or below the one the
firing wrote (`mergeSaturateF_rowsDescendCarry`, `mergeResult`'s `ordering-min` carried across a
pass and across the phase), `FDatabase.RowsClosed` and `row_unique_of_settled` identify that row
with the one the fixpoint started from, and `FDatabase.UFRowsDescend` plus `Term.blt_asymm` close
it. `FDatabase.UFRowEdge` excludes a self-loop, which is what `(union a a)` writes and what the
claim would otherwise be false at.

**What the firing cost.** All four are now paid.
`mem_matchQuery_of_lookup` is `matchQuery` completeness in general form —
`cxRb_mem_matchQuery`'s one instance generalised, naming `Query.freeVars`' order and composing
`Env.canon` with itself (`Env.canon_canon`), with `toString_nat_inj` for the key variables being
distinct. `FDatabase.EncBase.held` is the **converse** of `FDatabase.RulesEncoded`, that the
maintenance rules are rules the target holds, carried along the run by
`FDatabase.execProgramM_mem_rules` and the monotonicity of `rules`.
`FDatabase.EncBase.noAtEnv` is that the target's environment binds no `@`-prefixed variable, so
that `Query.freeVars` is the whole of the query's variables — `Program.EncodeDomain.noAt` at the
source (`Program.names` includes `P.vars`), `noAtLet_encodeCmd` at each emitted command, and
`FDatabase.execCmdM_noAtEnv` along the run. The fourth is placing the columns in
`FDatabase.valueTerms`, which `FDatabase.RowColumnsValued` names and `execM_rowColumnsValued`
discharges: a `Term.app` reaches `terms` only through `Expr.eval`, whose application case is
guarded by `Signature.IsCtor` — a declared name with no `:merge` — so every term an action
evaluates is a value, and `FDatabase.Valued` carries that over the writers `FDatabase.addRow`
mints entry terms with.

**All three obligations hold, and the identification they were waiting on is discharged.** The
bridge answers a view entry with a live row whose e-class column the union-find reaches from the
entry's, and that reach is `Database.UFReach`, over `@UF` **entry terms**: the row that
witnessed a step may since have been displaced, which is what `cxTgt_not_indexCurrent` refutes
and why the bridge is stated this way. The fixpoint's roots and the forest are stated over
`FDatabase.UFRowEdge`, over `@UF` **rows**. So the bridge hands each reader of an id a root it
reaches by *entries* and `execM_ufRowRoot_unique` makes the root reachable by *rows* unique;
`execM_ufRowRoot_of_ufReach` is what identifies the two, and `Database.Absorbs` is where that
bites, since it quantifies over every term that reads the id.

**What the identification cost was `FDatabase.UFTermsDescend`, and it is now a theorem.**
`execM_ufTermsDescend` is it: every `@UF` entry term of the target runs
`ordering-max ↦ ordering-min` whether or not its row survived, because **descent is a property
of the write and not of currency** — `FDatabase.addRow` mints the entry term for the very row it
writes and no writer removes a term. The induction is `execM_ufRowsDescend`'s writer for writer,
with `Action.EntrySafe` added at each: an action records the *subterms* of what it evaluates, so
the entry terms it records other than its own `set`'s have to be ones the state already holds.
`mergeBody` needs no case of its own — it **is** the `union` head's shape
(`mergeBody_ufWriteSafe`, `mergeBody_entrySafe`) — and `pathCompressRule` reads rows, so the
induction carries `FDatabase.UFRowsDescend` alongside.
**Confluence is not needed on top of descent**: the bridge already answers each entry with a row
at the entry's own key, so the induction only has to walk the chain the bridge hands back, and
`FDatabase.UFTermEdge.measure_lt` is what bounds that walk inside the finite list `terms`.
Mathlib carries no Newman's lemma over a well-founded relation, and `Relation.church_rosser` is
the strong `ReflGen` diamond; neither is wanted here.

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

**And the rest of the bridge was inductive**, which is why this was the case worth checking:
every other writer only adds. `FDatabase.addRow` writes the row for the entry term it mints, so
a new entry is current reflexively; `execRunRules` unions firings in and removes nothing;
`FDatabase.union` and `FDatabase.addTerm` touch no row. What those writers *do* owe is that they
record no entry term they write no row for, and that is syntactic in the action
(`Action.EntrySafe`) — so the bridge is a per-command induction over `FDatabase.EncBase`, and
`execM_entryRowsUF` is it run.

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

**The source run is a hypothesis because the property is false without it, and
`ltuProgram` is the program.** `Program.EncodeDomain.noLitUnion` reads rule heads only — a
*top-level* `union` on a literal was left to the source run, which sticks on it — while
`encodeBuild` gives a literal itself as its id, so `encodeAction`'s `union` head writes an `@UF`
entry between two distinct literals and `execM` returns. `ViewRepr d (.lit l) (.lit l)` holds at
every state with no premise, so `Database.Absorbs (.lit l) e` forces `e = .lit l` and `eclass`
asks for a point that is two different literals at once:
`Encoding/Correspond.lean`'s `not_rebuildClosed_of_out_uf_lits` is the clause against that entry
and `execM_viewJoined_false` is it at the target of a program every clause of the domain admits.
`ProgramStep Database.empty P src` is the repair rather than a tenth domain clause, since it is
what every consumer of this theorem already carries and what the encoder was excused from
checking. **What it owes the proof** is `FDatabase.UFLitsIsolated`, the target-side reading of
`Database.WF.litsIsolated`: no `@UF` entry of the target is keyed on a literal it does not equal.

**The vacuity mechanism is checked and half the clause is paid.** `ltuProgram_no_programStep` is
the mechanism — `evalAction` refuses a `union` on a literal, `cmdReach` at a `Cmd.action` *is*
`evalAction`, so `ltuProgram` has no source state and the claim is about nothing there — and
`cmdStep_union_notLit` is the same refusal read forwards at any successful step.
`ufLitsIsolated_of_no_lit_lit` pays the **key** half out of `execM_ufTermsDescend`: `Term.blt`
orders literals below applications, so an `@UF` entry out of a literal points at a literal and
the clause reduces to "no `@UF` entry between two **distinct** literals".
`FDatabase.UFLitsIsolated.ufRowRoot` is the reading `Database.Absorbs` consumes at a literal.

**What is left of it is the *value* half, and the writers to check are four rather than three.**
An `@UF` entry between two literals could come from a top-level source `union`, from a rule
head (excluded by `Program.EncodeDomain.noLitUnion`), from `mergeBody`, or — the writer the
three-way reading misses — from `pathCompressRule`, whose head copies an existing row's value.
And `mergeBody` runs at `@UF`'s own table as well as at a view's, so "the e-class column is
always the skolem `.app f es`" covers one of its two instances and not the other.

**The first of the four is paid.** `union_target_notLit` is it: `cmdStep_union_notLit` is the
source's own refusal, `encodeBuild_fst` makes the encoded block evaluate the source's own two
expressions, `execM_env` — the environment alignment, now standalone, its own command
induction carrying `Database.CtorState` and nothing about equalities — makes it do so in the
source's own environment, and `Expr.eval_sigIndep` says the two signatures cannot disagree
about the value. `union_out_uf_notLit` is the same at the `@UF` entry the block writes, and
`uSrc_union_target_notLit` is it at a top-level `union` a program actually runs, transported
to the *encoded* signature. So this residue no longer waits on `unionsJoined_fire` either.

**What is left is the other three**, as a run-wide invariant with two clauses — no `@UF` row
records a literal value, and no view row records a literal e-class column — which are mutually
recursive across `mergeBody` and the e-class rebuild rule. Its induction is
`execM_ufTermsDescend`'s, writer for writer, and none of it is written.

**And a side condition the clauses read but nothing stated, now discharged.** The `app` case
of `Database.Absorbs` reads a view entry the target holds and then applies the *rules* to it,
and every one of those is keyed on `tgt.sig (viewName f) = some (viewDecl k)` — that a view
head the target holds an entry of is a source constructor, at the entry's own key width.
`execM_viewDecl_of_mem_terms` is it, and it is not a new invariant on the target: the chain is
the completeness half's own. `execM_soundTerms` answers a view entry term with a *source*
application at the entry's key width (`EntrySound`), and `ctorsIn_of_programStep` says every
application a source run holds is one the program makes — `Database.CtorsInState`, which is
`Database.NoLits`' shape and carried for its reason, a firing evaluating a head the state
carries rather than one the command names. `encodeSig_tables` closes it, and
`execM_mergeOf_viewName_of_mem_terms` is the `:merge` every reader of a view row spends.
`rbProgram_viewDecl_W` is the chain end to end at positive arity.

**The mechanism `edged` and `column` were waiting on is landed**, and it separates the two.
With the identification in hand every clause answers with the **`@UF` row root** of the id it is
given: `Database.Lands a (root a)` is `FDatabase.UFRowEdge.toUFStep` for the reachability and,
for the absorption, the bridge at each reader's own view key — the live row it answers with has
an e-class column that `execM_viewRowsRooted` makes a root and `execM_ufRowRoot_of_ufReach`
identifies with `root a`. `eclass` is then immediate, since an `@UF` entry's two ends have one
root. `edged` is not: two readings of one source term sit at two id tuples `es₁` and `es₂` that
agree **rootwise**, and identifying the two rows' e-class columns needs both keys moved onto the
common root tuple. `execM_viewRow_of_rowReachList` is that move — `columnRule_fires` at one
column, `viewRowsColumnClosed_of_roundFixed` at the fixpoint, `execM_viewRowsColumnClosed`
run-wide, `execM_columnRow_step` making the e-class column exact rather than merely reachable —
and it is stated for a key tuple, which is the shape asked for and **not** "a key column is a
root": rows at superseded keys are never deleted, only a collision at *one* key removes one, so
a live view row's key column need not be a root and the column rule's conclusion sits at a
*different* key from its premise. That is why the descent contradiction that closes
`no_ufRowEdge_of_rowsClosed` has no counterpart here, and why the closure is what the fixpoint
delivers in its place.

**And both clauses are now closed, at the root the walk delivers.** The obstruction was that
the walk is stated over `FDatabase.UFRowReach`, over live `@UF` **rows**, while the clauses are
stated over `Database.Lands`, whose reachability half is `Database.UFReach`, over `@UF`
**entries** — and `execM_ufRowRoot_of_ufReach` identifies the two only at their *roots*. So
`edged` was pointed where it needed to be and `column`, quantified over every landing site,
additionally owed that an arbitrary one of a live key column is itself an `@UF` row root, which
`Database.Absorbs` cannot give: it is an entry-level property and `Database.Out` reads entry
terms, which are never removed.

`Database.LandsRoot` names the root in the clauses and that obligation vanishes.
`execM_rebuildColumn` is `column`, out of the bridge and
`execM_viewRow_of_rowReachList` at a tuple the clause now says is rooted; `execM_rootAgree` is
`edged`'s root agreement, the two walks landing at one key and `execM_viewRowUnique` — the
run-wide merge-fixpoint carry, `FDatabase.row_unique_of_settled` pushed across the blocks that
run no rebuild — identifying the rows there. `execM_rebuildClosed_of_ufLitRoots` is all three
clauses assembled.

**And its last hypothesis and its four carries are discharged, so nothing is left.** The
hypothesis is the *literal reader*: `ViewRepr d (.lit l) a` forces `a = .lit l` with no premise
at all, so `Database.Absorbs` asks that a literal be its own root, and `execM_ufLitRoots` is it
— the entry-valued clause outright, not the rows-only weakening, since `FDatabase.SoundTerms`
answers an `@UF` entry term with a source congruence and `Cong.eq_of_isLit` makes a literal's
class a singleton there. That covers all four writers at once, `mergeBody` at both its tables
and `pathCompressRule` included, and it is why no run-wide two-clause invariant was needed. The
carries are `Signature.IsCtor` at `@Sym`, `@Trans`, `@Fiat` and `congrName k`, which
`encode_corresponds` does not take and does not have to: `encodeSig_isCtor_symName` and its
three companions read them off `encodePrelude`'s own vocabulary at an arbitrary program.

**Non-vacuous, and still failing where it must**: `satTarget_rebuildClosed` is the degenerate
state, `Encoding/Match.lean`'s `uRebuilt_rebuildClosed` the one with a real `@UF` edge — where
`eclass` and `edged` both do work — `ncTgt_rebuildClosed` the one with a positive-arity key in
`column`, and `uTgt_not_rebuildClosed` is the same property one rebuild firing earlier, where it
fails because `uTgt_not_viewJoined` does, at *every* rootness notion. All three positive
witnesses are proved at `Database.RebuildClosedStrong` and transported by
`Database.RebuildClosed.of_strong_ufRoot`, which is what says the weakening is a weakening and
names the root while doing it — `Database.RebuildClosed.of_strong` is the same check at the
unrooted instance, which is the clause set before the restatement.
`cxStale_not_rebuildClosedStrong` is where the two forms come apart. -/
theorem execM_rebuildClosed {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.RebuildClosed tgt.UFRowRoot :=
  execM_rebuildClosed_of_ufLitRoots hdom hsrc (encodeSig_isCtor_symName P)
    (encodeSig_isCtor_transName P) (encodeSig_isCtor_fiatName P)
    (fun _ _ hgk hk => encodeSig_isCtor_congrName hgk hk) htgt
    (execM_ufLitRoots hdom hsrc htgt)

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

**And the source run, for the reason `execM_rebuildClosed` takes it**: `ufJoin` is false at an
`@UF` entry between two distinct literals, which a top-level `union` on literals writes and
which `Program.EncodeDomain` does not exclude (`execM_viewJoined_false`).

**Non-vacuous at three states, with every clause doing work at one of them**:
`satTarget_viewJoined` (the degenerate one), `Encoding/Match.lean`'s `uRebuilt_viewJoined` (a
real `@UF` edge in `ufJoin`, two ids for one term in `ids`) and `ncTgt_viewJoined` (positive
arity in `rowShared`, at the key the `union` moved) — with `ncTgt_rowShared_FB_FA` and
`ncTgt_ids_B` the two clauses at named instances with every hypothesis inhabited. -/
theorem execM_viewJoined {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.ViewJoined :=
  (execM_rebuildClosed hdom hsrc htgt).toViewJoined

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
  Database.ViewsCover.of_viewJoined (execM_viewJoined hdom hsrc htgt)
    (unionsInv_execM unionsJoined_fire hdom (encStep_rowMech hdom) hsrc htgt).reads

@[inherit_doc execM_viewsCover]
theorem execM_viewsCover_shared {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) :
    ∀ f as bs, Term.app f as ∈ src.terms → List.Forall₂ (SameClass tgt.toDatabase) as bs →
      ∃ es e pf, ViewReprList tgt.toDatabase as es ∧ ViewReprList tgt.toDatabase bs es ∧
        tgt.toDatabase.Out (viewName f) es [e, pf] :=
  (execM_viewsCover hdom hsrc htgt).shared

/-- **The residue of obligation `assert`'s `union` half**, assembled from the `union`'s own
write and the rebuild that follows it — and from nothing about the source's terms, which is
what `ncTgt_not_readsSelf` costs. `UnionsRead` itself holds at that counterexample
(`ncTgt_unionsRead`); it is the factorisation through `Database.ReadsSelf` that did not. -/
theorem execM_unionsRead {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) : tgt.toDatabase.UnionsRead src :=
  unionsRead_of_viewJoined (execM_viewJoined hdom hsrc htgt)
    (execM_unionsJoined unionsJoined_fire hdom (encStep_rowMech hdom) hsrc htgt)

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
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b c : Term) (hab : SameClass tgt.toDatabase a b) (hbc : SameClass tgt.toDatabase b c) :
    SameClass tgt.toDatabase a c :=
  SameClass.trans_of_viewJoined (execM_viewJoined hdom hsrc htgt) hab hbc

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

/-- **The correspondence.** `difftest correspond 64` runs exactly this claim over the 83
in-domain cases and the seventeen probes, through `sameClassF` and `closureF`, and reports
83 agreeing, 0 LOST, 0 INVENTED and `link-diff` 0 — the last is what says the swept relation is
this one.

**The eight `glob-*` cases are the ones that measure the globals.** A `let`-bound global read
from a rule's **query**, and a `union` that makes the bound term the loser: the encoding used to
ask for a live `@FView` row keyed at a term the rebuild's column rules only ever carry rows
*away* from, and six of them reported 7 LOST — this theorem's own conclusion failing at an
`execM` run. `Rule.substGlobals` is the repair (`unionsJoined_fire`'s `hglob` paragraph), and
all eight agree now, the `glob-keyed` and `glob-leader` controls included.

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
