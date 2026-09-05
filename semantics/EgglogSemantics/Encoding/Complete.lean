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
theorem noAtLet_encodeCmd {P : Program} (hdom : P.EncodeDomain) (c : Cmd) (hc : c ∈ P)
    (n i : Nat) : ∀ c' ∈ (encodeCmd c n i).1, c'.NoAtLet := by
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

/-- **`rules` only ever grows.** `Cmd.rule` is the one writer that extends it and no writer
removes from it — the same case analysis `FDatabase.execCmdM_rulesEncoded` is, read in the
other direction. -/
theorem execCmdM_rules_mono {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    ∀ r ∈ d.rules, r ∈ d'.rules := by
  intro r hr
  cases c with
  | action a =>
      rw [FDatabase.execCmdM] at hs
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
      rw [(FDatabase.mergeSaturateF_fields h₂).2.2, FDatabase.execAction_rules h₁]
      exact hr
  | rule s =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs
      exact List.mem_cons_of_mem s hr
  | run R =>
      rw [FDatabase.execCmdM] at hs
      rw [(FDatabase.runRoundM_fields hs).2.2]
      exact hr
  | saturate R =>
      rw [FDatabase.execCmdM] at hs
      rw [(FDatabase.runSaturateM_fields runFuel hs).2.2]
      exact hr
  | decl f dc =>
      rw [FDatabase.execCmdM, Option.some.injEq] at hs
      subst hs
      exact hr

@[inherit_doc execCmdM_rules_mono]
theorem execProgramM_rules_mono {p : Program} :
    ∀ {d D : FDatabase}, d.execProgramM p = some D → ∀ r ∈ d.rules, r ∈ D.rules := by
  induction p with
  | nil =>
    intro d D hs r hr
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ hr
  | cons c cs ih =>
    intro d D hs r hr
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact ih h₂ r (execCmdM_rules_mono h₁ r hr)

/-- **And every `Cmd.rule` of the block registers its rule.** With the monotonicity above this
is the converse of `execProgramM_rules_of_declOrRule`: what the prelude emits, the state after
it holds. -/
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
        (hwlP c hcP n i _ hmem) (noAtLet_encodeCmd hdom c hcP n i _ hmem) hs
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
      refine FDatabase.EncBase.execProgramM (P := P) (sg := sg) ?_ ?_ ?_ ?_ ?_ hok.base hblock
      all_goals
        intro c' hc'
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
        have hmem : Cmd.action b ∈ (encodeCmd (Cmd.action a) n i).1 :=
          List.mem_append_left _ (List.mem_map_of_mem hb)
      · trivial
      · exact encodeCmd_unionFree (Cmd.action a) n i _ hmem
      · exact noDecl_encodeCmd (Cmd.action a) n i _ hmem
      · exact hwlP (Cmd.action a) hcP n i _ hmem
      · exact noAtLet_encodeCmd hdom (Cmd.action a) hcP n i _ hmem
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
        empty_noUnions hprel, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact FDatabase.execProgramM_rulesEncoded (rulesEncodedOk_encodePrelude P)
      (fun r hr => absurd hr (by simp [FDatabase.empty])) hprel
  · rw [← hsig]
    exact FDatabase.execProgramM_mergeShape (mergeShapeOk_encodePrelude P)
      Signature.mergeShape_empty hprel
  · intro r hr
    rcases execProgramM_rules_of_declOrRule hprel r hr with hc | hc
    · exact hmaint r (mem_maintenanceRules_of_encodePrelude hc)
    · exact absurd hc (by simp [FDatabase.empty])
  · exact fun r hr => FDatabase.execProgramM_mem_rules hprel r
      (by rw [encodePrelude]; exact List.mem_append_right _ (List.mem_map_of_mem hr))
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
theorem mem_encodeCmd_of_mem_encodeCmds {P : Program} : ∀ (p : Program), (∀ c ∈ p, c ∈ P) →
    ∀ (n i : Nat), ∀ c' ∈ (encodeCmds p n i).1,
      ∃ c, c ∈ P ∧ ∃ (m j : Nat), c' ∈ (encodeCmd c m j).1
  | [], _, _, _ => by simp [encodeCmds]
  | c :: cs, hp, n, i => by
      intro c' hc'
      rw [encodeCmds_cons_fst] at hc'
      rcases List.mem_append.mp hc' with h | h
      · exact ⟨c, hp c List.mem_cons_self, n, i, h⟩
      · exact mem_encodeCmd_of_mem_encodeCmds cs
          (fun x hx => hp x (List.mem_cons_of_mem c hx)) _ _ c' h

/-- **The `union` head is the only `set` at `@UF` a block emits.** -/
theorem ufWriteOk_encodeCmd (c : Cmd) (n i : Nat) : ∀ c' ∈ (encodeCmd c n i).1, c'.UFWriteOk := by
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
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) 0 0) (encodeCmds_unionFree P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hdes₀ hcmds
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noDecl_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ m j c hmem
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact ufWriteOk_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noAtLet_encodeCmd hdom c₀ hc₀ m j c hmem

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
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) 0 0) (encodeCmds_unionFree P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hdes₀ hfor₀ hcmds
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noDecl_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ m j c hmem
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact ufWriteOk_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noAtLet_encodeCmd hdom c₀ hc₀ m j c hmem

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
    (hmem : Cmd.rule s ∈ P) (i n : Nat) :
    ∀ a ∈ (encodeRule i s n).1.actions, a.EntrySafe := by
  obtain ⟨-, hnv, -⟩ := hdom.queryEncodable_of_mem hmem
  rw [encodeRule_actions]
  refine encodeActions_entrySafe hdom
    (notEntryHead_ruleE (queryProofs_var (encodeQuery_valueVars s.query hnv n))) s.actions
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
  rcases hb.rules r hrm with ⟨s, i, n, hmem, rfl⟩ | hmaint
  · exact encodeRule_entrySafe hdom hmem i n
  · exact maintenance_entrySafe hmaint

/-- **Whether a command can record an entry term the bridge would have to answer for.** Only a
top-level action can; a `.rule`, a `.run` and a `.saturate` write through `d.rules`, which
`FDatabase.RulesEncoded` covers, and a `.decl` writes no data. -/
def Cmd.EntryWriteOk : Cmd → Prop
  | .action a => a.EntrySafe
  | _ => True

/-- **Every action an encoded block emits is entry-safe.** -/
theorem entryWriteOk_encodeCmd {P : Program} (hdom : P.EncodeDomain) (c : Cmd) (hc : c ∈ P)
    (n i : Nat) : ∀ c' ∈ (encodeCmd c n i).1, c'.EntryWriteOk := by
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
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) 0 0) (encodeCmds_unionFree P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ h₀ hcmds
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noDecl_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact entryWriteOk_encodeCmd hdom c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noAtLet_encodeCmd hdom c₀ hc₀ m j c hmem

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
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) 0 0) (encodeCmds_unionFree P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ h₀ hcmds
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noDecl_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noAtLet_encodeCmd hdom c₀ hc₀ m j c hmem

/-- **`FDatabase.EncBase` at the state `execM` returned**, which is the prelude's instance
carried along `encodeCmds` by `FDatabase.EncBase.execProgramM`. -/
theorem execM_encode_encBase {P : Program} (hdom : P.EncodeDomain) (hag : P.AritiesAgree)
    {tgt : FDatabase} (htgt : execM (encode P) = some tgt) : tgt.EncBase P (encodeSig P) := by
  rw [execM, encode] at htgt
  obtain ⟨d₀, hprel, hcmds⟩ := FDatabase.execProgramM_append htgt
  have hb₀ : d₀.EncBase P (encodeSig P) := (encOk_preludeState hdom hag hprel).base
  refine FDatabase.EncBase.execProgramM
    (rulesEncodedOk_encodeCmds P (fun _ hc => hc) 0 0) (encodeCmds_unionFree P 0 0)
    (fun c hc => ?_) (fun c hc => ?_) (fun c hc => ?_) hb₀ hcmds
  · obtain ⟨c₀, -, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noDecl_encodeCmd c₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact encodedWriteLegal hdom hag c₀ hc₀ m j c hmem
  · obtain ⟨c₀, hc₀, m, j, hmem⟩ := mem_encodeCmd_of_mem_encodeCmds P (fun _ h => h) 0 0 c hc
    exact noAtLet_encodeCmd hdom c₀ hc₀ m j c hmem

/-- **The fourth cost of the e-class rule's firing, discharged run-wide**: every column an
`execM` target's rows record is a term `matchQuery` will assign, so a rebuild rule can re-read
the rows the fixpoint's roots argument contradicts against.

`cxRb_rowColumnsValued` is the same property decided at the state the one-off match runs at. -/
theorem execM_rowColumnsValued {P : Program} (hdom : P.EncodeDomain) {tgt : FDatabase}
    (htgt : execM (encode P) = some tgt) : tgt.RowColumnsValued :=
  have hb := execM_encode_encBase hdom hdom.aritiesAgree' htgt
  (execM_encode_valued hdom hdom.aritiesAgree' htgt).rowColumnsValued hb.eqsRefl
    hb.subtermClosed hb.inv.index


/-! ## The forward half's residue, and the correspondence

`Database.RebuildClosed` and its four consumers are stated here and not in
`Encoding/Correspond.lean` because their proof reads this file: the bridge
(`execM_entryRowsUF`), the forest (`execM_ufRowRoot_unique`), the fixpoint's roots
(`no_ufRowEdge_of_rowsClosed`) and `encodeSig` itself. The definitions they are stated over,
the state-level reductions and the refutations stay upstream, which is why
`Encoding/Correspond.lean` is still all `DiffTest.lean` imports. -/

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

**All three obligations hold, and what is left is the assembly — one identification.** The
bridge answers a view entry with a live row whose e-class column the union-find reaches from the
entry's, and that reach is `Database.UFReach`, over `@UF` **entry terms**: the row that
witnessed a step may since have been displaced, which is what `cxTgt_not_indexCurrent` refutes
and why the bridge is stated this way. The fixpoint's roots and the forest are stated over
`FDatabase.UFRowEdge`, over `@UF` **rows**. So the bridge hands each reader of an id a root it
reaches by *entries*, `execM_ufRowRoot_unique` makes the root reachable by *rows* unique, and
nothing yet identifies the two. `Database.Absorbs` is where that bites: it quantifies over every
term that reads the id, so one landing site has to answer for all of them, and each reader's is
produced by the bridge at its own view key. Closing it wants either the `terms` analogue of
`execM_ufRowsDescend` — every `@UF` entry term running `ordering-max ↦ ordering-min`, so that
`Database.UFReach` is well-founded and can be inducted along — or a confluence of
`Database.UFReach` onto row roots.

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
checking. **What it now owes the proof** is the target-side reading of `Database.WF.litsIsolated`
— that no `@UF` entry of the target is keyed on a literal it does not equal — which the source
run's refusal supplies and which is not yet written down.

**Non-vacuous, and still failing where it must**: `satTarget_rebuildClosed` is the degenerate
state, `Encoding/Match.lean`'s `uRebuilt_rebuildClosed` the one with a real `@UF` edge — where
`eclass` and `edged` both do work — `ncTgt_rebuildClosed` the one with a positive-arity key in
`column`, and `uTgt_not_rebuildClosed` is the same property one rebuild firing earlier, where it
fails because `uTgt_not_viewJoined` does. All three positive witnesses are proved at
`Database.RebuildClosedStrong` and transported by `Database.RebuildClosed.of_strong`, which is
what says the weakening is a weakening; `cxStale_not_rebuildClosedStrong` is where the two come
apart. -/
theorem execM_rebuildClosed {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
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
    (unionsInv_execM hdom hsrc htgt).reads

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
    (execM_unionsJoined hdom hsrc htgt)

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
