import EgglogSemantics.Spec.Merge
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Spec.Step
import EgglogSemantics.Proofs.Match

namespace Egglog
@[simp] theorem runProgram_nil {db : Database} : runProgram db [] = some db := rfl

@[simp] theorem runProgram_cons {db : Database} {c : Cmd} {cs : Program} :
    runProgram db (c :: cs) = (stepCmd db c).bind fun db' => runProgram db' cs := rfl

theorem runProgram_append {db : Database} {p q : Program} :
    runProgram db (p ++ q) = (runProgram db p).bind fun db' => runProgram db' q := by
  induction p generalizing db with
  | nil => rfl
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv]
    | some db₁ => simp [hv, ih]

/-! ### Rule results agree with the caller on env and rules

This is what makes `Database.sUnion`'s left bias faithful to the Redex `U_d`: the
operands `(run)` unions all carry the pre-state's environment and rules, so taking
them from the left operand loses nothing. -/
theorem ruleResults_env {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.env = db.env :=
  evalLocalActions_env h.choose_spec.2

theorem ruleResults_rules {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.rules = db.rules :=
  evalLocalActions_rules h.choose_spec.2

theorem ruleResults_contained {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    db.Contained d :=
  evalLocalActions_contained h.choose_spec.2

theorem ruleResults_wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ ruleResults db r) : d.WF :=
  evalLocalActions_wf hw h.choose_spec.1.mem_terms h.choose_spec.2

/-! ### Steps only add, and preserve well-formedness -/
@[simp] theorem runRules_env {db : Database} : (runRules db).env = db.env := rfl

@[simp] theorem runRules_rules {db : Database} : (runRules db).rules = db.rules := rfl

theorem runRules_contained (db : Database) : db.Contained (runRules db) :=
  Database.Contained.sUnion db _

theorem runRules_wf {db : Database} (hw : db.WF) : (runRules db).WF :=
  hw.sUnion fun _ hd => ruleResults_wf hw hd.choose_spec.2

theorem stepCmd_contained {db db' : Database} {c : Cmd} (h : stepCmd db c = some db') :
    db.Contained db' := by
  cases c with
  | action a => exact evalAction_contained h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact runRules_contained db
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    subst h
    exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem stepCmd_wf {db db' : Database} (hw : db.WF) {c : Cmd}
    (h : stepCmd db c = some db') : db'.WF := by
  cases c with
  | action a => exact evalAction_wf hw h
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩
  | run =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ runRules_wf hw
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at h
    exact h ▸ ⟨hw.subtermClosed, hw.eqsInTerms, hw.envInTerms⟩

theorem runProgram_contained {db db' : Database} {p : Program}
    (h : runProgram db p = some db') : db.Contained db' := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact (stepCmd_contained hv).trans (ih h)

theorem runProgram_wf {db db' : Database} (hw : db.WF) {p : Program}
    (h : runProgram db p = some db') : db'.WF := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons c cs ih =>
    cases hv : stepCmd db c with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [runProgram_cons, hv, Option.bind_some] at h
      exact ih (stepCmd_wf hw hv) h

theorem run_wf {p : Program} {db : Database} (h : run p = some db) : db.WF :=
  runProgram_wf Database.WF.empty h

@[simp] theorem runRounds_zero {db : Database} : runRounds 0 db = db := rfl

theorem runRounds_succ {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRounds n (runRules db) := rfl

/-- The other way round: a round can be taken last as well as first. -/
theorem runRounds_succ' {n : Nat} {db : Database} :
    runRounds (n + 1) db = runRules (runRounds n db) := by
  induction n generalizing db with
  | zero => rfl
  | succ m ih => rw [runRounds_succ, ih, runRounds_succ]

theorem runRounds_contained (n : Nat) (db : Database) : db.Contained (runRounds n db) := by
  induction n generalizing db with
  | zero => exact .refl db
  | succ n ih => exact (runRules_contained db).trans (ih (runRules db))

theorem runRounds_wf {db : Database} (hw : db.WF) (n : Nat) : (runRounds n db).WF := by
  induction n generalizing db with
  | zero => exact hw
  | succ n ih => exact ih (runRules_wf hw)

@[simp] theorem runRounds_env {n : Nat} {db : Database} : (runRounds n db).env = db.env := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_env]

@[simp] theorem runRounds_rules {n : Nat} {db : Database} :
    (runRounds n db).rules = db.rules := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, ih, runRules_rules]

/-- Once saturated, every further round changes nothing. -/
theorem Saturated.runRounds_eq {db : Database} (h : Saturated db) (n : Nat) :
    runRounds n db = db := by
  induction n generalizing db with
  | zero => rfl
  | succ n ih => rw [runRounds_succ, h, ih h]

/-- A round that adds nothing means the next round's result is the same database.
This is the stopping condition a saturating schedule tests for. -/
theorem Saturated.runRounds_succ_eq {db : Database} {n : Nat}
    (h : Saturated (runRounds n db)) : runRounds (n + 1) db = runRounds n db := by
  rw [runRounds_succ', h]

/-! ### `runRules` sees a substitution only up to agreement

An executable enumerator emits one substitution per agreement class, where the spec
admits the whole class (`ValidEnv` fixes the domain only up to permutation). This is
what makes those contribute the same databases. -/
theorem ruleResults_of_agree {db : Database} {r : Rule} {σ σ' : Env} (hag : Env.Agree σ σ')
    (hσ' : ValidQuerySubst db r.query σ') {d : Database}
    (hd : evalLocalActions db r.actions σ = some d) : d ∈ ruleResults db r :=
  ⟨σ', hσ', (evalLocalActions_agree r.actions hag).symm.trans hd⟩

/-! ### Equalities survive -/
/-- Nothing a program derives is ever retracted: the semantics only adds terms and
equalities, so `Cong` is monotone along a run. -/
theorem cong_runProgram {db db' : Database} {p : Program} (h : runProgram db p = some db')
    {a b : Term} (hc : Cong db a b) : Cong db' a b :=
  hc.mono (runProgram_contained h)

/-! ### Matched substitutions bind terms the database holds

`ValidEnv` per pattern, unioned. `RuleResults.wf` and `RuleResults.ctorTerms` need it: a
firing runs its head in the caller's environment extended by the substitution, and both
invariants ask that every value there be a term the database already holds. -/
/-- The hypothesis `patternHolds_MValidSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. -/
theorem MValidSubst.validEnv {db : Database} {p : Pattern} {σ : Env}
    (h : MValidSubst db p σ) : ValidEnv (p.freeVars db.env) db σ := by
  cases h with
  | expr hv _ _ _ => exact hv
  | eq hv _ _ _ _ _ => exact hv
  | values hv _ _ _ _ _ => exact hv

/-- Every value a query substitution binds is a term the database holds — `ValidEnv` per
pattern, unioned. -/
theorem MValidQuerySubst.mem_terms {db : Database} {q : Query} {σ : Env}
    (h : MValidQuerySubst db q σ) : ∀ b ∈ σ, b.2 ∈ db.terms := by
  obtain ⟨σs, hall, hu⟩ := h
  have hmem : ∀ σ' ∈ σs, ∃ p, MValidSubst db p σ' := by
    clear hu
    induction hall with
    | nil => intro _ hx; simp at hx
    | @cons p σ' _ _ hr _ ih =>
      intro τ hτ
      rcases List.mem_cons.mp hτ with rfl | h'
      · exact ⟨p, hr⟩
      · exact ih τ h'
  refine hu.forall_mem fun σ' hσ' b hb => ?_
  obtain ⟨p, hp⟩ := hmem σ' hσ'
  exact hp.validEnv.2 b hb

/-! ### Constructor rows survive a run

`Database.CtorRows` — the rows are exactly the ones the terms induce — is one of the two
things `Proofs/Merge.lean`'s `mcong_iff_cong` wants of a database (`Database.CtorTerms`,
below, is the other), and until now nothing connected it to a database a program can
produce.
`Proofs/Database.lean` shows every database operation preserves it. What is left is to
carry it along the semantics, which takes three side conditions, each of them necessary:

* `Signature.AllConstructors`, because a `:merge` function's row is not a constructor
  row;
* `Action.SetLegal`, egglog's own restriction on `set`, because `set` is the one action
  that writes a row of its own choosing — `Database.not_ctorRows_addRow` is the failure;
* `Cmd.CtorDecl`, because declaring a `:merge` function turns rows *already present*
  into a `MergeStep` collision, whose combined row need not be a constructor row. No
  `set` occurs there, so `SetLegal` does not cover it.

Under the first two together there is in fact no legal `set` at all
(`Action.SetLegal.elim`): the constructor fragment is exactly the fragment with no
`set`, which is also why nothing before M9 needed any of this. -/
/-- **No `set` is legal on an all-constructors signature.** `SetLegal` asks for a
non-constructor and there is none, so every `set` case below is impossible rather
than merely well behaved. -/
theorem Action.SetLegal.elim {sig : Signature} (hsig : sig.AllConstructors) {f : FnName}
    {args out : List Expr} (h : (Action.set f args out).SetLegal sig) : False :=
  h (hsig f)

/-- `SetLegal` does not care *which* all-constructors signature it is read against,
because under one there is no legal `set` to disagree about. This is what lets a `decl`
change the signature without invalidating the rules the database already holds. -/
theorem Actions.SetLegal.of_allConstructors {as : List Action} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : Actions.SetLegal as sig) :
    Actions.SetLegal as sig' := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    refine ⟨?_, ih h.2⟩
    cases a with
    | set f args out => exact (Action.SetLegal.elim hsig h.1).elim
    | expr _ => trivial
    | letBind _ _ => trivial
    | union _ _ => trivial

theorem Rule.SetLegal.of_allConstructors {r : Rule} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : r.SetLegal sig) : r.SetLegal sig' :=
  Actions.SetLegal.of_allConstructors hsig h

/-- `AllConstructors` survives a command, provided the command declares a constructor. -/
theorem Signature.AllConstructors.sigBind {sig : Signature} (h : sig.AllConstructors)
    {c : Cmd} (hc : c.CtorDecl) : (c.sigBind sig).AllConstructors := by
  cases c with
  | decl f d =>
    intro g
    change ((Function.update sig f (some d)) g).bind FnDecl.merge = none
    rw [Function.update_apply]
    split
    · exact hc
    · exact h g
  | _ => exact h

/-- The state half of the constructor fragment: the database is well formed, the signature
declares no merge function, every application it holds is a *declared* constructor's, no
rule the database holds can `set`, and the rows are the terms'.

Bundled because they have to move together — a `decl` changes the signature, so it changes
what `SetLegal` means for the rules already stored, and `runRules` needs those rules legal
to keep the rows constructor rows.

`terms` is what `mcong_iff_cong` reads, and it is a field rather than a consequence of
`sig` because declaration is required: `AllConstructors` says nothing *is* a merge
function, which leaves an undeclared name neither a constructor nor a merge function.
`wf` is here only to keep `terms`: an action evaluates in `db.env`, and knowing that the
environment's values are constructor-built is `Database.env_ctorTerm`, which reads both. -/
structure Database.CtorState (db : Database) : Prop where
  wf : db.WF
  sig : db.sig.AllConstructors
  terms : db.CtorTerms
  rules : ∀ r ∈ db.rules, r.SetLegal db.sig
  rows : db.CtorRows

theorem Database.CtorState.empty : Database.empty.CtorState where
  wf := Database.WF.empty
  sig := by intro f; simp [Signature.mergeOf, Database.empty]
  terms := by intro f as hm; exact absurd hm (by simp [Database.empty])
  rules := by simp [Database.empty]
  rows := Database.CtorRows.empty

/-! #### Constructor terms survive a run

`Database.CtorTerms` — every application the database holds heads a declared constructor —
is the second thing `mcong_iff_cong` wants, and the one the old reading of
`Signature.IsCtor` gave away for free. It is carried the same way `CtorRows` is, with the
same three side conditions doing the same work: `Expr.eval` builds only at a constructor,
so an action adds nothing else; a `set` is the one action that could, and `SetLegal` plus
`AllConstructors` leaves none; and a `decl` moves the signature, where `CtorDecl` keeps it
moving in the one direction that adds constructors. -/
theorem evalAction_ctorTerms {db db' : Database} (hw : db.WF) (hsig : db.sig.AllConstructors)
    {a : Action} (hlegal : a.SetLegal db.sig) (hterms : db.CtorTerms)
    (h : evalAction db a = some db') : db'.CtorTerms := by
  have henv := Database.env_ctorTerm hw hterms
  rcases evalAction_eq_some h with ⟨_, t, -, ht, rfl⟩ | ⟨_, _, t, -, ht, rfl⟩ |
    ⟨_, _, t₁, t₂, -, ht₁, ht₂, rfl⟩ | ⟨f, _, _, as, v, rfl, -, -, rfl⟩
  · exact hterms.addTerm (Expr.eval_ctorTerm henv ht)
  · exact hterms.addTerm (Expr.eval_ctorTerm henv ht)
  · exact hterms.addEq (Expr.eval_ctorTerm henv ht₁) (Expr.eval_ctorTerm henv ht₂)
  · exact (Action.SetLegal.elim hsig hlegal).elim

theorem evalActions_ctorTerms {db db' : Database} (hw : db.WF)
    (hsig : db.sig.AllConstructors) {as : List Action}
    (hlegal : Actions.SetLegal as db.sig) (hterms : db.CtorTerms)
    (h : evalActions db as = some db') : db'.CtorTerms := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hterms
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (evalAction_wf hw hv) (by rw [evalAction_sig hv]; exact hsig)
        (by rw [evalAction_sig hv]; exact hlegal.2)
        (evalAction_ctorTerms hw hsig hlegal.1 hterms hv) h

theorem evalLocalActions_ctorTerms {db db' : Database} (hw : db.WF)
    (hsig : db.sig.AllConstructors) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (hlegal : Actions.SetLegal as db.sig)
    (hterms : db.CtorTerms) (h : evalLocalActions db as σ = some db') : db'.CtorTerms := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  have hw' : Database.WF { db with env := db.env ++ σ } := by
    refine ⟨hw.subtermClosed, hw.eqsInTerms, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb' | hb'
    · exact hw.envInTerms b hb'
    · exact hσ b hb'
  exact evalActions_ctorTerms (db := { db with env := db.env ++ σ }) (db' := d)
    hw' hsig hlegal hterms hv

theorem ruleResults_ctorTerms {db d : Database} (hw : db.WF)
    (hsig : db.sig.AllConstructors) {r : Rule} (hlegal : r.SetLegal db.sig)
    (hterms : db.CtorTerms) (h : d ∈ ruleResults db r) : d.CtorTerms :=
  evalLocalActions_ctorTerms hw hsig h.choose_spec.1.mem_terms hlegal hterms
    h.choose_spec.2

/-! #### The functional semantics -/
theorem evalAction_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {a : Action} (hlegal : a.SetLegal db.sig) (hrows : db.CtorRows)
    (h : evalAction db a = some db') : db'.CtorRows := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, args, out, as, v, rfl, -, -, rfl⟩
  · exact hrows.addTerm t
  · exact hrows.addTerm t
  · exact hrows.addEq t₁ t₂
  · exact (Action.SetLegal.elim hsig hlegal).elim

theorem evalActions_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {as : List Action} (hlegal : Actions.SetLegal as db.sig) (hrows : db.CtorRows)
    (h : evalActions db as = some db') : db'.CtorRows := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hrows
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (by rw [evalAction_sig hv]; exact hsig)
        (by rw [evalAction_sig hv]; exact hlegal.2)
        (evalAction_ctorRows hsig hlegal.1 hrows hv) h

theorem evalLocalActions_ctorRows {db db' : Database} (hsig : db.sig.AllConstructors)
    {as : List Action} {σ : Env} (hlegal : Actions.SetLegal as db.sig)
    (hrows : db.CtorRows) (h : evalLocalActions db as σ = some db') : db'.CtorRows := by
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  exact evalActions_ctorRows (db := { db with env := db.env ++ σ }) (db' := d)
    hsig hlegal hrows hv

theorem ruleResults_ctorRows {db d : Database} (hsig : db.sig.AllConstructors) {r : Rule}
    (hlegal : r.SetLegal db.sig) (hrows : db.CtorRows) (h : d ∈ ruleResults db r) :
    d.CtorRows :=
  evalLocalActions_ctorRows hsig hlegal hrows h.choose_spec.2

theorem runRules_ctorRows {db : Database} (h : db.CtorState) : (runRules db).CtorRows :=
  h.rows.sUnion fun _ hd =>
    ruleResults_ctorRows h.sig (h.rules _ hd.choose_spec.1) h.rows hd.choose_spec.2

theorem ruleResults_sig {db d : Database} {r : Rule} (h : d ∈ ruleResults db r) :
    d.sig = db.sig := evalLocalActions_sig h.choose_spec.2

theorem runRules_ctorTerms {db : Database} (h : db.CtorState) : (runRules db).CtorTerms :=
  h.terms.sUnion fun _ hd f as hm =>
    ruleResults_sig hd.choose_spec.2 ▸
      ruleResults_ctorTerms h.wf h.sig (h.rules _ hd.choose_spec.1) h.terms
        hd.choose_spec.2 f as hm

theorem runRules_ctorState {db : Database} (h : db.CtorState) : (runRules db).CtorState :=
  ⟨runRules_wf h.wf, h.sig, runRules_ctorTerms h, h.rules, runRules_ctorRows h⟩

/-- The signature a command leaves is `Cmd.sigBind`'s, which is what lets
`Program.SetLegal` thread through a `decl`. -/
theorem stepCmd_sig {db db' : Database} {c : Cmd} (h : stepCmd db c = some db') :
    db'.sig = c.sigBind db.sig := by
  cases c with
  | action a => exact evalAction_sig h
  | rule r => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl
  | run => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl
  | decl f d => simp only [stepCmd, Option.some.injEq] at h; exact h ▸ rfl

/-- A declaration whose entry has no merge keeps every constructor a constructor, and makes
the declared name one. This is the direction `Cmd.CtorDecl` buys: a *merge* declaration
would take `IsCtor` away at the declared name, which is `Falsity.claim1`. -/
theorem Signature.IsCtor.update {sig : Signature} {f g : FnName} {d : FnDecl}
    (hd : d.merge = none) (h : sig.IsCtor g) :
    Signature.IsCtor (Function.update sig f (some d)) g := by
  obtain ⟨e, he, hm⟩ := h
  by_cases hg : g = f
  · subst hg; exact ⟨d, Function.update_self .., hd⟩
  · exact ⟨e, by rw [Function.update_of_ne hg]; exact he, hm⟩

/-- **Declaring a name the signature does not mention keeps every constructor.** Unlike
`Signature.IsCtor.update` this puts no condition on the declaration: whatever `f` is
declared to be, it was not a constructor before, so nothing that *was* one is disturbed.

This is what declaration-required buys, and the reason `mcong_mono_needs_sig` is not a
counterexample to it: that witness *re*declares a name that was already a constructor. -/
theorem Signature.IsCtor.update_of_fresh {sig : Signature} {f g : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : sig.IsCtor g) :
    Signature.IsCtor (Function.update sig f (some dc)) g := by
  obtain ⟨e, he, hm⟩ := h
  have hg : g ≠ f := by rintro rfl; rw [hf] at he; exact absurd he (by simp)
  exact ⟨e, by rw [Function.update_of_ne hg]; exact he, hm⟩

/-- `CtorTerms` survives a command's signature change, provided the command declares a
constructor. -/
theorem Database.CtorTerms.sigBind {db : Database} (h : db.CtorTerms) {c : Cmd}
    (hc : c.CtorDecl) : ∀ f as, Term.app f as ∈ db.terms → (c.sigBind db.sig).IsCtor f := by
  cases c with
  | decl g d => exact fun f as hm => (h f as hm).update hc
  | _ => exact h

theorem stepCmd_ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hlegal : c.SetLegal db.sig) (hv : stepCmd db c = some db') :
    db'.CtorState := by
  cases c with
  | action a =>
    exact ⟨evalAction_wf h.wf hv,
      by rw [evalAction_sig hv]; exact h.sig,
      evalAction_ctorTerms h.wf h.sig hlegal h.terms hv,
      by rw [evalAction_sig hv, evalAction_rules hv]; exact h.rules,
      evalAction_ctorRows h.sig hlegal h.rows hv⟩
  | rule r =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    refine ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.sig, h.terms, ?_,
      h.rows⟩
    rintro r' (rfl | hr')
    · exact hlegal
    · exact h.rules r' hr'
  | run =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    exact runRules_ctorState h
  | decl f d =>
    simp only [stepCmd, Option.some.injEq] at hv
    subst hv
    exact ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.sig.sigBind hdecl,
      h.terms.sigBind (c := .decl f d) hdecl,
      fun r hr => Rule.SetLegal.of_allConstructors h.sig (h.rules r hr), h.rows⟩

theorem runProgram_ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig)
    (hv : runProgram db p = some db') : db'.CtorState := by
  induction p generalizing db with
  | nil => exact (Option.some.injEq .. ▸ hv : db = db') ▸ h
  | cons c cs ih =>
    cases hc : stepCmd db c with
    | none => simp [hc] at hv
    | some db₁ =>
      simp only [runProgram_cons, hc, Option.bind_some] at hv
      exact ih (stepCmd_ctorState h (hdecl c (by simp)) hlegal.1 hc)
        (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
        (by rw [stepCmd_sig hc]; exact hlegal.2) hv

/-- A whole run stays in the constructor fragment. -/
theorem run_ctorRows {p : Program} {db : Database} (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) (h : run p = some db) : db.CtorRows :=
  (runProgram_ctorState Database.CtorState.empty hdecl hlegal h).rows

/-! #### The step relations

M9's relational semantics, where the headline lives. Actions are not among them — one
evaluator means `evalAction` is both readings — so `MergeStep` upwards is all there is,
and `MergeStep` is the case `SetLegal` cannot reach: it fires only on a `.merge`
function, so `AllConstructors` makes it vacuous and a round is `RunRules` and nothing
else. -/
theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h with
  | collide _ _ _ _ hbody _ => simpa using evalActions_sig hbody

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

theorem RunStep.sig {db db' : Database} (h : RunStep db db') : db'.sig = db.sig :=
  MergeClosure.sig (d₁ := RunRules db) h

/-- **No merge fires on an all-constructors signature.** `MergeStep.collide` needs a
`.merge` function and there is none, so the merge phase of a round is empty. -/
theorem MergeStep.not_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeStep db db') : False := by
  cases h with
  | collide _ _ _ hm _ _ => exact hsig.elim hm

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-- A round on constructors is exactly `RunRules`: the merge phase does nothing. -/
theorem RunStep.eq_runRules {db db' : Database} (hsig : db.sig.AllConstructors)
    (h : RunStep db db') : db' = RunRules db :=
  MergeClosure.eq_of_allConstructors hsig h

/-- **Why `Cmd.CtorDecl` is a hypothesis, and why `SetLegal` alone would not do.**

Declare `f` a `:merge` function and the constructor row `f ↦ (f)` *already present*
collides with itself, so the merge body runs and writes whatever it likes at that key —
here the literal `0`. No `set` occurs anywhere, so no restriction on actions can rule
this out; what has to be ruled out is the declaration.

This is the one place the preservation chain needed a side condition beyond the `set`
one, and it is why `ProgramStep.ctorRows` takes `Program.CtorDecls`. -/
theorem exists_mergeStep_not_ctorRows :
    ∃ db db' : Database, db.CtorRows ∧ MergeStep db db' ∧ ¬db'.CtorRows :=
  ⟨{ sig := fun g => if g = "f" then some ⟨0, 1, some (.merge [] [.lit (.int 0)])⟩ else none
     terms := (Term.app "f" []).subterms
     rows := Database.ctorRowsOf (Term.app "f" []).subterms
     eqs := ∅
     env := []
     rules := ∅ },
    _, rfl,
    MergeStep.collide (f := "f") (as := []) (bs := []) (a := [Term.app "f" []])
      (b := [Term.app "f" []]) (vs := [Term.lit (.int 0)]) (body := [])
      (res := [.lit (.int 0)]) ⟨rfl, Term.IsSubterm.refl _⟩ ⟨rfl, Term.IsSubterm.refl _⟩
      .nil (by simp [Signature.mergeOf]) rfl rfl,
    Database.not_ctorRows_of_mem (Set.mem_insert _ _) (by simp)⟩

theorem RuleResults.ctorRows {db d : Database} (hsig : db.sig.AllConstructors) {r : Rule}
    (hlegal : r.SetLegal db.sig) (hrows : db.CtorRows) (h : d ∈ RuleResults db r) :
    d.CtorRows := by
  obtain ⟨σ, -, hstep⟩ := h
  exact evalLocalActions_ctorRows hsig hlegal hrows hstep

theorem RunRules.ctorRows {db : Database} (h : db.CtorState) : (RunRules db).CtorRows :=
  h.rows.sUnion fun _ hd =>
    RuleResults.ctorRows h.sig (h.rules _ hd.choose_spec.1) h.rows hd.choose_spec.2

theorem RuleResults.sig {db d : Database} {r : Rule} (h : d ∈ RuleResults db r) :
    d.sig = db.sig := by
  obtain ⟨σ, _, hstep⟩ := h; exact evalLocalActions_sig hstep

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, hq, hstep⟩ := h; exact evalLocalActions_wf hw hq.mem_terms hstep

theorem RuleResults.ctorTerms {db d : Database} (h : db.CtorState) {r : Rule}
    (hlegal : r.SetLegal db.sig) (hd : d ∈ RuleResults db r) : d.CtorTerms := by
  obtain ⟨σ, hq, hstep⟩ := hd
  exact evalLocalActions_ctorTerms h.wf h.sig hq.mem_terms hlegal h.terms hstep

theorem RunRules.wf {db : Database} (hw : db.WF) : (RunRules db).WF :=
  hw.sUnion fun _ hd => RuleResults.wf hw hd.choose_spec.2

theorem RunRules.ctorTerms {db : Database} (h : db.CtorState) : (RunRules db).CtorTerms :=
  h.terms.sUnion fun _ hd f as hm =>
    RuleResults.sig hd.choose_spec.2 ▸
      RuleResults.ctorTerms h (h.rules _ hd.choose_spec.1) hd.choose_spec.2 f as hm

theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  cases h with
  | action ha hm => rw [hm.sig]; exact evalAction_sig ha
  | rule => rfl
  | run hrun => exact hrun.sig
  | decl => rfl

theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hlegal : c.SetLegal db.sig) (hstep : CmdStep db c db') :
    db'.CtorState := by
  cases hstep with
  | action ha hm =>
    -- The merge phase is empty on a constructor signature, so the state after it is the
    -- state the action left: `MergeClosure.eq_of_allConstructors`, which is the local
    -- stand-in for `Proofs/Merge.lean`'s saturation lemma (that file is above this one).
    have hd := hm.eq_of_allConstructors (by rw [evalAction_sig ha]; exact h.sig)
    subst hd
    exact ⟨evalAction_wf h.wf ha,
      by rw [evalAction_sig ha]; exact h.sig,
      evalAction_ctorTerms h.wf h.sig hlegal h.terms ha,
      by rw [evalAction_sig ha, evalAction_rules ha]; exact h.rules,
      evalAction_ctorRows h.sig hlegal h.rows ha⟩
  | rule =>
    refine ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.sig, h.terms, ?_,
      h.rows⟩
    rintro r' (rfl | hr')
    · exact hlegal
    · exact h.rules r' hr'
  | run hrun =>
    rw [RunStep.eq_runRules h.sig hrun]
    exact ⟨RunRules.wf h.wf, h.sig, RunRules.ctorTerms h, h.rules, RunRules.ctorRows h⟩
  | @decl f d =>
    exact ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.sig.sigBind hdecl,
      h.terms.sigBind (c := .decl f d) hdecl,
      fun r hr => Rule.SetLegal.of_allConstructors h.sig (h.rules r hr), h.rows⟩

/-! #### Inversion

`ProgramStep` is a relation, so reading a run *backwards* — what must have happened at
each command — is a `cases` rather than a projection. These two package it, which is what
lets a proof peel a concrete program one command at a time without nesting. -/
theorem ProgramStep.cons_inv {db d' : Database} {c : Cmd} {cs : Program}
    (h : ProgramStep db (c :: cs) d') : ∃ d, CmdStep db c d ∧ ProgramStep d cs d' := by
  cases h with | cons hc hrest => exact ⟨_, hc, hrest⟩

theorem ProgramStep.nil_inv {db d' : Database} (h : ProgramStep db [] d') : db = d' := by
  cases h with | nil => rfl

/-- The invariant argument, in the shape `Proofs/Merge.lean`'s `invariant_of_step` gives
it: an invariant preserved by one command holds at every reachable state. It is spelled
out rather than instantiated because the invariant here is not a bare `Database → Prop`
— each step also takes the command's own two side conditions. -/
theorem ProgramStep.ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig) (hstep : ProgramStep db p db') :
    db'.CtorState := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hc _ ih =>
    exact ih (hc.ctorState h (hdecl c (by simp)) hlegal.1)
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
      (by rw [hc.sig]; exact hlegal.2)

/-- **The headline.** A program that declares only constructors and never `set`s a
constructor leaves the row set determined by the term set.

The three side conditions are not interchangeable: `SetLegal` rules out the action that
writes a bad row, `CtorDecls` rules out the *declaration* that would let `MergeStep`
write one with no action involved, and `AllConstructors` of the starting signature is
what makes both bite. `hwf` and `hterms` are the two `Database.CtorState` needs and this
statement does not: they say nothing about rows and are carried only because the bundle
moves as one. -/
theorem ProgramStep.ctorRows {db db' : Database} {p : Program}
    (hstep : ProgramStep db p db') (hwf : db.WF) (hrows : db.CtorRows)
    (hsig : db.sig.AllConstructors) (hterms : db.CtorTerms) (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal db.sig)
    (hrules : ∀ r ∈ db.rules, r.SetLegal db.sig) : db'.CtorRows :=
  (ProgramStep.ctorState ⟨hwf, hsig, hterms, hrules, hrows⟩ hdecl hlegal hstep).rows

end Egglog
