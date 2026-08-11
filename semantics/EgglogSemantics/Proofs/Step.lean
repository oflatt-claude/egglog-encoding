import EgglogSemantics.Spec.Merge
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Match

namespace Egglog
/-! ### Matched substitutions

The e-matcher's API, on the one matching relation there is. `ValidEnv` per pattern,
unioned: `RuleResults.wf` and `RuleResults.ctorTerms` need it, because a firing runs its
head in the caller's environment extended by the substitution and both invariants ask
that every value there be a term the database already holds. -/
namespace ValidSubst
variable {db : Database} {p : Pattern} {σ : Env}

/-- The hypothesis `patternHolds_validSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. Since the hoist it is the left conjunct. -/
theorem validEnv (h : ValidSubst db p σ) : ValidEnv (p.freeVars db.env) db σ := h.1

theorem mem_terms (h : ValidSubst db p σ) : ∀ b ∈ σ, b.2 ∈ db.terms :=
  h.validEnv.mem_terms

/-- Appending a matching substitution to the globals cannot fail. -/
theorem union2_env (h : ValidSubst db p σ) : Env.Union2 db.env σ (db.env ++ σ) :=
  h.validEnv.union2_env fun _ hv => p.freeVars_lookup_eq_none hv

/-- A matching substitution binds exactly the pattern's free variables. -/
theorem mem_dom_iff (h : ValidSubst db p σ) {v : Var} :
    v ∈ Env.dom σ ↔ v ∈ p.freeVars db.env :=
  h.validEnv.mem_dom_iff

end ValidSubst
/-- `ValidSubst` transfers along agreement, provided the new substitution has exactly the
pattern's free variables as its domain.

Agreement alone is not enough, because `ValidEnv` pins the domain — which is precisely why
an executable enumerator has to canonicalize rather than emit any agreeing representative. -/
theorem ValidSubst.of_agree {db : Database} {p : Pattern} {σ σ' : Env}
    (h : ValidSubst db p σ) (hag : Env.Agree σ σ')
    (hdom : Env.dom σ' = p.freeVars db.env) : ValidSubst db p σ' := by
  have hterms : ∀ b ∈ σ', b.2 ∈ db.terms := by
    intro b hb
    have hnd : (Env.dom σ').Nodup := hdom ▸ p.freeVars_nodup db.env
    have hlk : Env.lookup b.1 σ' = some b.2 := (Env.lookup_eq_some_iff_mem hnd).mpr hb
    rw [← hag b.1] at hlk
    exact h.mem_terms _ (Env.mem_of_lookup hlk)
  have hperm : (Env.dom σ').Perm (p.freeVars db.env) := hdom ▸ List.Perm.refl _
  have hev : ∀ e : Expr, e.eval db.sig (db.env ++ σ') = e.eval db.sig (db.env ++ σ) :=
    fun e => Expr.eval_agree (Env.Agree.append_left db.env hag.symm) e
  have hevl : ∀ es : List Expr,
      Expr.evalList db.sig es (db.env ++ σ') = Expr.evalList db.sig es (db.env ++ σ) :=
    fun es => Expr.evalList_agree (Env.Agree.append_left db.env hag.symm) es
  refine ⟨⟨hperm, hterms⟩, ?_⟩
  cases h.2 with
  | expr hwm he hc => exact .expr hwm (by rw [hev]; exact he) hc
  | eq hwm he₁ he₂ hc₁ hc₂ =>
    exact .eq hwm (by rw [hev]; exact he₁) (by rw [hev]; exact he₂) hc₁ hc₂
  | values hu ht hk hw hrow =>
    exact .values (by rw [hevl]; exact hu) (by rw [hevl]; exact ht) hk hw hrow

/-! ### Reading `CongOn` back as an `addTerm`

The three shapes `Matches` uses, unfolded to the nested `addTerm`/`addTerms` every
congruence lemma is stated at. The first two are `Iff.rfl`: `withOperands` at a list
*literal* is a fold that reduces, so `CongOn db [t]` and `CongOn db [t₁, t₂]` *are*
`Cong (db.addTerm t)` and `Cong ((db.addTerm t₁).addTerm t₂)`. Only the row atom's
`ts ++ us`, whose two halves are variables, needs a rewrite. -/

theorem congOn_singleton {db : Database} {t a b : Term} :
    CongOn db [t] a b ↔ Cong (db.addTerm t) a b := Iff.rfl

theorem congOn_pair {db : Database} {t₁ t₂ a b : Term} :
    CongOn db [t₁, t₂] a b ↔ Cong ((db.addTerm t₁).addTerm t₂) a b := Iff.rfl

theorem congListOn_append {db : Database} {ts us as bs : List Term} :
    CongListOn db (ts ++ us) as bs ↔ CongList ((db.addTerms ts).addTerms us) as bs := by
  unfold CongListOn Database.withOperands
  rw [Database.addTerms_append]

/-! ### The hoist changed nothing

`ValidSubst` used to be one inductive whose three constructors each carried their own
`ValidEnv` premise, written out longhand, and their own extended database, spelled as
nested `addTerm`/`addTerms`. That relation is reproduced verbatim once here, so that
`validSubst_iff_unfactored` can check the factored form means the same thing. Nothing
else uses it. -/

/-- The pre-hoist `ValidSubst`, copied unchanged. -/
inductive ValidSubstUnfactored (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      ValidEnv (e.freeVars db.env) db σ → w ∈ db.terms →
      e.eval db.sig (db.env ++ σ) = some t → Cong (db.addTerm t) w t →
      ValidSubstUnfactored db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      ValidEnv (e₁.freeVars db.env ∪ e₂.freeVars db.env) db σ → w ∈ db.terms →
      e₁.eval db.sig (db.env ++ σ) = some t₁ → e₂.eval db.sig (db.env ++ σ) = some t₂ →
      Cong ((db.addTerm t₁).addTerm t₂) w t₁ → Cong ((db.addTerm t₁).addTerm t₂) t₁ t₂ →
      ValidSubstUnfactored db (.eq e₁ e₂) σ
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts ws bs : List Term} :
      ValidEnv (Expr.freeVarsList vs db.env ∪ Expr.freeVarsList as db.env) db σ →
      Expr.evalList db.sig vs (db.env ++ σ) = some us →
      Expr.evalList db.sig as (db.env ++ σ) = some ts →
      CongList ((db.addTerms ts).addTerms us) ts bs →
      CongList ((db.addTerms ts).addTerms us) us ws → Row.mk f bs ws ∈ db.rows →
      ValidSubstUnfactored db (.values vs f as) σ

/-- **The two relations are the same.** Two things had to be checked, and each shows up
below as the absence of a transport:

* the hoisted `ValidEnv (p.freeVars db.env) db σ` is *definitionally* each constructor's
  old premise, because `Pattern.freeVars` is defined by cases on the pattern — the `hv`s
  pass straight through;
* `CongOn db [t]` and `CongOn db [t₁, t₂]` are definitionally the old `addTerm` chains
  (`congOn_singleton`, `congOn_pair`), so only the row atom's `ts ++ us` needs
  `congListOn_append`. -/
theorem validSubst_iff_unfactored {db : Database} {p : Pattern} {σ : Env} :
    ValidSubst db p σ ↔ ValidSubstUnfactored db p σ := by
  constructor
  · rintro ⟨hv, h⟩
    cases h with
    | expr hw he hc => exact .expr hv hw he hc
    | eq hw he₁ he₂ hc₁ hc₂ => exact .eq hv hw he₁ he₂ hc₁ hc₂
    | values hu ht hk hw hrow =>
      exact .values hv hu ht (congListOn_append.mp hk) (congListOn_append.mp hw) hrow
  · intro h
    cases h with
    | expr hv hw he hc => exact ⟨hv, .expr hw he hc⟩
    | eq hv hw he₁ he₂ hc₁ hc₂ => exact ⟨hv, .eq hw he₁ he₂ hc₁ hc₂⟩
    | values hv hu ht hk hw hrow =>
      exact ⟨hv, .values hu ht (congListOn_append.mpr hk) (congListOn_append.mpr hw) hrow⟩

namespace ValidQuerySubst
variable {db : Database} {q : Query} {σ : Env}

/-- Every value a query substitution binds is a term the database holds — `ValidEnv` per
pattern, unioned. -/
theorem mem_terms (h : ValidQuerySubst db q σ) : ∀ b ∈ σ, b.2 ∈ db.terms := by
  obtain ⟨σs, hall, hu⟩ := h
  refine hu.forall_mem fun σ' hσ' b hb => ?_
  obtain ⟨p, _, hv⟩ := hall.exists_left hσ'
  exact hv.mem_terms b hb

/-- A query substitution binds exactly the query's free variables. -/
theorem mem_dom_iff (h : ValidQuerySubst db q σ) {v : Var} :
    v ∈ Env.dom σ ↔ ∃ p ∈ q, v ∈ p.freeVars db.env := by
  obtain ⟨σs, hall, hu⟩ := h
  rw [hu.mem_dom_iff]
  constructor
  · rintro ⟨σ', hσ', hv⟩
    obtain ⟨p, hp, hvs⟩ := hall.exists_left hσ'
    exact ⟨p, hp, hvs.mem_dom_iff.mp hv⟩
  · rintro ⟨p, hp, hv⟩
    obtain ⟨σ', hσ', hvs⟩ := hall.flip.exists_left hp
    exact ⟨σ', hσ', (ValidSubst.mem_dom_iff hvs).mpr hv⟩

/-- The empty query is satisfied by exactly the empty substitution: a rule with no
patterns fires once. -/
theorem nil_iff : ValidQuerySubst db [] σ ↔ σ = [] := by
  constructor
  · rintro ⟨σs, hall, hu⟩
    cases hall
    cases hu
    rfl
  · rintro rfl
    exact ⟨[], .nil, .nil⟩

end ValidQuerySubst
/-! ### Constructor rows survive a run

`Database.CtorRows` — the rows are exactly the ones the terms induce — is what says a
state is in the constructor fragment, and something has to connect it to a database a
program can produce.
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
    | set f args out => exact (Action.SetLegal.elim (args := args) (out := out) hsig h.1).elim
    | expr _ => trivial
    | letBind _ _ => trivial
    | union _ _ => trivial

theorem Rule.SetLegal.of_allConstructors {r : Rule} {sig sig' : Signature}
    (hsig : sig.AllConstructors) (h : r.SetLegal sig) : r.SetLegal sig' :=
  ⟨fun _ _ => trivial, Actions.SetLegal.of_allConstructors hsig h.2⟩

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
what `SetLegal` means for the rules already stored, and `RunRules` needs those rules legal
to keep the rows constructor rows.

`terms` is a field rather than a consequence of `sig` because declaration is required:
`AllConstructors` says nothing *is* a merge function, which leaves an undeclared name
neither a constructor nor a merge function.
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
is the one the old reading of `Signature.IsCtor` gave away for free. It is carried the
same way `CtorRows` is, with the
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

This is what declaration-required buys. A *re*declaration is the case it does not
cover, and `Falsity.claim1` is where that bites. -/
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

/-! #### The step relations

The step relations are the semantics, so what is proved about them here is what a
program run leaves. `MergeStep` is the case `SetLegal` cannot reach: it fires only on a
`.merge` function, so `AllConstructors` makes it vacuous and a round is `RunRules` and
nothing else. -/
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
  exact evalLocalActions_ctorRows hsig hlegal.2 hrows hstep

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
  exact evalLocalActions_ctorTerms h.wf h.sig hq.mem_terms hlegal.2 h.terms hstep

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
    -- stand-in for `Proofs/Merge.lean`'s saturation lemma (that file is below this one).
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

/-- Running `p` then `q` is running `p ++ q`. What lets a concrete program be built a
prefix at a time. -/
theorem ProgramStep.append {db d d' : Database} {p q : Program} (h₁ : ProgramStep db p d) :
    ProgramStep d q d' → ProgramStep db (p ++ q) d' := by
  induction h₁ with
  | nil => exact id
  | cons hc _ ih => exact fun h₂ => .cons hc (ih h₂)

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

/-! #### Determinism on the constructor fragment

`CmdStep` and `ProgramStep` are relations because the merge phase is one — a round may
stop anywhere in `MergeClosure`. On a constructor signature there is no merge phase, so
the freedom is gone and the relation is a partial function. This is what lets a concrete
run be read backwards one command at a time, and it is what makes the interpreter's
refinement an *equality* rather than a reachability statement. -/
/-- One command has at most one result where no merge fires.

The `action` case is the only one with a choice to eliminate: `evalAction` is a function,
so the two runs agree up to the merge phase, and `MergeClosure.eq_of_allConstructors`
collapses that. `run` is `RunStep.eq_runRules` twice, `rule` and `decl` are `rfl`. -/
theorem CmdStep.det {db d₁ d₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (h₁ : CmdStep db c d₁) (h₂ : CmdStep db c d₂) : d₁ = d₂ := by
  cases h₁ with
  | action ha₁ hm₁ =>
    cases h₂ with
    | action ha₂ hm₂ =>
      obtain rfl := Option.some.inj (ha₁.symm.trans ha₂)
      rw [hm₁.eq_of_allConstructors (by rw [evalAction_sig ha₁]; exact hsig),
        hm₂.eq_of_allConstructors (by rw [evalAction_sig ha₁]; exact hsig)]
  | rule => cases h₂ with | rule => rfl
  | run hr₁ => cases h₂ with | run hr₂ => rw [hr₁.eq_runRules hsig, hr₂.eq_runRules hsig]
  | decl => cases h₂ with | decl => rfl

/-- A whole program has at most one result on the constructor fragment. The side
conditions are `CmdStep.ctorState`'s: they are what keeps `AllConstructors` true at every
intermediate state, which is what `CmdStep.det` needs there. -/
theorem ProgramStep.det {db d₁ d₂ : Database} (hc : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hlegal : p.SetLegal db.sig)
    (h₁ : ProgramStep db p d₁) (h₂ : ProgramStep db p d₂) : d₁ = d₂ := by
  induction p generalizing db d₁ d₂ with
  | nil => rw [← h₁.nil_inv, ← h₂.nil_inv]
  | cons c cs ih =>
    obtain ⟨e₁, he₁, hr₁⟩ := h₁.cons_inv
    obtain ⟨e₂, he₂, hr₂⟩ := h₂.cons_inv
    obtain rfl := he₁.det hc.sig he₂
    exact ih (he₁.ctorState hc (hdecl c (by simp)) hlegal.1)
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))
      (by rw [he₁.sig]; exact hlegal.2) hr₁ hr₂

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
