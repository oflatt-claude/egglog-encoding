import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Match

namespace Egglog
/-! ### `set` legality

`Action.SetLegal` is egglog's own restriction on `set`: on an all-constructors signature it
admits nothing at all, so that fragment is exactly the fragment with no `set`. -/
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
  Actions.SetLegal.of_allConstructors hsig h

/-! ### The constructor fragment's state

`MergeStep` fires only on a `.merge` function, so a signature that declares none makes the
merge phase empty; that is what turns the relational `CmdStep` back into a partial
function. -/
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

/-- The state half of the constructor fragment: the database is well formed and the
signature declares no merge function.

`WF` is what `Proofs/Interp.lean`'s `execRunRules_RunRules` reads, and `AllConstructors` is
what makes `MergeStep` vacuous, so that a command has exactly one result. Bundled because
they move together across a command and because a `decl` moves the signature, which is why
`CmdStep.ctorState` takes `Cmd.CtorDecl` and nothing else. -/
structure Database.CtorState (db : Database) : Prop where
  wf : db.WF
  sig : db.sig.AllConstructors

theorem Database.CtorState.empty : Database.empty.CtorState where
  wf := Database.WF.empty
  sig := by intro f; simp [Signature.mergeOf, Database.empty]

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

/-! ### The merge phase -/
theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h with
  | collide _ _ _ _ _ _ _ hbody _ => simpa using evalActions_sig hbody

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- **No merge fires on an all-constructors signature.** `MergeStep.collide` needs a
`.merge` function and there is none, so every command's merge phase is empty. -/
theorem MergeStep.not_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeStep db db') : False := by
  cases h with
  | @collide _ f _ _ _ _ _ _ _ _ hd hm _ _ _ _ _ _ _ =>
    have hno := hsig f
    rw [Signature.mergeOf, hd, Option.bind_some, hm] at hno
    simp at hno

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-! ### Rule firing -/
theorem RuleResults.sig {db d : Database} {r : Rule} (h : d ∈ RuleResults db r) :
    d.sig = db.sig := by
  obtain ⟨σ, _, hstep⟩ := h; exact evalLocalActions_sig hstep

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, hq, hstep⟩ := h; exact evalLocalActions_wf hw hq.mem_terms hstep

theorem RunRules.wf {db : Database} (hw : db.WF) : (RunRules db).WF :=
  hw.sUnion fun _ hd => RuleResults.wf hw hd.choose_spec.2

/-! ### A command's effect

`CmdStep` is `cmdEffect` followed by a merge phase, so every fact about a command splits
into a fact about the deterministic effect and `MergeClosure`'s own. -/
theorem cmdEffect_sig {db d : Database} {c : Cmd} (h : cmdEffect db c = some d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_sig h
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | run => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | decl f dc => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl

theorem cmdEffect_wf {db d : Database} (hw : db.WF) {c : Cmd}
    (h : cmdEffect db c = some d) : d.WF := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_wf hw h
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl
  | run => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact RunRules.wf hw
  | decl f dc =>
    simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl

/-- The signature a command leaves is all-constructors provided the command declares a
constructor. This is what makes the merge phase that *follows* the effect empty — including
after a `.decl`, which is the case the uniform merge phase added. -/
theorem cmdEffect_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdEffect db c = some d) :
    d.sig.AllConstructors := by
  rw [cmdEffect_sig h]; exact hsig.sigBind hdecl

/-! ### The step relations

The step relations are the semantics, so what is proved about them here is what a program
run leaves. -/
theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  obtain ⟨d, heff, hcl⟩ := h
  rw [hcl.sig]; exact cmdEffect_sig heff

/-- **A command keeps the constructor fragment's state, with no condition on its actions.**
The one thing that has to be excluded is the *declaration* of a `:merge` function, which is
`Cmd.CtorDecl`; a `set` cannot disturb either field. -/
theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hstep : CmdStep db c db') : db'.CtorState := by
  obtain ⟨d, heff, hcl⟩ := hstep
  have hsig := cmdEffect_allConstructors h.sig hdecl heff
  rw [hcl.eq_of_allConstructors hsig]
  exact ⟨cmdEffect_wf h.wf heff, hsig⟩

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

/-- The invariant argument: an invariant preserved by one command holds at every reachable
state. It is spelled out rather than instantiated because the invariant here is not a bare
`Database → Prop` — each step also takes the command's own side condition. -/
theorem ProgramStep.ctorState {db db' : Database} (h : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (hstep : ProgramStep db p db') : db'.CtorState := by
  induction hstep with
  | nil => exact h
  | @cons db d d' c cs hc _ ih =>
    exact ih (hc.ctorState h (hdecl c (by simp)))
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc'))

/-! #### Determinism on the constructor fragment

`CmdStep` and `ProgramStep` are relations because the merge phase is one — a command may
stop anywhere in `MergeClosure`. On a constructor signature there is no merge phase, so
the freedom is gone and the relation is a partial function. This is what lets a concrete
run be read backwards one command at a time, and it is what makes the interpreter's
refinement an *equality* rather than a reachability statement. -/
/-- One command has at most one result where no merge fires.

`cmdEffect` is a function, so the two runs agree up to the merge phase and
`MergeClosure.eq_of_allConstructors` collapses that. `Cmd.CtorDecl` is needed because the
merge phase now follows a `.decl` as well: declaring a `:merge` function is exactly how a
run on an otherwise constructor-only state regains a choice. -/
theorem CmdStep.det {db d₁ d₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (hdecl : c.CtorDecl) (h₁ : CmdStep db c d₁) (h₂ : CmdStep db c d₂) : d₁ = d₂ := by
  obtain ⟨e₁, heff₁, hcl₁⟩ := h₁
  obtain ⟨e₂, heff₂, hcl₂⟩ := h₂
  obtain rfl := Option.some.inj (heff₁.symm.trans heff₂)
  have hs := cmdEffect_allConstructors hsig hdecl heff₁
  rw [hcl₁.eq_of_allConstructors hs, hcl₂.eq_of_allConstructors hs]

/-- A whole program has at most one result on the constructor fragment. The side
conditions are `CmdStep.ctorState`'s: they are what keeps `AllConstructors` true at every
intermediate state, which is what `CmdStep.det` needs there. -/
theorem ProgramStep.det {db d₁ d₂ : Database} (hc : db.CtorState) {p : Program}
    (hdecl : p.CtorDecls) (h₁ : ProgramStep db p d₁) (h₂ : ProgramStep db p d₂) :
    d₁ = d₂ := by
  induction p generalizing db d₁ d₂ with
  | nil => rw [← h₁.nil_inv, ← h₂.nil_inv]
  | cons c cs ih =>
    obtain ⟨e₁, he₁, hr₁⟩ := h₁.cons_inv
    obtain ⟨e₂, he₂, hr₂⟩ := h₂.cons_inv
    obtain rfl := he₁.det hc.sig (hdecl c (by simp)) he₂
    exact ih (he₁.ctorState hc (hdecl c (by simp)))
      (fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc')) hr₁ hr₂

end Egglog
