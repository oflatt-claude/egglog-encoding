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

/-! ### Declaredness, in a signature that grows

`Cmd.sigBind` only ever writes a `some`, so every check reading `Expr.Declared` survives a
later command. This is what carries `Cmd.MergeDeclared`, asked at the declaration, to the
signature a merge phase further on runs against. -/
/-- One signature declares everything another does. `Cmd.sigBind` writes only a `some`, so
this is what a command leaves. -/
def Signature.Extends (sig' sig : Signature) : Prop := ∀ f, sig f ≠ none → sig' f ≠ none

theorem Signature.Extends.refl (sig : Signature) : sig.Extends sig := fun _ h => h

theorem Signature.Extends.trans {s₁ s₂ s₃ : Signature} (h₁ : s₂.Extends s₁)
    (h₂ : s₃.Extends s₂) : s₃.Extends s₁ := fun f h => h₂ f (h₁ f h)

theorem Signature.extends_sigBind (sig : Signature) (c : Cmd) :
    (c.sigBind sig).Extends sig := by
  cases c with
  | decl f d =>
    intro g hg
    rw [Cmd.sigBind]
    by_cases h : g = f
    · subst h; rw [Function.update_self]; simp
    · rw [Function.update_of_ne h]; exact hg
  | _ => exact fun _ h => h

/-- Declaredness is monotone in the signature, which is what carries a clause asked before
the rule to the state the rule fires at. -/
theorem Expr.Declared.mono {e : Expr} {sig sig' : Signature} (hs : sig'.Extends sig)
    (h : e.Declared sig) : e.Declared sig' :=
  fun f hf => (h f hf).imp id (hs f)

theorem Action.Declared.mono {a : Action} {sig sig' : Signature} (hs : sig'.Extends sig)
    (h : a.Declared sig) : a.Declared sig' := by
  cases a with
  | expr e => exact Expr.Declared.mono hs h
  | letBind v e => exact Expr.Declared.mono hs h
  | union e₁ e₂ => exact ⟨Expr.Declared.mono hs h.1, Expr.Declared.mono hs h.2⟩
  | set f args out =>
    exact ⟨hs f h.1, fun e he => Expr.Declared.mono hs (h.2.1 e he),
      fun e he => Expr.Declared.mono hs (h.2.2 e he)⟩

theorem Actions.Declared.mono : ∀ {as : List Action} {sig sig' : Signature},
    sig'.Extends sig → Actions.Declared as sig → Actions.Declared as sig'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hs, h => ⟨h.1.mono hs, Actions.Declared.mono hs h.2⟩

@[inherit_doc Expr.Declared.mono]
theorem MergeSpec.Declared.mono {ms : MergeSpec} {sig sig' : Signature}
    (hs : sig'.Extends sig) (h : ms.Declared sig) : ms.Declared sig' := by
  cases ms with
  | merge body res =>
    exact ⟨Actions.Declared.mono hs h.1, fun e he => Expr.Declared.mono hs (h.2 e he)⟩
  | noMerge => trivial

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
  | collide _ _ _ _ _ _ _ _ hbody _ => simpa using evalActions_sig hbody

theorem MergeClosure.sig {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.sig = d₁.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- A merge writes its combined row and then restores the caller's environment and rule
list, so neither field ever moves. -/
theorem MergeStep.envRules {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  cases h with
  | collide => exact ⟨rfl, rfl⟩

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-- Every binding a merge body's environment provides is one of the two colliding rows'
outputs. `Proofs/Merge.lean`'s `MergeStep.wf` and `mergeOneOriented_inv` both need it,
because `WF.envInTerms` has to hold of `mergeEnv a b` before the body runs — and an entry is
a term now, so `WF.subtermClosed` supplies the outputs where `RowsWF` used to;
`mergeStep_avoids` below reads it for the same reason. -/
theorem mem_mergeEnvIdx {i : Nat} {os ns : List Term} {p : Var × Term}
    (h : p ∈ mergeEnvIdx i os ns) : p.2 ∈ os ∨ p.2 ∈ ns := by
  induction os generalizing i ns with
  | nil => simp [mergeEnvIdx] at h
  | cons o os ih =>
    cases ns with
    | nil => simp [mergeEnvIdx] at h
    | cons n ns =>
      simp only [mergeEnvIdx, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih h).imp (fun hm => by simp [hm]) fun hm => by simp [hm]

@[inherit_doc mem_mergeEnvIdx]
theorem mem_mergeEnv {os ns : List Term} {p : Var × Term} (h : p ∈ mergeEnv os ns) :
    p.2 ∈ os ∨ p.2 ∈ ns := by
  unfold mergeEnv at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · exact mem_mergeEnvIdx h

/-- **A `:merge` expression with no `:internal-identity-vals` conflicts on every pair**: it
has no action block, so `FnDecl.unchangedWidth` gives it no width and every collision
resolves. This is the whole of `MergeConflict` on the fragment `Signature.OrderingFree`
admits. -/
theorem mergeConflict_of_ordering_free {decl : FnDecl} (h : decl.OrderingFree)
    {body : List Action} {res : List Expr} (hm : decl.merge = some (.merge body res))
    (a b : List Term) : MergeConflict decl body a b := by
  obtain ⟨hid, hms⟩ := h
  obtain ⟨hbody, -⟩ := hms (.merge body res) (by rw [hm]; rfl)
  simp [MergeConflict, FnDecl.unchangedWidth, hid, hbody]

/-- **A collision's value tuples have the declared width.** `MergeStep.collide` fixes the
key/value split with its `arity` premise, and `Database.DeclaredTerms` — which every state a
legal run reaches has (`Proofs/Merge.lean`'s `reachable_declaredTerms`) — fixes the entry
width, so what is left over is `outArity` wide. -/
theorem outLength_of_declaredTerms {db : Database} (hdt : db.DeclaredTerms) {f : FnName}
    {decl : FnDecl} {as a : List Term} (hsig : db.sig f = some decl) (hm : decl.merge ≠ none)
    (has : as.length = decl.arity) (hmem : Term.app f (as ++ a) ∈ db.terms) :
    a.length = decl.outArity := by
  obtain ⟨d, hd, hw⟩ := hdt f (as ++ a) hmem
  obtain rfl : decl = d := Option.some.inj (hsig.symm.trans hd)
  have hnn : ¬ decl.merge.isNone = true := by simp [Option.isNone_iff_eq_none, hm]
  rw [List.length_append, has, FnDecl.entryWidth, if_neg hnn] at hw
  omega

/-- **The case split on `identityVals` that `MergeConflict` used to make.** The comparison is
at `FnDecl.unchangedWidth`, as egglog's is; where that width is every value column — a
`:merge` with a block and no `:internal-identity-vals` — comparing the counted prefixes is
comparing the whole tuples, *provided* the tuples have the declared width, which
`outLength_of_declaredTerms` supplies at every collision `MergeStep` can see. On a tuple wider
than the declaration the prefix test is the weaker one, and no reachable state has one. -/
theorem mergeConflict_iff_split {decl : FnDecl} {body : List Action} {a b : List Term}
    (ha : a.length = decl.outArity) (hb : b.length = decl.outArity) :
    MergeConflict decl body a b ↔
      (match decl.identityVals with
        | some k => a.take k ≠ b.take k
        | none => body = [] ∨ a ≠ b) := by
  have hta : a.take decl.outArity = a := by rw [← ha]; simp
  have htb : b.take decl.outArity = b := by rw [← hb]; simp
  unfold MergeConflict FnDecl.unchangedWidth
  cases hid : decl.identityVals with
  | some k => simp
  | none =>
    by_cases hbody : body = []
    · simp [hbody]
    · simp [hbody, hta, htb, List.isEmpty_iff]

/-- **No merge fires on an all-constructors signature.** `MergeStep.collide` needs a
`.merge` function and there is none, so every command's merge phase is empty. -/
theorem MergeStep.not_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeStep db db') : False := by
  cases h with
  | @collide _ f _ _ _ _ _ _ _ _ hd hm _ _ _ _ _ _ _ _ =>
    have hno := hsig f
    rw [Signature.mergeOf, hd, Option.bind_some, hm] at hno
    simp at hno

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-- **A merge phase out of a merge-saturated state is the identity.** The other reason a
merge closure collapses, and the one that makes `CmdStep`'s trailing phase neutral after a
`Cmd.saturate` — which is how the uniform phase survives the new command. -/
theorem MergeClosure.eq_of_mergeSaturated {db db' : Database} (hs : MergeSaturated db)
    (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; exact hs _ hstep

/-! ### Rule firing -/
theorem RuleResults.sig {db d : Database} {r : Rule} (h : d ∈ RuleResults db r) :
    d.sig = db.sig := by
  obtain ⟨σ, _, hstep⟩ := h; exact evalLocalActions_sig hstep

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, hq, hstep⟩ := h; exact evalLocalActions_wf hw hq.mem_terms hstep

theorem RunRules.wf {R : RulesetName} {db : Database} (hw : db.WF) : (RunRules R db).WF :=
  hw.sUnion fun _ hd => RuleResults.wf hw hd.choose_spec.2.2

@[simp] theorem RunRules.sig {R : RulesetName} {db : Database} :
    (RunRules R db).sig = db.sig := by
  simp only [RunRules, Database.sUnion_sig]

/-- **A ruleset is at a fixpoint exactly when none of its rules adds an equation.**

The right-hand side is the shape a "the rules have run out" hypothesis is naturally
written in — `Encoding/Encode.lean`'s `Rebuilt` is one — and the left is the fixpoint
`Cmd.saturate` reaches. Identifying them is what turns such a hypothesis into a
postcondition. -/
theorem runRules_eq_self_iff (R : RulesetName) (db : Database) :
    RunRules R db = db ↔
      ∀ r ∈ db.rules, r.ruleset = R → ∀ d ∈ RuleResults db r, Database.Contained d db := by
  constructor
  · intro h r hr hR d hd
    refine ⟨fun p hp => ?_⟩
    have hsub : d.eqs ⊆ (RunRules R db).eqs := fun q hq =>
      Or.inr (Set.mem_biUnion (Set.mem_setOf.mpr ⟨r, hr, hR, hd⟩) hq)
    rw [h] at hsub
    exact hsub hp
  · intro h
    refine Database.ext rfl ?_ rfl rfl
    refine Set.Subset.antisymm ?_ Set.subset_union_left
    rintro p (hp | hp)
    · exact hp
    · obtain ⟨d, ⟨r, hr, hR, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (h r hr hR d hd).eqs hp

/-! ### A saturating run

`Cmd.saturate` is a fixpoint condition rather than a `cmdEffect`, so the three facts every
command needs — the signature it leaves, the constructor fragment it keeps, and determinism
there — are proved for its *rounds* instead. Each is an induction along
`Relation.ReflTransGen (RunStep R)`. -/
theorem RunStep.sig {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.sig = db.sig := by
  rw [MergeClosure.sig h, RunRules.sig]

/-- Rounds preserve the signature, so `Cmd.saturate` leaves it alone. -/
theorem RunReach.sig {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.sig = db.sig := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [hstep.sig, ih]

/-- On a constructor signature a round has no merge phase, so it is the *function*
`RunRules R`. -/
theorem RunStep.eq_of_allConstructors {R : RulesetName} {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : RunStep R db db') : db' = RunRules R db :=
  MergeClosure.eq_of_allConstructors (by rw [RunRules.sig]; exact hsig) h

/-- So a state rounds reach is an iterate of it. -/
theorem RunReach.iterate {R : RulesetName} {db d : Database} (hsig : db.sig.AllConstructors)
    (h : Relation.ReflTransGen (RunStep R) db d) : ∃ k, (RunRules R)^[k] db = d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail e f hde hstep ih =>
      obtain ⟨k, hk⟩ := ih
      have hse : e.sig.AllConstructors := by rw [RunReach.sig hde]; exact hsig
      exact ⟨k + 1, by
        rw [Function.iterate_succ_apply', hk, ← hstep.eq_of_allConstructors hse]⟩

/-- **An invariant a round preserves is preserved by a saturating run.** The rounds are the
one unbounded iteration in the semantics, so every "this holds at every reachable state"
argument passes through here. -/
theorem RunReach.induction {R : RulesetName} {P : Database → Prop}
    (hstep : ∀ db db', P db → RunStep R db db' → P db') {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) (hp : P db) : P d := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact hstep _ _ ih hs

/-- Rounds keep the constructor fragment. -/
theorem RunReach.ctorState {R : RulesetName} {db d : Database} (h : db.CtorState)
    (hr : Relation.ReflTransGen (RunStep R) db d) : d.CtorState := by
  induction hr with
  | refl => exact h
  | tail _ hstep ih =>
      rw [hstep.eq_of_allConstructors ih.sig]
      exact ⟨RunRules.wf ih.wf, by rw [RunRules.sig]; exact ih.sig⟩

/-- **A saturating run is deterministic on the constructor fragment**: two fixpoints of one
deterministic iteration coincide. This is what `CmdStep.det` needs, and it is why the
fixpoint condition costs nothing there. -/
theorem saturateReach_det {R : RulesetName} {db d₁ d₂ : Database}
    (hsig : db.sig.AllConstructors) (h₁ : SaturateReach R db d₁)
    (h₂ : SaturateReach R db d₂) : d₁ = d₂ := by
  obtain ⟨k₁, hk₁⟩ := RunReach.iterate hsig h₁.1
  obtain ⟨k₂, hk₂⟩ := RunReach.iterate hsig h₂.1
  rcases Nat.le_total k₁ k₂ with hle | hle
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, hk₁, Function.iterate_fixed h₁.2.1] at hk₂
    exact hk₂
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, hk₂, Function.iterate_fixed h₂.2.1] at hk₁
    exact hk₁.symm

/-! ### A command's effect

`CmdStep` is `cmdEffect` followed by a merge phase, so every fact about a command splits
into a fact about the deterministic effect and `MergeClosure`'s own. -/
theorem cmdEffect_sig {db d : Database} {c : Cmd} (h : cmdEffect db c = some d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_sig (evalAction_of_top h)
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | run R => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl f dc => simp only [cmdEffect, Option.some.injEq] at h; subst h; rfl

theorem cmdEffect_wf {db d : Database} (hw : db.WF) {c : Cmd}
    (h : cmdEffect db c = some d) : d.WF := by
  cases c with
  | action a => simp only [cmdEffect] at h; exact evalAction_wf hw (evalAction_of_top h)
  | rule r => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl
  | run R => simp only [cmdEffect, Option.some.injEq] at h; subst h; exact RunRules.wf hw
  | saturate R => exact absurd h (by simp [cmdEffect])
  | decl f dc =>
    simp only [cmdEffect, Option.some.injEq] at h; subst h; exact hw.congr rfl rfl

/-- The signature a command leaves is all-constructors provided the command declares a
constructor. This is what makes the merge phase that *follows* the effect empty — including
after a `.decl`, which is the case the uniform merge phase added. -/
theorem cmdEffect_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdEffect db c = some d) :
    d.sig.AllConstructors := by
  rw [cmdEffect_sig h]; exact hsig.sigBind hdecl

/-! ### What a command reaches

`cmdReach` is `cmdEffect` on four commands out of five and a fixpoint condition on
`Cmd.saturate`. Absorbing the split here is what keeps it out of `CmdStep`'s proofs
below. -/
theorem cmdReach_of_cmdEffect {db d : Database} {c : Cmd} (hns : c.NoSaturate)
    (h : cmdEffect db c = some d) : cmdReach db c d := by
  cases c with
  | saturate R => exact (hns : False).elim
  | _ => exact h

theorem cmdEffect_of_cmdReach {db d : Database} {c : Cmd} (hns : c.NoSaturate)
    (h : cmdReach db c d) : cmdEffect db c = some d := by
  cases c with
  | saturate R => exact (hns : False).elim
  | _ => exact h

theorem cmdReach_sig {db d : Database} {c : Cmd} (h : cmdReach db c d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | saturate R => exact RunReach.sig (show SaturateReach R db d from h).1
  | _ => exact cmdEffect_sig h

theorem cmdReach_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdReach db c d) : d.sig.AllConstructors := by
  rw [cmdReach_sig h]; exact hsig.sigBind hdecl

theorem cmdReach_ctorState {db d : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hr : cmdReach db c d) : d.CtorState := by
  refine ⟨?_, cmdReach_allConstructors h.sig hdecl hr⟩
  cases c with
  | saturate R => exact (RunReach.ctorState h (show SaturateReach R db d from hr).1).wf
  | _ => exact cmdEffect_wf h.wf hr

/-- What a command reaches is unique on the constructor fragment: `cmdEffect` is a
function, and a saturating run's fixpoint is unique by `saturateReach_det`. -/
theorem cmdReach_det {db e₁ e₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (h₁ : cmdReach db c e₁) (h₂ : cmdReach db c e₂) : e₁ = e₂ := by
  cases c with
  | saturate R => exact saturateReach_det hsig h₁ h₂
  | _ => exact Option.some.inj ((show cmdEffect db _ = some e₁ from h₁).symm.trans h₂)

/-! ### The step relations

The step relations are the semantics, so what is proved about them here is what a program
run leaves. -/
theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  obtain ⟨d, hreach, hcl⟩ := h
  rw [hcl.sig]; exact cmdReach_sig hreach

/-- **A command keeps the constructor fragment's state, with no condition on its actions.**
The one thing that has to be excluded is the *declaration* of a `:merge` function, which is
`Cmd.CtorDecl`; a `set` cannot disturb either field. -/
theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hstep : CmdStep db c db') : db'.CtorState := by
  obtain ⟨d, hreach, hcl⟩ := hstep
  have hd := cmdReach_ctorState h hdecl hreach
  rw [hcl.eq_of_allConstructors hd.sig]
  exact hd

/-- **`CmdStep`'s trailing merge phase is neutral on `Cmd.saturate`.** `SaturateReach`
already ends merge-saturated, so the phase that `.rule` and `.decl` pay for uniformly is
free here too, and `CmdStep` stays one `def` over all five commands. -/
theorem cmdStep_saturate_iff {R : RulesetName} {db db' : Database} :
    CmdStep db (.saturate R) db' ↔ SaturateReach R db db' := by
  refine ⟨fun ⟨d, hreach, hcl⟩ => ?_, fun h => ⟨db', h, Relation.ReflTransGen.refl⟩⟩
  have hreach' : SaturateReach R db d := hreach
  rw [MergeClosure.eq_of_mergeSaturated hreach'.2.2 hcl]
  exact hreach'

/-! ### The merge phase after every command

`CmdStep` runs `cmdReach` and then a merge phase, where `.rule` and `.decl` once took none.
Both additions are **neutral**: every state the trailing phase reaches is one a phase run
*before* the command already reaches, so the uniform phase adds nothing. `.decl` is neutral
only once `Spec/Scope.lean`'s `MergeDeclared` is asked — without that check a declaration
*creates* a merge step, and `Proofs/Counterexamples.lean`'s `decl_enables_merge` is the
program that does. -/

/-! #### `.rule` is neutral

`Cong` reads `eqs`, a merge body never consults `rules`, and a `MergeStep` restores the
caller's, so the whole step is indifferent to the field a `.rule` writes. -/

/-- `Cong` reads `eqs` and nothing else, so a `sig`/`env`/`rules` update transports it, and
with it every term the state holds. -/
theorem CongList.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := CongList.mono ⟨h.subset⟩ hc

@[inherit_doc CongList.of_eqs_eq]
theorem Database.mem_terms_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Database.Contained.terms ⟨h.subset⟩ ht

theorem evalAction_setRules (db : Database) (R : Set Rule) (a : Action) :
    evalAction { db with rules := R } a
      = (evalAction db a).map fun d => { d with rules := R } := by
  cases a with
  | expr e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | letBind v e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | union e₁ e₂ =>
      cases h₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, h₁]
      | some t₁ =>
          cases h₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, h₁, h₂]
          | some t₂ =>
              simp only [evalAction, h₁, h₂, Option.bind_some]
              split <;> simp [Database.addEq, Database.addTerm]
  | set f args out =>
      cases h₁ : Expr.evalList db.sig args db.env <;>
        cases h₂ : Expr.evalList db.sig out db.env <;>
          simp [evalAction, h₁, h₂, Database.addTerm]

theorem evalActions_setRules (R : Set Rule) : ∀ (db : Database) (as : List Action),
    evalActions { db with rules := R } as
      = (evalActions db as).map fun d => { d with rules := R }
  | _, [] => by simp [evalActions]
  | db, a :: as => by
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_setRules, h]
      | some d =>
          have hstep : evalActions { db with rules := R } (a :: as)
              = evalActions { d with rules := R } as := by
            simp [evalActions, evalAction_setRules, h]
          rw [hstep, evalActions_setRules R d as]
          simp [evalActions, h]

theorem MergeStep.setRules {db db' : Database} (h : MergeStep db db') (R : Set Rule) :
    MergeStep { db with rules := R } { db' with rules := R } := by
  cases h with
  | @collide d f decl as bs a b vs body res hsig hmerge hcf ha hb hma hmb hcl heval hres =>
      refine MergeStep.collide (d := { d with rules := R }) hsig hmerge hcf ha hb
        (Database.mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hma)
        (Database.mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hmb)
        (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hcl) ?_ hres
      rw [show ({ db with rules := R, env := mergeEnv a b } : Database)
            = { { db with env := mergeEnv a b } with rules := R } from rfl,
        evalActions_setRules, heval]
      rfl

/-- The merge phase a `rules` update gained runs just as well *before* the update. -/
theorem mergeClosure_setRules {db db' : Database} {R : Set Rule} :
    MergeClosure { db with rules := R } db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := R } := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨db, Relation.ReflTransGen.refl, rfl⟩
    | @tail x y _ hstep ih =>
        obtain ⟨d, hcl, rfl⟩ := ih
        have hstep' : MergeStep d { y with rules := d.rules } :=
          MergeStep.setRules hstep d.rules
        have hrules : y.rules = R := (MergeStep.envRules hstep).2
        exact ⟨{ y with rules := d.rules }, hcl.tail hstep', by rw [← hrules]⟩
  · rintro ⟨d, hcl, rfl⟩
    induction hcl with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (MergeStep.setRules hstep R)

/-- **`.rule` is neutral.** The new step is a merge phase of the pre-state followed by the
old effect: every state it adds is one the *preceding* merge phase already reaches. -/
theorem ruleStep_iff {db db' : Database} {r : Rule} :
    CmdStep db (.rule r) db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := insert r db.rules } := by
  simpa [CmdStep, cmdReach, cmdEffect] using
    mergeClosure_setRules (db := db) (db' := db') (R := insert r db.rules)

/-! #### The invariant `.decl` carries: the declared name occurs nowhere

A **fresh** `f` is named by no existing `:merge`, so no merge body evaluates differently
across the declaration, and no state the phase reaches holds an `f`-headed entry to collide.
The `set` head clause of `Action.Declared` is load-bearing: a head is not in `Expr.fns` and
`evalAction` never checks it, so without the clause a merge body could plant entries of the
name being declared, and the declaration would turn them into a collision. -/

/-- The state-level reading of `Program.MergeDeclared`: every declared merge function's body
and result name only functions the signature already has. `programStep_sigMergeDeclared`
below is where a checked program supplies it. -/
def SigMergeDeclared (sig : Signature) : Prop :=
  ∀ g d ms, sig g = some d → d.merge = some ms → ms.Declared sig

/-- `f` heads `t` or one of its subterms. -/
def Term.Mentions (f : FnName) (t : Term) : Prop := ∃ args, Term.app f args ∈ t.subterms

theorem Term.mentions_head (f : FnName) (args : List Term) : Term.Mentions f (.app f args) :=
  ⟨args, Term.self_mem_subterms _⟩

theorem Term.not_mentions_lit {f : FnName} {l : Lit} : ¬ Term.Mentions f (.lit l) := by
  rintro ⟨args, h⟩; simp at h

theorem Term.mentions_of_subterm {f : FnName} {s t : Term} (h : s ∈ t.subterms)
    (hm : Term.Mentions f s) : Term.Mentions f t := hm.imp fun _ hs => hs.trans h

/-- An application mentions `f` by heading it or through an argument. -/
theorem Term.mentions_app {f g : FnName} {args : List Term}
    (h : Term.Mentions f (.app g args)) : g = f ∨ ∃ a ∈ args, Term.Mentions f a := by
  obtain ⟨cs, hs⟩ := h
  cases hs with
  | refl => exact Or.inl rfl
  | arg hmem hsub => exact Or.inr ⟨_, hmem, cs, hsub⟩

theorem Term.not_mentions_args {f g : FnName} {args : List Term}
    (h : ¬ Term.Mentions f (.app g args)) : ∀ t ∈ args, ¬ Term.Mentions f t :=
  fun t ht hm => h (Term.mentions_of_subterm (Term.arg_subterms ht t.self_mem_subterms) hm)

/-- The invariant a declaration of a fresh `f` carries through its merge phase: no term the
state holds and no value its environment binds applies `f`. -/
structure Database.Avoids (db : Database) (f : FnName) : Prop where
  terms : ∀ t ∈ db.terms, ¬ Term.Mentions f t
  env : ∀ b ∈ db.env, ¬ Term.Mentions f b.2

theorem Database.Avoids.congr {f : FnName} {d₁ d₂ : Database} (heq : d₂.eqs = d₁.eqs)
    (henv : ∀ b ∈ d₂.env, ¬ Term.Mentions f b.2) (h : d₁.Avoids f) : d₂.Avoids f :=
  ⟨fun t ht => h.terms t (Database.mem_terms_of_eqs_eq heq ht), henv⟩

theorem avoids_addTerm {f : FnName} {db : Database} {t : Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s) (ht : ¬ Term.Mentions f t) :
    ∀ s ∈ (db.addTerm t).terms, ¬ Term.Mentions f s := by
  simp only [Database.addTerm_terms, Set.mem_union]
  rintro s (hs | hs)
  · exact hav s hs
  · exact fun hm => ht (Term.mentions_of_subterm hs hm)

theorem avoids_addEq {f : FnName} {db : Database} {a b : Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s) (ha : ¬ Term.Mentions f a)
    (hb : ¬ Term.Mentions f b) : ∀ s ∈ (db.addEq a b).terms, ¬ Term.Mentions f s := by
  simp only [Database.addEq_terms, Set.mem_union]
  rintro s ((hs | hs) | hs)
  · exact hav s hs
  · exact fun hm => ha (Term.mentions_of_subterm hs hm)
  · exact fun hm => hb (Term.mentions_of_subterm hs hm)

/-- **A `DeclaredTerms` state holds no term mentioning an undeclared name**, which is where
the invariant comes from at the declaration itself. -/
theorem avoids_of_declaredTerms {f : FnName} {db : Database} (hf : db.sig f = none)
    (hwf : db.WF) (hdt : db.DeclaredTerms) : db.Avoids f := by
  have key : ∀ (t : Term), t ∈ db.terms → ¬ Term.Mentions f t := by
    intro t
    induction t using Term.recTerm with
    | lit l => intro _; exact Term.not_mentions_lit
    | app g args ih =>
        intro hmem hmen
        rcases Term.mentions_app hmen with rfl | ⟨a, ha, hm⟩
        · obtain ⟨d, hd, -⟩ := hdt g args hmem
          rw [hf] at hd
          exact absurd hd (by simp)
        · exact ih a ha (hwf.subtermClosed _ hmem (Term.IsSubterm.arg ha (.refl _))) hm
  exact ⟨key, fun b hb => key b.2 (hwf.envInTerms b hb)⟩

/-! #### Evaluation builds no term mentioning an undeclared name -/

/-- A primitive returns an operand or a literal, so it builds no new head. -/
theorem prim_result {p : Prim} {ts : List Term} {t : Term} (h : p.apply ts = some t) :
    t ∈ ts ∨ ∃ l, t = Term.lit l := by
  unfold Prim.apply at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl (by split <;> simp)
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem prim_avoids {f : FnName} {p : Prim} {ts : List Term} {t : Term}
    (hts : ∀ s ∈ ts, ¬ Term.Mentions f s) (h : p.apply ts = some t) :
    ¬ Term.Mentions f t := by
  rcases prim_result h with hm | ⟨l, rfl⟩
  · exact hts t hm
  · exact Term.not_mentions_lit

theorem evalList_avoids {sig : Signature} {f : FnName} {σ : Env} :
    ∀ (args : List Expr) (ts : List Term),
      (∀ a ∈ args, ∀ t, a.eval sig σ = some t → ¬ Term.Mentions f t) →
      Expr.evalList sig args σ = some ts → ∀ s ∈ ts, ¬ Term.Mentions f s := by
  intro args
  induction args with
  | nil =>
      intro ts _ h s hs
      rw [Expr.evalList] at h
      rw [← Option.some.inj h] at hs
      simp at hs
  | cons e es ih =>
      intro ts ihe h s hs
      rw [Expr.evalList] at h
      obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts', hts', rfl⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ihe e (List.mem_cons_self ..) _ ht
      · exact ih ts' (fun a ha => ihe a (List.mem_cons_of_mem _ ha)) hts' s hs'

/-- `Expr.eval` builds only heads the signature declares, so an undeclared `f` stays out. -/
theorem eval_avoids {sig : Signature} {f : FnName} {σ : Env} (hf : sig f = none)
    (hσ : ∀ b ∈ σ, ¬ Term.Mentions f b.2) :
    ∀ (e : Expr) (t : Term), e.eval sig σ = some t → ¬ Term.Mentions f t := by
  intro e
  induction e using Expr.recExpr with
  | lit l =>
      intro t h; rw [Expr.eval] at h; rw [← Option.some.inj h]; exact Term.not_mentions_lit
  | var v =>
      intro t h
      rw [Expr.eval] at h
      exact hσ (v, t) (Env.mem_of_lookup h)
  | app g args ih =>
      intro t h
      rw [Expr.eval] at h
      cases hp : Prim.ofName g with
      | some p =>
          rw [hp] at h
          obtain ⟨ts, hts, happ⟩ := Option.bind_eq_some_iff.mp h
          exact prim_avoids (evalList_avoids args ts ih hts) happ
      | none =>
          rw [hp] at h
          by_cases hc : sig.IsCtor g
          · rw [if_pos hc] at h
            obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
            intro hmen
            rcases Term.mentions_app hmen with rfl | ⟨a, ha, hm⟩
            · obtain ⟨d, hd, -⟩ := hc
              rw [hf] at hd
              exact absurd hd (by simp)
            · exact evalList_avoids args ts ih hts _ ha hm
          · rw [if_neg hc] at h; exact absurd h (by simp)

theorem evalAction_avoids {f : FnName} {db d : Database} {a : Action}
    (hf : db.sig f = none) (hd : a.Declared db.sig) (hav : db.Avoids f)
    (h : evalAction db a = some d) : d.Avoids f := by
  cases a with
  | expr e =>
      rw [evalAction] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨avoids_addTerm hav.terms (eval_avoids hf hav.env e t ht), hav.env⟩
  | letBind v e =>
      rw [evalAction] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      have hat := eval_avoids hf hav.env e t ht
      refine Database.Avoids.congr (d₁ := db.addTerm t) rfl (fun b hb => ?_)
        ⟨avoids_addTerm hav.terms hat, hav.env⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hat
      · exact hav.env b hb
  | union e₁ e₂ =>
      rw [evalAction] at h
      obtain ⟨t₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h
        exact ⟨avoids_addEq hav.terms (eval_avoids hf hav.env e₁ t₁ h₁)
          (eval_avoids hf hav.env e₂ t₂ h₂), hav.env⟩
  | set g args out =>
      rw [evalAction] at h
      obtain ⟨as, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨avoids_addTerm hav.terms fun hmen => ?_, hav.env⟩
      rcases Term.mentions_app hmen with rfl | ⟨x, hx, hm⟩
      · exact hd.1 hf
      · rcases List.mem_append.mp hx with hmem | hmem
        · exact evalList_avoids args as
            (fun a _ t ht => eval_avoids hf hav.env a t ht) h₁ _ hmem hm
        · exact evalList_avoids out vs
            (fun a _ t ht => eval_avoids hf hav.env a t ht) h₂ _ hmem hm

theorem evalActions_avoids {f : FnName} :
    ∀ (as : List Action) (db d : Database), db.sig f = none → Actions.Declared as db.sig →
      db.Avoids f → evalActions db as = some d → d.Avoids f := by
  intro as
  induction as with
  | nil => intro db d _ _ hav h; rw [evalActions] at h; rw [← Option.some.inj h]; exact hav
  | cons a as ih =>
      intro db d hf hd hav h
      rw [evalActions] at h
      obtain ⟨db', h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      have hsig : db'.sig = db.sig := evalAction_sig h₁
      exact ih db' d (by rw [hsig]; exact hf) (by rw [hsig]; exact hd.2)
        (evalAction_avoids hf hd.1 hav h₁) h₂

/-- **A merge step preserves the invariant.** The body it runs is `Declared` in a signature
`f` is not in, so neither the body nor the result can build an `f`-headed term, and the two
colliding rows do not hold one. -/
theorem mergeStep_avoids {f : FnName} {db x : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f) (h : MergeStep db x) : x.Avoids f := by
  cases h with
  | @collide d g decl as bs a b vs body res hsig hmerge _ _ _ hta htb _ heval hres =>
      have hgf : g ≠ f := by rintro rfl; rw [hf] at hsig; exact absurd hsig (by simp)
      have hdec := hsmd g decl (.merge body res) hsig hmerge
      have hta' := hav.terms _ hta
      have htb' := hav.terms _ htb
      have hmenv : ∀ p ∈ mergeEnv a b, ¬ Term.Mentions f p.2 := by
        intro p hp
        rcases mem_mergeEnv hp with hm | hm
        · exact Term.not_mentions_args hta' _ (List.mem_append_right _ hm)
        · exact Term.not_mentions_args htb' _ (List.mem_append_right _ hm)
      have hdav : d.Avoids f :=
        evalActions_avoids body { db with env := mergeEnv a b } d hf hdec.1
          (Database.Avoids.congr (d₁ := db) rfl hmenv hav) heval
      have hdsig : d.sig = db.sig := evalActions_sig (db := { db with env := mergeEnv a b }) heval
      have hvs : ∀ v ∈ vs, ¬ Term.Mentions f v :=
        evalList_avoids res vs
          (fun e _ t ht => eval_avoids (by rw [hdsig]; exact hf) hdav.env e t ht) hres
      refine Database.Avoids.congr (d₁ := d.addTerm (.app g (as ++ vs))) rfl hav.env
        ⟨avoids_addTerm hdav.terms fun hmen => ?_, hdav.env⟩
      rcases Term.mentions_app hmen with rfl | ⟨x, hx, hm⟩
      · exact hgf rfl
      · rcases List.mem_append.mp hx with hmem | hmem
        · exact Term.not_mentions_args hta' _ (List.mem_append_left _ hmem) hm
        · exact hvs _ hmem hm

theorem mergeClosure_avoids {f : FnName} {db d : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f) (h : MergeClosure db d) :
    d.Avoids f := by
  induction h with
  | refl => exact hav
  | @tail p q hcl hstep ih =>
      have hpsig : p.sig = db.sig := MergeClosure.sig hcl
      exact mergeStep_avoids (by rw [hpsig]; exact hf) (by rw [hpsig]; exact hsmd) ih hstep

/-! #### The declaration commutes with its merge phase -/

theorem evalList_update {sig sig' : Signature} {σ : Env} :
    ∀ (args : List Expr), (∀ a ∈ args, a.eval sig σ = a.eval sig' σ) →
      Expr.evalList sig args σ = Expr.evalList sig' args σ
  | [], _ => rfl
  | e :: es, h => by
      rw [Expr.evalList, Expr.evalList, h e (List.mem_cons_self ..),
        evalList_update es fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- Declaring a name a `Declared` expression cannot mention leaves its value alone. -/
theorem eval_update {sig sig' : Signature} {f : FnName} (hf : sig f = none)
    (hag : ∀ g, g ≠ f → sig g = sig' g) :
    ∀ (e : Expr), e.Declared sig → ∀ (σ : Env), e.eval sig σ = e.eval sig' σ := by
  intro e
  induction e using Expr.recExpr with
  | lit l => intro _ σ; rfl
  | var v => intro _ σ; rfl
  | app g args ih =>
      intro hdec σ
      have hargs : ∀ a ∈ args, a.Declared sig := fun a ha x hx =>
        hdec x (by rw [Expr.fns]; exact List.mem_cons_of_mem _ (Expr.fns_subset_fnsList ha hx))
      have hlist : Expr.evalList sig args σ = Expr.evalList sig' args σ :=
        evalList_update args fun a ha => ih a ha (hargs a ha) σ
      rw [Expr.eval, Expr.eval, hlist]
      cases hp : Prim.ofName g with
      | some p => rfl
      | none =>
          have hgf : g ≠ f := by
            rintro rfl
            rcases hdec g (by rw [Expr.fns]; exact List.mem_cons_self ..) with h | h
            · exact h hp
            · exact h hf
          have hiff : sig.IsCtor g ↔ sig'.IsCtor g := by
            simp only [Signature.IsCtor, hag g hgf]
          by_cases hc : sig.IsCtor g
          · rw [if_pos hc, if_pos (hiff.mp hc)]
          · rw [if_neg hc, if_neg fun h => hc (hiff.mpr h)]

theorem evalAction_update {f : FnName} {sig' : Signature} {db : Database} {a : Action}
    (hf : db.sig f = none) (hag : ∀ g, g ≠ f → db.sig g = sig' g) (hd : a.Declared db.sig) :
    evalAction { db with sig := sig' } a
      = (evalAction db a).map fun d => { d with sig := sig' } := by
  cases a with
  | expr e =>
      have he := eval_update hf hag e hd db.env
      cases h : e.eval db.sig db.env <;> simp [evalAction, ← he, h, Database.addTerm]
  | letBind v e =>
      have he := eval_update hf hag e hd db.env
      cases h : e.eval db.sig db.env <;> simp [evalAction, ← he, h, Database.addTerm]
  | union e₁ e₂ =>
      have h₁ := eval_update hf hag e₁ hd.1 db.env
      have h₂ := eval_update hf hag e₂ hd.2 db.env
      cases hc₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, ← h₁, hc₁]
      | some t₁ =>
          cases hc₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, ← h₁, ← h₂, hc₁, hc₂]
          | some t₂ =>
              simp only [evalAction, ← h₁, ← h₂, hc₁, hc₂, Option.bind_some]
              split <;> simp [Database.addEq, Database.addTerm]
  | set g args out =>
      have h₁ := evalList_update (sig := db.sig) (sig' := sig') (σ := db.env) args
        fun a ha => eval_update hf hag a (hd.2.1 a ha) db.env
      have h₂ := evalList_update (sig := db.sig) (sig' := sig') (σ := db.env) out
        fun a ha => eval_update hf hag a (hd.2.2 a ha) db.env
      cases hc₁ : Expr.evalList db.sig args db.env <;>
        cases hc₂ : Expr.evalList db.sig out db.env <;>
          simp [evalAction, ← h₁, ← h₂, hc₁, hc₂, Database.addTerm]

theorem evalActions_update {f : FnName} {sig' : Signature} :
    ∀ (as : List Action) (db : Database), db.sig f = none →
      (∀ g, g ≠ f → db.sig g = sig' g) → Actions.Declared as db.sig →
      evalActions { db with sig := sig' } as
        = (evalActions db as).map fun d => { d with sig := sig' } := by
  intro as
  induction as with
  | nil => intro db _ _ _; simp [evalActions]
  | cons a as ih =>
      intro db hf hag hd
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_update hf hag hd.1, h]
      | some d =>
          have hsig : d.sig = db.sig := evalAction_sig h
          have hstep : evalActions { db with sig := sig' } (a :: as)
              = evalActions { d with sig := sig' } as := by
            simp [evalActions, evalAction_update hf hag hd.1, h]
          rw [hstep, ih d (by rw [hsig]; exact hf) (by rw [hsig]; exact hag)
            (by rw [hsig]; exact hd.2)]
          simp [evalActions, h]

theorem mergeStep_update_iff {f : FnName} {fd : FnDecl} {db x : Database}
    (hf : db.sig f = none) (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f) :
    MergeStep { db with sig := Function.update db.sig f (some fd) } x ↔
      ∃ y, MergeStep db y ∧ x = { y with sig := Function.update db.sig f (some fd) } := by
  have hag : ∀ g, g ≠ f → db.sig g = Function.update db.sig f (some fd) g :=
    fun g hg => (Function.update_of_ne hg _ _).symm
  set sig' := Function.update db.sig f (some fd) with hsig'
  constructor
  · intro h
    cases h with
    | @collide d g decl as bs a b vs body res hsig hmerge hcf harity hbrity hta htb hcl
        heval hres =>
        have hsigg : sig' g = some decl := hsig
        have hta' : Term.app g (as ++ a) ∈ db.terms :=
          Database.mem_terms_of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl hta
        have htb' : Term.app g (bs ++ b) ∈ db.terms :=
          Database.mem_terms_of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl htb
        have hcl' : CongList db as bs :=
          CongList.of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl hcl
        have hgf : g ≠ f := by
          rintro rfl; exact hav.terms _ hta' (Term.mentions_head _ _)
        rw [hsig', Function.update_of_ne hgf] at hsigg
        have hdec := hsmd g decl (.merge body res) hsigg hmerge
        have heval' : evalActions { { db with env := mergeEnv a b } with sig := sig' } body
            = some d := heval
        rw [evalActions_update body { db with env := mergeEnv a b } hf hag hdec.1] at heval'
        obtain ⟨d₀, hd₀, rfl⟩ := Option.map_eq_some_iff.mp heval'
        have hd₀sig : d₀.sig = db.sig :=
          evalActions_sig (db := { db with env := mergeEnv a b }) hd₀
        have hres' : Expr.evalList sig' res d₀.env = some vs := hres
        refine ⟨_, MergeStep.collide hsigg hmerge hcf harity hbrity hta' htb' hcl' hd₀ ?_, rfl⟩
        refine Eq.trans ?_ hres'
        exact evalList_update res fun e he =>
          eval_update (by rw [hd₀sig]; exact hf) (by rw [hd₀sig]; exact hag) e
            (by rw [hd₀sig]; exact hdec.2 e he) d₀.env
  · rintro ⟨y, h, rfl⟩
    cases h with
    | @collide d g decl as bs a b vs body res hsig hmerge hcf harity hbrity hta htb hcl
        heval hres =>
        have hgf : g ≠ f := by rintro rfl; rw [hf] at hsig; exact absurd hsig (by simp)
        have hdec := hsmd g decl (.merge body res) hsig hmerge
        have hdsig : d.sig = db.sig :=
          evalActions_sig (db := { db with env := mergeEnv a b }) heval
        refine MergeStep.collide (d := { d with sig := sig' })
          (show sig' g = some decl by rw [hsig', Function.update_of_ne hgf]; exact hsig)
          hmerge hcf harity hbrity
          (Database.mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl hta)
          (Database.mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl htb)
          (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl hcl) ?_ ?_
        · change evalActions { { db with env := mergeEnv a b } with sig := sig' } body
            = some { d with sig := sig' }
          rw [evalActions_update body { db with env := mergeEnv a b } hf hag hdec.1, heval]
          rfl
        · change Expr.evalList sig' res d.env = some vs
          refine Eq.trans ?_ hres
          exact (evalList_update res fun e he =>
            eval_update (by rw [hdsig]; exact hf) (by rw [hdsig]; exact hag) e
              (by rw [hdsig]; exact hdec.2 e he) d.env).symm

theorem mergeClosure_setSig {f : FnName} {fd : FnDecl} {db db' : Database}
    (hf : db.sig f = none) (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f) :
    MergeClosure { db with sig := Function.update db.sig f (some fd) } db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with sig := Function.update db.sig f (some fd) } := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨db, Relation.ReflTransGen.refl, rfl⟩
    | @tail _ q _ hstep ih =>
        obtain ⟨d, hcl, rfl⟩ := ih
        have hdsig : d.sig = db.sig := MergeClosure.sig hcl
        have hiff := mergeStep_update_iff (f := f) (fd := fd) (db := d) (x := q)
          (by rw [hdsig]; exact hf) (by rw [hdsig]; exact hsmd)
          (mergeClosure_avoids hf hsmd hav hcl)
        rw [hdsig] at hiff
        obtain ⟨y, hy, rfl⟩ := hiff.mp hstep
        exact ⟨y, hcl.tail hy, rfl⟩
  · rintro ⟨d, hcl, rfl⟩
    induction hcl with
    | refl => exact Relation.ReflTransGen.refl
    | @tail p q hcl hstep ih =>
        have hpsig : p.sig = db.sig := MergeClosure.sig hcl
        have hiff := mergeStep_update_iff (f := f) (fd := fd) (db := p)
          (x := { q with sig := Function.update db.sig f (some fd) })
          (by rw [hpsig]; exact hf) (by rw [hpsig]; exact hsmd)
          (mergeClosure_avoids hf hsmd hav hcl)
        rw [hpsig] at hiff
        exact ih.tail (hiff.mpr ⟨q, hstep, rfl⟩)

/-- **`.decl` is neutral.** Under the checks — the declared name fresh, every `:merge` in
the signature declared, the state well-formed — the merge phase the declaration gained is
one the *preceding* merge phase already reaches. -/
theorem declStep_iff {db db' : Database} {f : FnName} {fd : FnDecl} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hwf : db.WF) (hdt : db.DeclaredTerms) :
    CmdStep db (.decl f fd) db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with sig := Function.update db.sig f (some fd) } := by
  simpa [CmdStep, cmdReach, cmdEffect] using
    mergeClosure_setSig (fd := fd) hf hsmd (avoids_of_declaredTerms hf hwf hdt)

/-! #### `Program.MergeDeclared` supplies `declStep_iff`'s hypothesis -/

/-- `Cmd.MergeDeclared` establishes the invariant: the new function's `:merge` is checked
against the signature it is already in, and every older one still resolves. -/
theorem sigMergeDeclared_decl {sig : Signature} {f : FnName} {d : FnDecl}
    (h : SigMergeDeclared sig) (hc : Cmd.MergeDeclared (.decl f d) sig) :
    SigMergeDeclared (Function.update sig f (some d)) := by
  have hm : Signature.Extends (Function.update sig f (some d)) sig :=
    Signature.extends_sigBind sig (.decl f d)
  intro g d' ms hg hms
  by_cases hgf : g = f
  · subst hgf
    rw [Function.update_self] at hg
    obtain rfl := Option.some.inj hg
    exact hc ms hms
  · rw [Function.update_of_ne hgf] at hg
    exact MergeSpec.Declared.mono hm (h g d' ms hg hms)

theorem cmdStep_sigMergeDeclared {db d : Database} {c : Cmd} (hsmd : SigMergeDeclared db.sig)
    (hc : c.MergeDeclared db.sig) (h : CmdStep db c d) : SigMergeDeclared d.sig := by
  rw [CmdStep.sig h]
  cases c with
  | action a => exact hsmd
  | rule r => exact hsmd
  | run R => exact hsmd
  | saturate R => exact hsmd
  | decl g d' => exact sigMergeDeclared_decl hsmd hc

/-- Every state a checked program reaches satisfies the invariant, so `declStep_iff` covers
every `.decl` such a program runs. -/
theorem programStep_sigMergeDeclared : ∀ {db d : Database} {p : Program}, ProgramStep db p d →
    SigMergeDeclared db.sig → Program.MergeDeclared p db.sig → SigMergeDeclared d.sig := by
  intro db d p h
  induction h with
  | nil => exact fun hsmd _ => hsmd
  | @cons db x _ c _ hstep _ ih =>
      intro hsmd hp
      exact ih (cmdStep_sigMergeDeclared hsmd hp.1 hstep)
        (by rw [CmdStep.sig hstep]; exact hp.2)

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
  obtain ⟨e₁, hr₁, hcl₁⟩ := h₁
  obtain ⟨e₂, hr₂, hcl₂⟩ := h₂
  obtain rfl := cmdReach_det hsig hr₁ hr₂
  have hs := cmdReach_allConstructors hsig hdecl hr₁
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
