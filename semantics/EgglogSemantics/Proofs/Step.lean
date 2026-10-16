import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Match

namespace Egglog

variable {oldVars newVars : List Var}
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
  fun f hf => hs f (h f hf)

theorem Action.Declared.mono {a : Action} {sig sig' : Signature} (hs : sig'.Extends sig)
    (h : a.Declared sig) : a.Declared sig' := by
  cases a with
  | expr e => exact Expr.Declared.mono hs h
  | union e₁ e₂ => exact ⟨Expr.Declared.mono hs h.1, Expr.Declared.mono hs h.2⟩

theorem Actions.Declared.mono : ∀ {as : List Action} {sig sig' : Signature},
    sig'.Extends sig → Actions.Declared as sig → Actions.Declared as sig'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hs, h => ⟨h.1.mono hs, Actions.Declared.mono hs h.2⟩

@[inherit_doc Expr.Declared.mono]
theorem MergeSpec.Declared.mono {ms : MergeSpec} {sig sig' : Signature}
    (hs : sig'.Extends sig) (h : ms.Declared sig) : ms.Declared sig' := by
  cases ms with
  | merge oldVars newVars body res =>
    exact ⟨Actions.Declared.mono hs h.1, fun e he => Expr.Declared.mono hs (h.2 e he)⟩

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

theorem MergeValues.sig {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) : d.sig = db.sig := by
  cases h with
  | unchanged => rfl
  | changed _ _ hb _ => have hs := evalActions_sig hb; exact hs

theorem MergeValues.envRules {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) : d.env = db.env ∧ d.rules = db.rules := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem MergeValues.contained {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) : db.Contained d := by
  cases h with
  | unchanged => exact .refl _
  | changed _ _ hb _ => exact ⟨(evalActions_contained hb).eqs⟩

theorem MergeValues.merge_ne_none {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) : decl.merge ≠ none := by
  cases h with
  | unchanged hm _ | changed hm _ _ _ => simp [hm]

theorem MergeStep.sig {d₁ d₂ : Database} (h : MergeStep d₁ d₂) : d₂.sig = d₁.sig := by
  cases h with
  | collide _ _ _ _ _ _ hv =>
      simpa only [Database.putEntry_sig, Database.eraseEntry_sig]
        using hv.sig

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
  | collide _ _ _ _ _ _ hv =>
      simpa only [Database.putEntry_env, Database.putEntry_rules, Database.eraseEntry_env,
        Database.eraseEntry_rules]
        using hv.envRules

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-- Every merge binding is an output of one of the colliding rows. Subterm closure
therefore puts the whole merge environment in the database before the body runs. -/
theorem mem_mergeEnv {os ns : List Term} {p : Var × Term}
    (h : p ∈ mergeEnv oldVars newVars os ns) : p.2 ∈ os ∨ p.2 ∈ ns := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (List.of_mem_zip h).2
  · exact Or.inr (List.of_mem_zip h).2

def Signature.MergesWidthOk (sig : Signature) : Prop :=
  ∀ g dc ms, sig g = some dc → dc.merge = some ms → MergeSpec.WidthOk ms dc.outArity sig

theorem MergeValues.storeOk {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) (hs : db.StoreOk)
    (ho : ∀ t ∈ old, t.IsValue db.sig) (hn : ∀ t ∈ new, t.IsValue db.sig) : d.StoreOk := by
  cases h with
  | unchanged => exact hs
  | @changed post vs ovs nvs body res _ _ hb _ =>
      have hstart : ({ db with env := mergeEnv ovs nvs old new } : Database).StoreOk :=
        hs.setEnv (fun b hb => (mem_mergeEnv hb).elim (ho b.2) (hn b.2))
      exact (evalActions_storeOk hstart hb).congr rfl rfl (by
        simpa only [evalActions_sig hb] using hs.envValues)

theorem MergeValues.output_values {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) (ho : ∀ t ∈ old, t.IsValue db.sig) :
    ∀ t ∈ vs, t.IsValue d.sig := by
  cases h with
  | unchanged => exact ho
  | changed _ _ _ hr => exact Expr.evalList_isValue hr

theorem MergeStep.storeOk {db d : Database} (h : MergeStep db d) (hs : db.StoreOk)
    (hw : db.sig.MergesWidthOk) : d.StoreOk := by
  cases h with
  | @collide post old new decl vs ho hn _ _ hd _ hv =>
      have hs' := (hs.eraseEntry old ho.1).eraseEntry new hn.1
      have hpost := hv.storeOk hs' ho.1.output_values hn.1.output_values
      apply hpost.putEntry
      have hlen : vs.length = old.value.length := by
        obtain ⟨dc, hdc, _, _, hlen, _⟩ := ho.1
        have he : dc = decl := Option.some.inj (hdc.symm.trans hd)
        subst dc
        cases hv with
        | unchanged => rfl
        | changed hm _ _ hr =>
            exact (Expr.evalList_length hr).trans ((hw _ _ _ hd hm).1.trans hlen.symm)
      simpa only [hv.sig, Database.eraseEntry_sig] using ho.1.with_value hlen
        (by simpa only [hv.sig, Database.eraseEntry_sig] using hv.output_values ho.1.output_values)

theorem MergeClosure.storeOk {db d : Database} (h : MergeClosure db d) (hs : db.StoreOk)
    (hw : db.sig.MergesWidthOk) : d.StoreOk := by
  induction h with
  | refl => exact hs
  | tail hc hm ih => exact hm.storeOk ih (by rw [MergeClosure.sig hc]; exact hw)

/-- **A `:merge` expression with no `:internal-identity-vals` conflicts on every pair**: it
has no action block, so `FnDecl.unchangedWidth` gives it no width and every collision
resolves. This is the whole of `MergeConflict` on the fragment `Signature.OrderingFree`
admits. -/
theorem mergeConflict_of_ordering_free {decl : FnDecl} (h : decl.OrderingFree)
    {body : List Action} {res : List Expr} (hm : decl.merge = some (.merge oldVars
      newVars body res))
    (a b : List Term) : MergeConflict decl body a b := by
  obtain ⟨hid, hms⟩ := h
  obtain ⟨hbody, -⟩ := hms (.merge oldVars newVars body res) (by rw [hm]; rfl)
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
  have hn : ∀ f dc, db.sig f = some dc → dc.merge = none := by
    intro f dc hd
    have hh := hsig f
    rwa [Signature.mergeOf, hd, Option.bind_some] at hh
  cases h with
  | collide _ _ _ _ hd _ hv =>
      exact hv.merge_ne_none (hn _ _ hd)

/-- Constructor-only signatures cannot have function entries in a valid store. -/
theorem Database.StoreOk.empty_tables {db : Database} (h : db.StoreOk)
    (hc : db.sig.AllConstructors) : db.entries = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro row hr
  obtain ⟨decl, hd, hm⟩ := h.declared row hr
  have hh := hc row.name
  rw [Signature.mergeOf, hd, Option.bind_some] at hh
  exact hm hh

theorem Database.StoreOk.mergeNormal {db : Database} (h : db.StoreOk)
    (hc : db.sig.AllConstructors) : MergeNormal db := by
  intro row hr
  simp [h.empty_tables hc] at hr

/-- A normal store has no pair of distinct colliding entries. -/
theorem MergeStep.not_of_mergeNormal {db db' : Database}
    (hn : MergeNormal db) (h : MergeStep db db') : False := by
  cases h with
  | collide ha hb hne hname _ hk _ => exact hne (hn _ ha _ hb hname hk)

theorem MergeClosure.eq_of_allConstructors {db db' : Database}
    (hsig : db.sig.AllConstructors) (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (MergeStep.not_of_allConstructors hsig (ih ▸ hstep)).elim

/-- **A merge phase out of a merge-saturated state is the identity.** The other reason a
merge closure collapses, and the one that makes `CmdStep`'s trailing phase neutral after a
`Cmd.saturate` — which is how the uniform phase survives the new command. -/
theorem MergeClosure.eq_of_mergeNormal {db db' : Database} (hs : MergeNormal db)
    (h : MergeClosure db db') : db' = db := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; exact (hstep.not_of_mergeNormal hs).elim

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

theorem RuleResults.entries_subset {db d : Database} {r : Rule} (h : d ∈ RuleResults db r) :
    db.entries ⊆ d.entries := by
  obtain ⟨σ, _, hs⟩ := h
  exact evalLocalActions_entries_subset hs

theorem RunRules.entries_subset {R : RulesetName} {db : Database} :
    db.entries ⊆ (RunRules R db).entries := fun _ hr => ⟨hr.1, Or.inl hr.2⟩

/-- A round is unchanged exactly when each firing adds no assertion. -/
theorem runRules_eq_self_iff (R : RulesetName) (db : Database) :
    RunRules R db = db ↔
      ∀ r ∈ db.rules, r.ruleset = R → ∀ d ∈ RuleResults db r,
        Database.Contained d db := by
  constructor
  · intro h r hr hR d hd
    have hmem : d ∈ {d | ∃ r ∈ db.rules, r.ruleset = R ∧ d ∈ RuleResults db r} :=
      ⟨r, hr, hR, hd⟩
    have he : d.eqs ⊆ (RunRules R db).eqs := fun _ hp =>
      Or.inr (Set.mem_biUnion hmem hp)
    rw [h] at he
    exact ⟨he⟩
  · intro h
    refine Database.ext rfl ?_ rfl rfl
    refine Set.Subset.antisymm ?_ Set.subset_union_left
    rintro p (hp | hp)
    · exact hp
    · obtain ⟨d, ⟨r, hr, hR, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (h r hr hR d hd).eqs hp

/-! ### A saturating run

`Cmd.saturate` is a fixpoint condition rather than a function, so the three facts every
command needs — the signature it leaves, the constructor fragment it keeps, and determinism
there — are proved for its *rounds* instead. Each is an induction along
`Relation.ReflTransGen (RunStep R)`. -/
theorem RunStep.sig {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.sig = db.sig := by
  rw [MergeClosure.sig h.1, RunRules.sig]

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
  MergeClosure.eq_of_allConstructors (by rw [RunRules.sig]; exact hsig) h.1

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
  induction h₁ with
  | done hs hm =>
      cases h₂ with
      | done hs' _ =>
          exact (hs.eq_of_allConstructors hsig).trans (hs'.eq_of_allConstructors hsig).symm
      | step hs' hne _ =>
          have heq := (hs.eq_of_allConstructors hsig).trans
            (hs'.eq_of_allConstructors hsig).symm
          exact (hne (heq ▸ hm)).elim
  | step hs hne htail ih =>
      cases h₂ with
      | done hs' hm =>
          have heq := (hs'.eq_of_allConstructors hsig).trans
            (hs.eq_of_allConstructors hsig).symm
          exact (hne (heq ▸ hm)).elim
      | step hs' _ htail' =>
          have heq := (hs.eq_of_allConstructors hsig).trans
            (hs'.eq_of_allConstructors hsig).symm
          subst heq
          exact ih (by rw [hs.sig]; exact hsig) htail'

/-! ### What a command reaches

`cmdReach` is a function's graph on four commands out of five and a fixpoint condition on
`Cmd.saturate`. Absorbing the split here is what keeps it out of `CmdStep`'s proofs
below. -/
theorem cmdReach_sig {db d : Database} {c : Cmd} (h : cmdReach db c d) :
    d.sig = c.sigBind db.sig := by
  cases c with
  | action a => exact evalAction_sig h
  | rule r => subst h; rfl
  | run R => subst h; rfl
  | saturate R => exact RunReach.sig (show SaturateReach R db d from h).reach
  | decl f dc => subst h; rfl
  | check q => rw [(h : QueryHolds db q ∧ d = db).2]; rfl

/-- Well-formedness through every command but a saturating run, whose rounds need
`CtorState` (`cmdReach_ctorState`). -/
theorem cmdReach_wf {db d : Database} (hw : db.WF) {c : Cmd} (hns : c.NoSaturate)
    (h : cmdReach db c d) : d.WF := by
  cases c with
  | action a => exact evalAction_wf hw h
  | rule r => subst h; exact hw.congr rfl rfl
  | run R => subst h; exact RunRules.wf hw
  | saturate R => exact (hns : False).elim
  | decl f dc => subst h; exact hw.congr rfl rfl
  | check q => rw [(h : QueryHolds db q ∧ d = db).2]; exact hw

theorem cmdReach_allConstructors {db d : Database} (hsig : db.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (h : cmdReach db c d) : d.sig.AllConstructors := by
  rw [cmdReach_sig h]; exact hsig.sigBind hdecl

theorem cmdReach_ctorState {db d : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hr : cmdReach db c d) : d.CtorState := by
  refine ⟨?_, cmdReach_allConstructors h.sig hdecl hr⟩
  cases c with
  | saturate R => exact (RunReach.ctorState h (show SaturateReach R db d from hr).reach).wf
  | _ => exact cmdReach_wf h.wf (by trivial) hr

/-- What a command reaches is unique on the constructor fragment: four commands are
functions, and a saturating run's fixpoint is unique by `saturateReach_det`. -/
theorem cmdReach_det {db e₁ e₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (h₁ : cmdReach db c e₁) (h₂ : cmdReach db c e₂) : e₁ = e₂ := by
  cases c with
  | saturate R => exact saturateReach_det hsig h₁ h₂
  | action a => exact Option.some.inj (h₁.symm.trans h₂)
  | rule _ | run _ | decl _ _ => exact h₁.trans h₂.symm
  | check q => exact h₁.2.trans h₂.2.symm

/-! ### The step relations

The step relations are the semantics, so what is proved about them here is what a program
run leaves. -/
/-- Rule rounds preserve the surrounding evaluation context. -/
theorem RunStep.env {R : RulesetName} {db db' : Database} (h : RunStep R db db') :
    db'.env = db.env := (MergeClosure.envRules h.1).1

/-- Repeated rule rounds preserve the surrounding evaluation context. -/
theorem RunReach.env {R : RulesetName} {db db' : Database}
    (h : Relation.ReflTransGen (RunStep R) db db') : db'.env = db.env := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact hs.env.trans ih

/-- No command introduces persistent variable bindings. -/
theorem CmdStep.env {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.env = db.env := by
  obtain ⟨d, he, hm⟩ := h.reach
  refine (MergeClosure.envRules hm).1.trans ?_
  cases c with
  | action a => exact evalAction_env he
  | saturate R => exact RunReach.env (show SaturateReach R db d from he).reach
  | rule r => subst he; rfl
  | run R => subst he; rfl
  | decl f dc => subst he; rfl
  | check q => rw [(he : QueryHolds db q ∧ d = db).2]

/-- A program keeps its initial context; in particular, an ordinary run leaves it empty. -/
theorem ProgramStep.env {db db' : Database} {p : Program} (h : ProgramStep db p db') :
    db'.env = db.env := by
  induction h with
  | nil => rfl
  | cons hc _ ih => exact ih.trans hc.env

theorem CmdStep.sig {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db'.sig = c.sigBind db.sig := by
  obtain ⟨d, hreach, hcl⟩ := h.reach
  rw [hcl.sig]; exact cmdReach_sig hreach

/-- **A command keeps the constructor fragment's state, with no condition on its actions.**
The one thing that has to be excluded is the *declaration* of a `:merge` function, which is
`Cmd.CtorDecl`; a `set` cannot disturb either field. -/
theorem CmdStep.ctorState {db db' : Database} (h : db.CtorState) {c : Cmd}
    (hdecl : c.CtorDecl) (hstep : CmdStep db c db') : db'.CtorState := by
  obtain ⟨d, hreach, hcl⟩ := hstep.reach
  have hd := cmdReach_ctorState h hdecl hreach
  rw [hcl.eq_of_allConstructors hd.sig]
  exact hd

/-- **`CmdStep`'s trailing merge phase is neutral on `Cmd.saturate`.** `SaturateReach`
already ends merge-saturated, so the phase that `.rule` and `.decl` pay for uniformly is
free here too, and `CmdStep` stays one `def` over all five commands. -/
theorem cmdStep_saturate_iff {R : RulesetName} {db db' : Database} :
    CmdStep db (.saturate R) db' ↔ SaturateReach R db db' := by
  constructor
  · rintro ⟨d, hr, hcl, _⟩
    have hreach : SaturateReach R db d := hr
    rw [hcl.eq_of_mergeNormal hreach.mergeNormal]
    exact hreach
  · intro h
    exact ⟨db', h, .refl, h.mergeNormal⟩

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
  | expr e =>
      cases h : e.evalAtom db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | union e₁ e₂ =>
      cases h₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, h₁]
      | some t₁ =>
          cases h₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, h₁, h₂]
          | some t₂ =>
              simp only [evalAction, h₁, h₂, Option.bind_some]
              split <;> simp [Database.addEq]

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

theorem MergeValues.setRules {db d : Database} {decl : FnDecl} {old new vs : List Term}
    (h : MergeValues db decl old new d vs) (R : Set Rule) :
    MergeValues { db with rules := R } decl old new { d with rules := R } vs := by
  cases h with
  | unchanged hm hc => exact .unchanged hm hc
  | @changed post vs ovs nvs body res hm hc hb hr =>
      apply MergeValues.changed (d := { post with rules := R }) hm hc ?_ hr
      change evalActions { { db with env := mergeEnv ovs nvs old new } with rules := R } body = _
      rw [evalActions_setRules, hb]
      rfl

theorem MergeStep.setRules {db db' : Database} (h : MergeStep db db') (R : Set Rule) :
    MergeStep { db with rules := R } { db' with rules := R } := by
  cases h with
  | @collide d old new decl vs ho hn hne hname hd hk hv =>
      rw [← Database.putEntry_setRules]
      exact MergeStep.collide (db := { db with rules := R }) ho hn hne hname hd
        (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hk) (hv.setRules R)

/-- Normality depends on current entries and equations. -/
theorem MergeNormal.setRules {db : Database} (h : MergeNormal db) (R : Set Rule) :
    MergeNormal { db with rules := R } := by
  intro a ha b hb hn hk
  exact h a ha b hb hn (CongList.of_eqs_eq (d₁ := { db with rules := R }) (d₂ := db) rfl hk)

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
      ∃ d, MergeNormalize db d ∧ db' = { d with rules := insert r db.rules } := by
  constructor
  · rintro ⟨mid, rfl, hcl, hn⟩
    obtain ⟨d, hd, rfl⟩ := mergeClosure_setRules.mp hcl
    have hdn : MergeNormal d := by
      have hh := hn.setRules d.rules
      exact hh
    exact ⟨d, ⟨hd, hdn⟩, rfl⟩
  · rintro ⟨d, ⟨hd, hn⟩, rfl⟩
    exact ⟨_, rfl, mergeClosure_setRules.mpr ⟨d, hd, rfl⟩,
      hn.setRules (insert r db.rules)⟩

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
theorem avoids_addTerms {f : FnName} {db : Database} {ts : List Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s)
    (ht : ∀ t ∈ ts, ¬ Term.Mentions f t) :
    ∀ s ∈ (db.addTerms ts).terms, ¬ Term.Mentions f s := by
  intro s hs
  rw [Database.addTerms_terms] at hs
  rcases hs with hs | ⟨t, hm, hs⟩
  · exact hav s hs
  · exact fun hmen => ht t hm (Term.mentions_of_subterm hs hmen)

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
      exact hσ (v, t) (Env.mem_of_lookup (Option.filter_eq_some_iff.mp h).1)
  | app g args ih =>
      intro t h
      rw [Expr.eval] at h
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
  | min a b iha ihb =>
      intro t h
      rw [Expr.eval_min] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      rcases Term.least_eq_or x y with hl | hl <;> rw [hl]
      · exact iha x hx
      · exact ihb y hy

theorem evalAtom_avoids {sig : Signature} {f : FnName} {σ : Env} (hf : sig f = none)
    (hσ : ∀ b ∈ σ, ¬ Term.Mentions f b.2) (e : Expr) (t : Term)
    (h : e.evalAtom sig σ = some t) : ¬ Term.Mentions f t := by
  cases e with
  | lit l => exact eval_avoids hf hσ (.lit l) t h
  | var v => exact eval_avoids hf hσ (.var v) t h
  | min a b => exact eval_avoids hf hσ (.min a b) t h
  | app g args =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      intro hm
      rcases Term.mentions_app hm with rfl | ⟨a, ha, hm⟩
      · simp [hf] at hd
      · exact evalList_avoids args ts (fun a _ => eval_avoids hf hσ a) hts a ha hm
    · simp at h

theorem evalAction_avoids {f : FnName} {db d : Database} {a : Action}
    (hf : db.sig f = none) (_hd : a.Declared db.sig) (hav : db.Avoids f)
    (h : evalAction db a = some d) : d.Avoids f := by
  rcases evalAction_eq_some h with ⟨e, t, _, ht, rfl⟩ |
    ⟨e₁, e₂, t₁, t₂, _, ht₁, ht₂, _, rfl⟩
  · exact ⟨avoids_addTerm hav.terms (evalAtom_avoids hf hav.env e t ht), hav.env⟩
  · exact ⟨avoids_addEq hav.terms (eval_avoids hf hav.env e₁ t₁ ht₁)
      (eval_avoids hf hav.env e₂ t₂ ht₂), hav.env⟩

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

/-- A merge body and its result avoid an undeclared name when their incoming values do. -/
theorem mergeValues_avoids {f : FnName} {db d : Database} {decl : FnDecl}
    {old new vs : List Term} (hf : db.sig f = none) (hd : ∀ ms, decl.merge = some ms →
      ms.Declared db.sig) (hav : db.Avoids f)
    (ho : ∀ t ∈ old, ¬ Term.Mentions f t) (hn : ∀ t ∈ new, ¬ Term.Mentions f t)
    (h : MergeValues db decl old new d vs) :
    d.Avoids f ∧ ∀ t ∈ vs, ¬ Term.Mentions f t := by
  cases h with
  | unchanged => exact ⟨hav, ho⟩
  | @changed post vs ovs nvs body res hm _ hb hr =>
      have henv : ∀ p ∈ mergeEnv ovs nvs old new, ¬ Term.Mentions f p.2 := by
        intro p hp
        exact (mem_mergeEnv hp).elim (ho p.2) (hn p.2)
      have hpost := evalActions_avoids body { db with env := mergeEnv ovs nvs old new }
        post hf (hd _ hm).1 (Database.Avoids.congr (d₁ := db)
          (d₂ := { db with env := mergeEnv ovs nvs old new }) rfl henv hav) hb
      have hsig : post.sig = db.sig := by have hh := evalActions_sig hb; exact hh
      refine ⟨Database.Avoids.congr (d₁ := post)
        (d₂ := { post with env := db.env, rules := db.rules }) rfl hav.env hpost, ?_⟩
      exact evalList_avoids res vs
        (fun e _ => eval_avoids (by rw [hsig]; exact hf) hpost.env e) hr

/-- Erasing rows and evaluating a declared merge cannot introduce a fresh name. -/
theorem mergeStep_avoids {f : FnName} {db x : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f)
    (h : MergeStep db x) : x.Avoids f := by
  have hcols : ∀ row ∈ db.entries, ∀ t ∈ row.columns,
      ¬ Term.Mentions f t := fun row hr t ht =>
        Term.not_mentions_args (hav.terms row.atom (Cong.assert hr.2)) t ht
  cases h with
  | @collide post old new decl vs ho hn _ _ hd _ hv =>
      have hov := hcols old ho
      have hnv := hcols new hn
      have hterms : ((db.eraseEntry old).eraseEntry new).terms ⊆ db.terms :=
        (Database.terms_eraseEntry_subset (row := new) (fun t ht =>
          Database.mem_terms_eraseEntry_of_value ho.1 (hn.1.column_values t ht)
            (Cong.subterm (.assert hn.2) (Term.arg_subterms ht (.refl _))))).trans
          (Database.terms_eraseEntry_subset (fun t ht =>
            Cong.subterm (.assert ho.2) (Term.arg_subterms ht (.refl _))))
      have hstart : ((db.eraseEntry old).eraseEntry new).Avoids f :=
        ⟨fun t ht => hav.terms t (hterms ht), hav.env⟩
      obtain ⟨havpost, hvs⟩ := mergeValues_avoids (db := (db.eraseEntry old).eraseEntry new) hf
        (hsmd old.name decl · hd) hstart
        (fun t ht => hov t (List.mem_append_right _ ht))
        (fun t ht => hnv t (List.mem_append_right _ ht)) hv
      refine ⟨avoids_addTerm havpost.terms ?_, havpost.env⟩
      intro hm
      rcases Term.mentions_app hm with he | ⟨t, ht, hm⟩
      · rw [he, hf] at hd
        contradiction
      · exact (List.mem_append.mp ht).elim
          (fun ht => hov t (List.mem_append_left _ ht) hm) (fun ht => hvs t ht hm)

theorem mergeClosure_avoids {f : FnName} {db d : Database} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f)
    (h : MergeClosure db d) : d.Avoids f := by
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

theorem Term.isValue_update {sig sig' : Signature} {f : FnName}
    (hag : ∀ g, g ≠ f → sig g = sig' g) {t : Term}
    (ht : ¬ t.Mentions f) : t.isValue sig = t.isValue sig' := by
  have hiff : t.IsValue sig ↔ t.IsValue sig' := by
    induction t using Term.recTerm with
    | lit l => simp [Term.IsValue, Term.isValue]
    | app g args ih =>
      have hgf : g ≠ f := fun he => ht (he ▸ Term.mentions_head g args)
      rw [Term.isValue_app_iff, Term.isValue_app_iff]
      have hc : sig.IsCtor g ↔ sig'.IsCtor g := by simp [Signature.IsCtor, hag g hgf]
      exact and_congr hc (forall₂_congr (fun a ha => ih a ha (Term.not_mentions_args ht a ha)))
  cases h₁ : t.isValue sig <;> cases h₂ : t.isValue sig' <;> simp_all [Term.IsValue]

theorem Entry.valid_update_iff {sig sig' : Signature} {f : FnName} {row : Entry}
    (hag : ∀ g, g ≠ f → sig g = sig' g) (ht : ¬ row.atom.Mentions f) :
    row.Valid sig ↔ row.Valid sig' := by
  have hn : row.name ≠ f := fun he => ht (he ▸ Term.mentions_head row.name row.columns)
  have hc : ∀ t ∈ row.columns, t.IsValue sig ↔ t.IsValue sig' := by
    intro t hm
    exact congrArg (· = true) (Term.isValue_update hag (Term.not_mentions_args ht t hm)) |>.to_iff
  simp only [Entry.Valid, hag row.name hn]
  constructor <;> rintro ⟨d, hd, hm, hk, hv, hcols⟩
  · exact ⟨d, hd, hm, hk, hv, fun t ht => (hc t ht).mp (hcols t ht)⟩
  · exact ⟨d, hd, hm, hk, hv, fun t ht => (hc t ht).mpr (hcols t ht)⟩

theorem Database.entries_update_of_avoids {db : Database} {sig' : Signature} {f : FnName}
    (hag : ∀ g, g ≠ f → db.sig g = sig' g) (hav : db.Avoids f) :
    ({db with sig := sig'} : Database).entries = db.entries := by
  ext row
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨(Entry.valid_update_iff hag (hav.terms _ (Cong.assert hp))).mpr hv, hp⟩
  · rintro ⟨hv, hp⟩
    exact ⟨(Entry.valid_update_iff hag (hav.terms _ (Cong.assert hp))).mp hv, hp⟩

/-- Declaring a name a `Declared` expression cannot mention leaves its value alone. -/
theorem eval_update {sig sig' : Signature} {f : FnName} (hf : sig f = none)
    (hag : ∀ g, g ≠ f → sig g = sig' g) :
    ∀ (e : Expr), e.Declared sig → ∀ (σ : Env),
      (∀ b ∈ σ, ¬ Term.Mentions f b.2) → e.eval sig σ = e.eval sig' σ := by
  intro e
  induction e using Expr.recExpr with
  | lit l => intro _ σ _; rfl
  | var v =>
      intro _ σ hv
      cases hl : Env.lookup v σ with
      | none => simp [Expr.eval, hl]
      | some t =>
        simp only [Expr.eval, hl, Option.filter_some]
        rw [Term.isValue_update hag (hv (v,t) (Env.mem_of_lookup hl))]
  | app g args ih =>
      intro hdec σ hv
      have hargs : ∀ a ∈ args, a.Declared sig := fun a ha x hx =>
        hdec x (by rw [Expr.fns]; exact List.mem_cons_of_mem _ (Expr.fns_subset_fnsList ha hx))
      have hlist : Expr.evalList sig args σ = Expr.evalList sig' args σ :=
        evalList_update args fun a ha => ih a ha (hargs a ha) σ hv
      rw [Expr.eval, Expr.eval, hlist]
      have hgf : g ≠ f := by
        rintro rfl
        exact hdec g (by rw [Expr.fns]; exact List.mem_cons_self ..) hf
      have hiff : sig.IsCtor g ↔ sig'.IsCtor g := by
        simp only [Signature.IsCtor, hag g hgf]
      by_cases hc : sig.IsCtor g
      · rw [if_pos hc, if_pos (hiff.mp hc)]
      · rw [if_neg hc, if_neg fun h => hc (hiff.mpr h)]
  | min a b iha ihb =>
      intro hdec σ hv
      have ha : a.Declared sig := fun x hx => hdec x (by simp [hx])
      have hb : b.Declared sig := fun x hx => hdec x (by simp [hx])
      rw [Expr.eval_min, Expr.eval_min, iha ha σ hv, ihb hb σ hv]

theorem evalAtom_update {sig sig' : Signature} {f : FnName} (hf : sig f = none)
    (hag : ∀ g, g ≠ f → sig g = sig' g) (e : Expr) (hd : e.Declared sig) (σ : Env)
    (hv : ∀ b ∈ σ, ¬ Term.Mentions f b.2) :
    e.evalAtom sig σ = e.evalAtom sig' σ := by
  cases e with
  | lit _ => rfl
  | var v => exact eval_update hf hag (.var v) hd σ hv
  | min a b => exact eval_update hf hag (.min a b) hd σ hv
  | app g args =>
    have hargs : ∀ a ∈ args, a.Declared sig := fun a ha x hx =>
      hd x (by rw [Expr.fns]; exact List.mem_cons_of_mem _ (Expr.fns_subset_fnsList ha hx))
    have hl := evalList_update args (fun a ha => eval_update hf hag a (hargs a ha) σ hv)
    simp only [Expr.evalAtom, hl]
    have hgf : g ≠ f := by
      rintro rfl
      exact hd g (by rw [Expr.fns]; exact List.mem_cons_self ..) hf
    rw [hag g hgf]

theorem Expr.entry_update {sig sig' : Signature} {f : FnName} (hf : sig f = none)
    (hag : ∀ g, g ≠ f → sig g = sig' g) (e : Expr) (hd : e.Declared sig) :
    e.entry sig = e.entry sig' := by
  cases e with
  | lit _ | var _ | min _ _ => rfl
  | app g cols =>
      have hgf : g ≠ f := by
        intro heq
        subst g
        exact hd f (by simp [Expr.fns]) hf
      simp only [Expr.entry, hag g hgf]

theorem evalAction_update {f : FnName} {sig' : Signature} {db : Database} {a : Action}
    (hf : db.sig f = none) (hag : ∀ g, g ≠ f → db.sig g = sig' g) (hd : a.Declared db.sig)
    (hv : ∀ b ∈ db.env, ¬ Term.Mentions f b.2) :
    evalAction { db with sig := sig' } a
      = (evalAction db a).map fun d => { d with sig := sig' } := by
  cases a with
  | expr e =>
      have he := evalAtom_update hf hag e hd db.env hv
      cases h : e.evalAtom db.sig db.env <;>
        simp [evalAction, ← he, h, Database.addTerm]
  | union e₁ e₂ =>
      have h₁ := eval_update hf hag e₁ hd.1 db.env hv
      have h₂ := eval_update hf hag e₂ hd.2 db.env hv
      cases hc₁ : e₁.eval db.sig db.env with
      | none => simp [evalAction, ← h₁, hc₁]
      | some t₁ =>
          cases hc₂ : e₂.eval db.sig db.env with
          | none => simp [evalAction, ← h₁, ← h₂, hc₁, hc₂]
          | some t₂ =>
              simp only [evalAction, ← h₁, ← h₂, hc₁, hc₂, Option.bind_some]
              split <;> simp [Database.addEq]

theorem evalActions_update {f : FnName} {sig' : Signature} :
    ∀ (as : List Action) (db : Database), db.sig f = none →
      (∀ g, g ≠ f → db.sig g = sig' g) → Actions.Declared as db.sig →
      (∀ b ∈ db.env, ¬ Term.Mentions f b.2) →
      evalActions { db with sig := sig' } as
        = (evalActions db as).map fun d => { d with sig := sig' } := by
  intro as
  induction as with
  | nil => intro db _ _ _ _; simp [evalActions]
  | cons a as ih =>
      intro db hf hag hd hv
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_update hf hag hd.1 hv, h]
      | some d =>
          have hsig : d.sig = db.sig := evalAction_sig h
          have hstep : evalActions { db with sig := sig' } (a :: as)
              = evalActions { d with sig := sig' } as := by
            simp [evalActions, evalAction_update hf hag hd.1 hv, h]
          rw [hstep, ih d (by rw [hsig]; exact hf) (by rw [hsig]; exact hag)
            (by rw [hsig]; exact hd.2) (by rw [evalAction_env h]; exact hv)]
          simp [evalActions, h]

theorem mergeValues_update_iff {f : FnName} {sig' : Signature} {db d : Database}
    {decl : FnDecl} {old new vs : List Term} (hf : db.sig f = none)
    (hag : ∀ g, g ≠ f → db.sig g = sig' g)
    (hd : ∀ ms, decl.merge = some ms → ms.Declared db.sig)
    (ho : ∀ t ∈ old, ¬ Term.Mentions f t) (hn : ∀ t ∈ new, ¬ Term.Mentions f t) :
    MergeValues { db with sig := sig' } decl old new d vs ↔
      ∃ post, MergeValues db decl old new post vs ∧ d = { post with sig := sig' } := by
  have henv : ∀ ovs nvs, ∀ b ∈ mergeEnv ovs nvs old new, ¬ Term.Mentions f b.2 :=
    fun _ _ b hb => (mem_mergeEnv hb).elim (ho b.2) (hn b.2)
  constructor
  · intro h
    cases h with
    | unchanged hm hc => exact ⟨db, .unchanged hm hc, rfl⟩
    | @changed post vs ovs nvs body res hm hc hb hr =>
        change evalActions { { db with env := mergeEnv ovs nvs old new } with sig := sig' }
          body = some post at hb
        rw [evalActions_update body { db with env := mergeEnv ovs nvs old new }
          hf hag (hd _ hm).1 (henv ovs nvs)] at hb
        obtain ⟨post₀, hb₀, rfl⟩ := Option.map_eq_some_iff.mp hb
        have hsig : post₀.sig = db.sig := by have hh := evalActions_sig hb₀; exact hh
        refine ⟨_, MergeValues.changed hm hc hb₀ ?_, rfl⟩
        have he := evalList_update (sig := post₀.sig) (sig' := sig') res (fun e he =>
          eval_update (sig := post₀.sig) (sig' := sig') (f := f)
            (by rw [hsig]; exact hf) (by rw [hsig]; exact hag) e
            (by rw [hsig]; exact (hd _ hm).2 e he) post₀.env
              (by rw [evalActions_env hb₀]; exact henv ovs nvs))
        exact he.trans hr
  · rintro ⟨post, h, rfl⟩
    cases h with
    | unchanged hm hc => exact .unchanged hm hc
    | @changed post vs ovs nvs body res hm hc hb hr =>
        have hsig : post.sig = db.sig := by have hh := evalActions_sig hb; exact hh
        apply MergeValues.changed (d := { post with sig := sig' }) hm hc
        · change evalActions { { db with env := mergeEnv ovs nvs old new } with sig := sig' }
            body = _
          rw [evalActions_update body { db with env := mergeEnv ovs nvs old new }
            hf hag (hd _ hm).1 (henv ovs nvs), hb]
          rfl
        · have he := evalList_update (sig := post.sig) (sig' := sig') res (fun e he =>
            eval_update (sig := post.sig) (sig' := sig') (f := f)
            (by rw [hsig]; exact hf) (by rw [hsig]; exact hag) e
              (by rw [hsig]; exact (hd _ hm).2 e he) post.env
                (by rw [evalActions_env hb]; exact henv ovs nvs))
          exact he.symm.trans hr

theorem mergeStep_update_iff {f : FnName} {fd : FnDecl} {db x : Database}
    (hf : db.sig f = none) (hsmd : SigMergeDeclared db.sig) (hav : db.Avoids f) :
    MergeStep { db with sig := Function.update db.sig f (some fd) } x ↔
      ∃ y, MergeStep db y ∧ x = { y with sig := Function.update db.sig f (some fd) } := by
  let sig' := Function.update db.sig f (some fd)
  have hag : ∀ g, g ≠ f → db.sig g = sig' g :=
    fun g hg => (Function.update_of_ne hg _ _).symm
  have he := Database.entries_update_of_avoids hag hav
  have hne : ∀ row ∈ db.entries, row.name ≠ f := by
    intro row hr hname
    exact hav.terms row.atom (Cong.assert hr.2) (hname ▸ Term.mentions_head row.name row.columns)
  have hcols : ∀ row ∈ db.entries, ∀ t ∈ row.value, ¬ Term.Mentions f t := by
    intro row hr t ht
    exact Term.not_mentions_args (hav.terms row.atom (Cong.assert hr.2)) t
      (List.mem_append_right _ ht)
  constructor
  · intro h
    cases h with
    | @collide post old new decl vs ho hn hneq hname hd hk hv =>
        have ho' : old ∈ db.entries := he ▸ ho
        have hn' : new ∈ db.entries := he ▸ hn
        have hd' : db.sig old.name = some decl := (hag old.name (hne old ho')).trans hd
        obtain ⟨post₀, hv₀, rfl⟩ :=
          (mergeValues_update_iff (db := (db.eraseEntry old).eraseEntry new)
            hf hag (hsmd old.name decl · hd') (hcols old ho') (hcols new hn')).mp hv
        refine ⟨_, MergeStep.collide ho' hn' hneq hname hd'
          (CongList.of_eqs_eq (d₁ := { db with sig := sig' }) (d₂ := db) rfl hk) hv₀, ?_⟩
        exact Database.putEntry_setSig post₀ sig' _
  · rintro ⟨y, h, rfl⟩
    cases h with
    | @collide post old new decl vs ho hn hneq hname hd hk hv =>
        rw [← Database.putEntry_setSig]
        apply MergeStep.collide (db := { db with sig := sig' }) (he.symm ▸ ho)
          (he.symm ▸ hn) hneq hname ((hag old.name (hne old ho)).symm.trans hd)
          (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with sig := sig' }) rfl hk)
        exact (mergeValues_update_iff (db := (db.eraseEntry old).eraseEntry new)
          hf hag (hsmd old.name decl · hd) (hcols old ho) (hcols new hn)).mpr ⟨post, hv, rfl⟩

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

/-- Updating a signature preserves normality when its derived rows are unchanged. -/
theorem MergeNormal.setSig {db : Database} (h : MergeNormal db) (sig : Signature)
    (he : ({ db with sig := sig } : Database).entries = db.entries) :
    MergeNormal { db with sig := sig } := by
  intro a ha b hb hn hk
  exact h a (he ▸ ha) b (he ▸ hb) hn
    (CongList.of_eqs_eq (d₁ := { db with sig := sig }) (d₂ := db) rfl hk)

/-- A fresh declaration commutes with normalization. -/
theorem declStep_iff {db db' : Database} {f : FnName} {fd : FnDecl} (hf : db.sig f = none)
    (hsmd : SigMergeDeclared db.sig) (hwf : db.WF) (hdt : db.DeclaredTerms)
    (_hs : db.StoreOk) :
    CmdStep db (.decl f fd) db' ↔
      ∃ d, MergeNormalize db d ∧ db' = { d with sig := Function.update db.sig f (some fd) } := by
  have hav := avoids_of_declaredTerms hf hwf hdt
  have rows : ∀ d, MergeClosure db d →
      ({d with sig := Function.update db.sig f (some fd)} : Database).entries = d.entries := by
    intro d hd
    exact Database.entries_update_of_avoids
      (fun g hg => by rw [hd.sig]; exact (Function.update_of_ne hg _ _).symm)
      (mergeClosure_avoids hf hsmd hav hd)
  constructor
  · rintro ⟨mid, rfl, hcl, hn⟩
    obtain ⟨d, hd, rfl⟩ := (mergeClosure_setSig hf hsmd hav).mp hcl
    have hdn : MergeNormal d := by
      have hh := hn.setSig d.sig (rows d hd).symm
      exact hh
    exact ⟨d, ⟨hd, hdn⟩, rfl⟩
  · rintro ⟨d, ⟨hd, hn⟩, rfl⟩
    exact ⟨_, rfl, (mergeClosure_setSig hf hsmd hav).mpr ⟨d, hd, rfl⟩,
      hn.setSig _ (rows d hd)⟩

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
  | check _ => exact hsmd

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

Every command but a saturation is a function, so the two runs agree up to the merge phase and
`MergeClosure.eq_of_allConstructors` collapses that. `Cmd.CtorDecl` is needed because the
merge phase now follows a `.decl` as well: declaring a `:merge` function is exactly how a
run on an otherwise constructor-only state regains a choice. -/
theorem CmdStep.det {db d₁ d₂ : Database} (hsig : db.sig.AllConstructors) {c : Cmd}
    (hdecl : c.CtorDecl) (h₁ : CmdStep db c d₁) (h₂ : CmdStep db c d₂) : d₁ = d₂ := by
  obtain ⟨e₁, hr₁, hcl₁⟩ := h₁.reach
  obtain ⟨e₂, hr₂, hcl₂⟩ := h₂.reach
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
