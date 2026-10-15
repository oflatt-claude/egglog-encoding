import EgglogSemantics.Proofs.Step

/-! Well-formedness and declared widths through mathematical execution. -/

namespace Egglog

/-- `env` and `rules` are invisible to `WF`, as they are to `Cong`. -/
theorem Database.WF.setEnvRules {db : Database} (hw : db.WF) {σ : Env} {R : Set Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ({ db with env := σ, rules := R } : Database).WF := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun b hb => ?_, hw.litsIsolated⟩
  · rw [Database.terms_setEnvRules] at ht; exact hw.eqsRefl t ht
  · rw [Database.terms_setEnvRules] at ht ⊢; exact hw.subtermClosed t ht
  · rw [Database.terms_setEnvRules]; exact hσ b hb

def Action.SetWidthOk : Action → Signature → Prop
  | _, _ => True

@[simp] def Actions.SetWidthOk : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetWidthOk sig ∧ Actions.SetWidthOk as sig

/-- The automatic structural write predicate used by the refinement interfaces. -/
def Action.WriteLegal (a : Action) (sig : Signature) : Prop :=
  a.SetWidthOk sig

@[simp] def Actions.WriteLegal (as : List Action) (sig : Signature) : Prop :=
  Actions.SetWidthOk as sig

@[simp] def Cmd.WriteLegal : Cmd → Signature → Prop
  | .action a, sig => a.WriteLegal sig
  | .rule r, sig => Actions.WriteLegal r.actions sig
  | .check _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

theorem Actions.WriteLegal.head {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : a.WriteLegal sig := h.1

theorem Actions.WriteLegal.tail {a : Action} {as : List Action} {sig : Signature}
    (h : Actions.WriteLegal (a :: as) sig) : Actions.WriteLegal as sig := h.2

/-- Every declared `:merge` obeys the discipline every other action block obeys — its body
writes at the declared column widths — and its result has one expression per value column.

No program-level check walks into a merge body, so this has to be carried separately. The
`res.length` half is **new**: it is what
`FDatabase.IndexOk.width` needs of the row a firing writes, which is `MergeStep.collide`'s
`arity` premises reaching back into the declaration. -/
def Signature.MergesLegal (sig : Signature) : Prop :=
  ∀ g dc oldVars newVars body res, sig g = some dc → dc.merge = some (MergeSpec.merge
    oldVars newVars body res) →
    Actions.WriteLegal body sig ∧ res.length = dc.outArity

/-- A merge preserves the invariants. `RowsWF` is gone as a hypothesis: an entry is a term,
so `WF.subtermClosed` already puts the colliding entries' value columns in `terms`, which
is what `WF.envInTerms` needs of `mergeEnv oldVars newVars a b` before the body runs. -/
theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d f dc as bs a b vs oldVars newVars body res
    hdc hmg _ hla hlb hra hrb hcong hbody hres =>
    have hout : ∀ (cs os : List Term), Term.app f (cs ++ os) ∈ d₁.terms →
        ∀ x ∈ os, x ∈ d₁.terms := by
      intro cs os hmem x hx
      exact hw.subtermClosed _ hmem
        (Term.mem_subterms.mpr (Term.IsSubterm.arg (List.mem_append_right _ hx)
          (Term.IsSubterm.refl x)))
    have hw0 : ({ d₁ with env := mergeEnv oldVars newVars a b } : Database).WF :=
      hw.setEnv fun p hp => by
        rcases mem_mergeEnv hp with hpa | hpb
        · exact hout as a hra _ hpa
        · exact hout bs b hrb _ hpb
    have hd : d.WF := evalActions_wf hw0 hbody
    have hr : (d.addTerm (.app f (as ++ vs))).WF := hd.addTerm _
    have hb : d₁.Contained d := ⟨(evalActions_contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addTerm (.app f (as ++ vs)) d)
    exact hr.setEnvRules fun p hp => hc.terms (hw.envInTerms p hp)

theorem MergeClosure.wf {d₁ d₂ : Database} (hw : d₁.WF) (h : MergeClosure d₁ d₂) : d₂.WF := by
  induction h with
  | refl => exact hw
  | tail _ hstep ih => exact MergeStep.wf ih hstep

/-- One command preserves `Database.WF`: `cmdReach_wf'` for what it reaches,
`MergeClosure.wf` for the merge phase. -/
theorem RunStep.wf {R : RulesetName} {db db' : Database} (hw : db.WF)
    (h : RunStep R db db') : db'.WF := MergeClosure.wf (RunRules.wf hw) h

/-- `cmdReach_wf` for every command, a saturating run included: its rounds are `RunStep.wf`,
which needs `MergeClosure.wf` and so lives here rather than in `Proofs/Step.lean`. -/
theorem cmdReach_wf' {db d : Database} (hw : db.WF) {c : Cmd} (h : cmdReach db c d) :
    d.WF := by
  cases c with
  | saturate R =>
    exact RunReach.induction (P := Database.WF) (fun _ _ hp hs => hs.wf hp)
      (show SaturateReach R db d from h).1 hw
  | _ => exact cmdReach_wf hw (by trivial) h

theorem CmdStep.wf {db db' : Database} (hw : db.WF) {c : Cmd} (h : CmdStep db c db') :
    db'.WF := by
  obtain ⟨d, hreach, hcl⟩ := h.reach
  exact MergeClosure.wf (cmdReach_wf' hw hreach) hcl

/-- A whole run preserves `Database.WF`, `CmdStep.wf` per command. It is what pays for
`Database.Recorded.trans`'s two `WF` premises where the refinement chain composes two
containments. -/
theorem ProgramStep.wf {db db' : Database} {p : Program} (h : ProgramStep db p db') :
    db.WF → db'.WF := by
  induction h with
  | nil => exact id
  | cons hcmd _ ih => exact fun hw => ih (CmdStep.wf hw hcmd)

/-! ### `DeclaredTerms` over the step relations

Every application a reachable state holds is a declared function's entry, `entryWidth`
children wide. `Proofs/Eval.lean` carries the action half; what is left is the merge phase,
the rule phase, and a declaration.

Two front-end checks pay for it: `Program.WidthOk` for the terms a command builds and
`Program.DeclsFresh` for the signature a `.decl` writes. Two conditions no signature-level
check can deliver are carried by `Database.RunLegal`. -/

/-- **`DeclaredTerms` is preserved by a merge firing**, under the two signature-level
invariants and no premise on the firing itself. `MergesWidthOk` supplies the body's
`Actions.WidthOk`, which is what running the body needs; the combined entry is
`arity + outArity` wide because `res` has one expression per value column. -/
theorem mergeStep_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (_hml : db.sig.MergesLegal) (hmw : db.sig.MergesWidthOk) (h : MergeStep db db') :
    db'.DeclaredTerms := by
  cases h with
  | @collide d f decl as bs a b vs oldVars newVars body res
    hd hmerge _ hasl _ hae hbe _ hbody hres =>
  have hmemab : ∀ p ∈ mergeEnv oldVars newVars a b, p.2 ∈ db.terms := by
    intro p hp
    rcases mem_mergeEnv hp with hp' | hp'
    · exact Database.mem_terms_of_arg hwf hae (List.mem_append_right as hp')
    · exact Database.mem_terms_of_arg hwf hbe (List.mem_append_right bs hp')
  have hwf₀ : ({ db with env := mergeEnv oldVars newVars a b } : Database).WF := hwf.setEnv hmemab
  have hdt₀ : ({ db with env := mergeEnv oldVars newVars a b } : Database).DeclaredTerms := by
    intro g cs hmem; rw [Database.terms_setEnv] at hmem; exact hdt g cs hmem
  have hspec := hmw f decl _ hd hmerge
  have hdsig : d.sig = db.sig :=
    evalActions_sig (db := { db with env := mergeEnv oldVars newVars a b }) hbody
  have hdwf : d.WF := evalActions_wf hwf₀ hbody
  have hddt : d.DeclaredTerms := evalActions_declaredTerms hwf₀ hdt₀ hspec.2.1 hbody
  have hvsd : ∀ t ∈ vs, Term.DeclaredTerm db.sig t := by
    have := Expr.evalList_declaredTerm (Database.env_declaredTerm hdwf hddt)
      (sig := d.sig) (by rw [hdsig]; exact hspec.2.2) hres
    intro t ht; rw [← hdsig]; exact this t ht
  have hvsl : vs.length = decl.outArity := (Expr.evalList_length hres).trans hspec.1
  have hentry : Term.DeclaredTerm db.sig (.app f (as ++ vs)) := by
    intro g cs hsub
    rw [Term.subterms_app] at hsub
    rcases Set.mem_insert_iff.mp hsub with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
      refine ⟨decl, hd, ?_⟩
      rw [List.length_append, hasl, hvsl, FnDecl.entryWidth, if_neg]
      simp [hmerge]
    · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
      rcases List.mem_append.mp hx with hx | hx
      · exact Database.declaredTerm_of_mem hwf hdt
          (Database.mem_terms_of_arg hwf hae (List.mem_append_left a hx)) g cs hxs
      · exact hvsd x hx g cs hxs
  intro g cs hmem
  rw [Database.terms_setEnvRules, Database.addTerm_terms] at hmem
  rcases hmem with hmem | hmem
  · exact hdsig ▸ hddt g cs hmem
  · exact hdsig ▸ hentry g cs hmem

theorem mergeClosure_declaredTerms {db db' : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hml : db.sig.MergesLegal) (hmw : db.sig.MergesWidthOk) (h : MergeClosure db db') :
    db'.DeclaredTerms := by
  induction h with
  | refl => exact hdt
  | @tail x y hcl hstep ih =>
    have hsx : x.sig = db.sig := MergeClosure.sig hcl
    exact mergeStep_declaredTerms (MergeClosure.wf hwf hcl) ih
      (by rw [hsx]; exact hml) (by rw [hsx]; exact hmw) hstep

/-- The rules the state holds obey the check `evalLocalActions_declaredTerms` asks of an
action block. `RunRules` fires the rules in `db.rules`, which no signature-level check
reaches. -/
def Database.RulesOk (db : Database) : Prop :=
  ∀ r ∈ db.rules, Actions.WidthOk r.actions db.sig

theorem runRules_declaredTerms {R : RulesetName} {db : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) : (RunRules R db).DeclaredTerms := by
  intro g cs hmem
  rw [RunRules, Database.sUnion_terms] at hmem
  rcases hmem with hmem | hmem
  · exact hdt g cs hmem
  · obtain ⟨e, he, hmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨r, hrmem, -, σ, hq, hstep⟩ := he
    have hes : e.sig = db.sig := evalLocalActions_sig hstep
    change ∃ x, db.sig g = some x ∧ cs.length = x.entryWidth
    rw [← hes]
    exact evalLocalActions_declaredTerms hwf hdt hq.mem_terms (hr r hrmem) hstep g cs hmem

/-- **A declaration preserves `DeclaredTerms` exactly when it is fresh**, and needs nothing
else. A `DeclaredTerms` state holds no application of an undeclared name, so writing the
signature at a fresh name cannot invalidate a term it already holds. -/
theorem decl_declaredTerms {db : Database} (hdt : db.DeclaredTerms) {f : FnName}
    {dc : FnDecl} (hf : db.sig f = none) :
    ({ db with sig := Function.update db.sig f (some dc) } : Database).DeclaredTerms := by
  intro g cs hmem
  rw [Database.terms_setSig] at hmem
  obtain ⟨d, hd, hlen⟩ := hdt g cs hmem
  have hgf : g ≠ f := by rintro rfl; rw [hf] at hd; exact absurd hd (by simp)
  refine ⟨d, ?_, hlen⟩
  change Function.update db.sig f (some dc) g = some d
  rw [Function.update_of_ne hgf]; exact hd

/-- **A saturating run preserves `DeclaredTerms`.** Each round is `runRules_declaredTerms`
then `mergeClosure_declaredTerms`; what makes the induction go through is that a round moves
neither `sig` nor `rules`, so `Database.RulesOk` and the two signature-level checks hold
verbatim at every intermediate state. -/
theorem runReach_declaredTerms {R : RulesetName} {db d : Database} (hwf : db.WF)
    (hdt : db.DeclaredTerms) (hr : db.RulesOk) (hml : db.sig.MergesLegal)
    (hmw : db.sig.MergesWidthOk) (h : Relation.ReflTransGen (RunStep R) db d) :
    d.DeclaredTerms := by
  refine (RunReach.induction
    (P := fun x => x.WF ∧ x.DeclaredTerms ∧ x.sig = db.sig ∧ x.rules = db.rules)
    ?_ h ⟨hwf, hdt, rfl, rfl⟩).2.1
  rintro x y ⟨hxw, hxd, hxs, hxr⟩ hstep
  have hro : x.RulesOk := fun r hr' => hxs ▸ hr r (hxr ▸ hr')
  have hxml : Signature.MergesLegal (RunRules R x).sig := by
    rw [RunRules.sig (R := R) (db := x), hxs]; exact hml
  have hxmw : Signature.MergesWidthOk (RunRules R x).sig := by
    rw [RunRules.sig (R := R) (db := x), hxs]; exact hmw
  have hyr : y.rules = db.rules := by
    rw [(MergeClosure.envRules hstep).2]
    simpa only [RunRules, Database.sUnion_rules] using hxr
  exact ⟨hstep.wf hxw, mergeClosure_declaredTerms (RunRules.wf hxw)
      (runRules_declaredTerms hxw hxd hro) hxml hxmw hstep,
    by rw [hstep.sig]; exact hxs, hyr⟩

theorem cmdReach_declaredTerms {db d : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : cmdReach db c d) : d.DeclaredTerms := by
  cases c with
  | action a => exact evalAction_declaredTerms hwf hdt hw h
  | rule r =>
    subst h
    intro g cs hmem
    rw [Database.terms_setRules] at hmem
    exact hdt g cs hmem
  | run R => subst h; exact runRules_declaredTerms hwf hdt hr
  | saturate R =>
    exact runReach_declaredTerms hwf hdt hr hml hmw (show SaturateReach R db d from h).1
  | decl f dc => subst h; exact decl_declaredTerms hdt hfresh
  | check q => rw [h.2]; exact hdt

/-- The two signature-level invariants are read at the signature the command *installs*, as
`Cmd.WidthOk` and `Cmd.MergeDeclared` are: that is the signature the merge phase runs
against. -/
theorem cmdStep_declaredTerms {db d : Database} (hwf : db.WF) (hdt : db.DeclaredTerms)
    (hr : db.RulesOk) {c : Cmd} (hw : c.WidthOk db.sig)
    (hfresh : c.DeclFresh db.sig) (hml : (c.sigBind db.sig).MergesLegal)
    (hmw : (c.sigBind db.sig).MergesWidthOk) (h : CmdStep db c d) : d.DeclaredTerms := by
  obtain ⟨x, hx, hcl⟩ := h.reach
  have hxs : x.sig = c.sigBind db.sig := cmdReach_sig hx
  exact mergeClosure_declaredTerms (cmdReach_wf' hwf hx)
    (cmdReach_declaredTerms hwf hdt hr hw hfresh hml hmw hx)
    (by rw [hxs]; exact hml) (by rw [hxs]; exact hmw) hcl

/-- What `Program.WidthOk` and `Program.DeclsFresh` cannot say, checked at the state each
command actually runs in — the weakest place to check it, as `FDatabase.ProgramLegal` does.
Two things: the rules the state holds pass the action-block check, and the signature the
command leaves has width-checked `:merge` bodies.
Neither is a condition on the program text — a rule outlives the signature it was added
under, and `Cmd.WidthOk` reaches a `:merge` only at the declaration that installs it. -/
def Database.RunLegal : Database → Program → Prop
  | _, [] => True
  | db, c :: cs =>
      db.RulesOk ∧ Signature.MergesLegal (c.sigBind db.sig) ∧
        Signature.MergesWidthOk (c.sigBind db.sig) ∧
        ∀ d, CmdStep db c d → Database.RunLegal d cs

/-- **A run preserves `DeclaredTerms`.** The two front-end checks thread through the
induction on their own: each is read at the signature the earlier commands leave, which is
the signature the run has reached by `CmdStep.sig`. -/
theorem programStep_declaredTerms {db db' : Database} {p : Program}
    (h : ProgramStep db p db') :
    db.WF → db.DeclaredTerms → Program.WidthOk p db.sig →
      Program.DeclsFresh p db.sig → db.RunLegal p → db'.DeclaredTerms := by
  induction h with
  | nil => exact fun _ hdt _ _ _ => hdt
  | @cons db x d' c cs hstep _ ih =>
    intro hwf hdt hw hfresh hl
    have hxs : x.sig = c.sigBind db.sig := CmdStep.sig hstep
    exact ih (CmdStep.wf hwf hstep)
      (cmdStep_declaredTerms hwf hdt hl.1 hw.1 hfresh.1 hl.2.1 hl.2.2.1 hstep)
      (by rw [hxs]; exact hw.2) (by rw [hxs]; exact hfresh.2)
      (hl.2.2.2 x hstep)

/-- **Every state a legal run reaches from `Database.empty` is `DeclaredTerms`.** -/
theorem reachable_declaredTerms {p : Program} {db : Database}
    (hw : Program.WidthOk p Database.empty.sig)
    (hfresh : Program.DeclsFresh p Database.empty.sig)
    (hl : Database.empty.RunLegal p) (h : ProgramStep Database.empty p db) :
    db.DeclaredTerms :=
  programStep_declaredTerms h Database.WF.empty Database.empty_declaredTerms hw hfresh hl

end Egglog
