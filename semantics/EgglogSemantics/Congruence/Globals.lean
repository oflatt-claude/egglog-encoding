import EgglogSemantics.Congruence.Rounds

/-! Source global actions, including the merge phases between compiled writes. -/

namespace Egglog.Congruence

/-- A top-level compiled write has an original constructor value or union justification. -/
inductive SourceAtom (src : Database) : Term → Prop where
  | view {f : FnName} {cs : List Term} : Term.app f cs ∈ src.terms →
      SourceAtom src (.app (viewName f) (cs ++ [.app f cs]))
  | uf {a b : Term} : Cong src a b → (b = a ∨ Term.blt b a = true) →
      SourceAtom src (.app ufName [a, b])

/-- Source columns cannot hide generated table entries, and each explicit UF edge descends. -/
theorem SourceAtom.preserves {src : Database} {d : FDatabase} {t : Term}
    (hw : src.WF) (hsafe : SourceSafe src) (h : RunState src d) (ht : SourceAtom src t) :
    RunState src (d.addAtom t) := by
  refine ⟨h.inv.addAtom t, ⟨h.noUnions.eqs, h.noUnions.sig, h.noUnions.rules⟩,
    h.shape, h.uf, ?_, ?_, ?_⟩
  · cases ht with
    | view hm => exact h.sound.addView_source hw hsafe hm
    | uf hc _ => exact h.sound.addUF_source hw hsafe hc
  · cases ht with
    | view hm =>
        apply h.history.addAtom_source hw hsafe h.shape
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hw.subtermClosed _ hm (Term.arg_subterms ht (Term.self_mem_subterms t))
        · exact List.mem_singleton.mp ht ▸ hm
    | uf hc _ =>
        apply h.history.addAtom_source hw hsafe h.shape
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hc.mem_of.1
        · exact List.mem_singleton.mp ht ▸ hc.mem_of.2
  · cases ht with
    | @view f cs hm =>
        apply h.descend.addAtom_source hw hsafe
        · intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hw.subtermClosed _ hm (Term.arg_subterms ht (Term.self_mem_subterms t))
          · exact List.mem_singleton.mp ht ▸ hm
        · intro a b he
          exact (viewName_ne_ufName (Term.app.inj he).1).elim
    | uf hc hle =>
        apply h.descend.addAtom_source hw hsafe
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hc.mem_of.1
          · exact List.mem_singleton.mp ht ▸ hc.mem_of.2
        · intro a b he
          obtain ⟨rfl, rfl⟩ := by simpa using (Term.app.inj he).2
          exact hle

/-- The values of a compiled action block depend only on its signature and environment,
so merge phases can be interleaved without changing its original write justifications. -/
def SourceWrites (src : Database) (sig : Signature) (ρ : Env) (as : List Action) : Prop :=
  ∀ a ∈ as, ∃ e t, a = .expr e ∧ e.evalAtom sig ρ = some t ∧ SourceAtom src t

mutual

/-- Every atom emitted by a global build is justified by a subterm of the source result. -/
theorem encodeBuild_sourceWrites {src : Database} (hw : src.WF) {sig : Signature} {ρ : Env} :
    ∀ (e : Expr) {t : Term}, (∀ f ∈ e.fns, Prim.ofName f = none) →
      (∀ fk ∈ e.ctors, (sig (viewName fk.1)).isSome = true) →
      e.eval sig ρ = some t → t ∈ src.terms → SourceWrites src sig ρ (encodeBuild e)
  | .lit _, _, _, _, _, _ => by intro a ha; cases ha
  | .var _, _, _, _, _, _ => by intro a ha; cases ha
  | .app f args, _, hp, hd, he, ht => by
      have hpf := hp f (by simp [Expr.fns])
      have hctor : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hpf hn] at he
        contradiction
      rw [Expr.eval_app_ctor hpf hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      have hl := encodeBuildArgs_sourceWrites hw args
        (fun g hg => hp g (by simp [Expr.fns, hg]))
        (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) hts
        (fun t ht' => hw.subtermClosed _ ht (Term.arg_subterms ht' (Term.self_mem_subterms t)))
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hl a ha
      · obtain rfl := List.mem_singleton.mp ha
        refine ⟨_, .app (viewName f) (ts ++ [.app f ts]), rfl, ?_, .view ht⟩
        have hval : (Expr.app f args).eval sig ρ = some (.app f ts) := by
          rw [Expr.eval_app_ctor hpf hctor, hts]; rfl
        have hcols : Expr.evalList sig (args ++ [.app f args]) ρ =
            some (ts ++ [.app f ts]) := Expr.evalList_append_eq hts (by
          simp only [Expr.evalList, hval, Option.bind_some, Option.map_some])
        simp only [Expr.evalAtom, prim_viewName, hd (f, args.length) List.mem_cons_self,
          if_true, hcols, Option.map_some]

@[inherit_doc encodeBuild_sourceWrites]
theorem encodeBuildArgs_sourceWrites {src : Database} (hw : src.WF)
    {sig : Signature} {ρ : Env} :
    ∀ (es : List Expr) {ts : List Term}, (∀ f ∈ Expr.fnsList es, Prim.ofName f = none) →
      (∀ fk ∈ Expr.ctorsList es, (sig (viewName fk.1)).isSome = true) →
      Expr.evalList sig es ρ = some ts → (∀ t ∈ ts, t ∈ src.terms) →
      SourceWrites src sig ρ (encodeBuildArgs es)
  | [], _, _, _, _, _ => by intro a ha; cases ha
  | e :: es, _, hp, hd, he, ht => by
      obtain ⟨t, ht', he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      have hfirst := encodeBuild_sourceWrites hw e
        (fun f hf => hp f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) ht' (ht t List.mem_cons_self)
      have hrest := encodeBuildArgs_sourceWrites hw es
        (fun f hf => hp f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) hts
        (fun t ht' => ht t (List.mem_cons_of_mem _ ht'))
      intro a ha
      exact (List.mem_append.mp ha).elim (hfirst a) (hrest a)

end

theorem SourceWrites.append {src : Database} {sig : Signature} {ρ : Env} {as bs : List Action}
    (ha : SourceWrites src sig ρ as) (hb : SourceWrites src sig ρ bs) :
    SourceWrites src sig ρ (as ++ bs) := fun a h => (List.mem_append.mp h).elim (ha a) (hb a)

/-- The oriented UF write and all operand builds come from the asserted source union. -/
theorem encodeUnion_sourceWrites {src : Database} (hw : src.WF) {sig : Signature} {ρ : Env}
    {a b : Expr} {ta tb : Term}
    (hp : ∀ e ∈ [a, b], ∀ f ∈ e.fns, Prim.ofName f = none)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, (sig (viewName fk.1)).isSome = true)
    (huf : (sig ufName).isSome = true)
    (ha : a.eval sig ρ = some ta) (hb : b.eval sig ρ = some tb) (hc : Cong src ta tb) :
    SourceWrites src sig ρ (encodeAction (.union a b)) := by
  apply SourceWrites.append
    ((encodeBuild_sourceWrites hw a (hp a (by simp)) (hd a (by simp)) ha hc.mem_of.1).append
      (encodeBuild_sourceWrites hw b (hp b (by simp)) (hd b (by simp)) hb hc.mem_of.2))
  intro act hact
  obtain rfl := List.mem_singleton.mp hact
  have hvals := eval_order_ids ha hb
  refine ⟨_, .app ufName [upperId ta tb, lowerId ta tb], rfl, ?_, .uf ?_ (lowerId_le_upperId ..)⟩
  · simp only [Expr.evalAtom, show Prim.ofName ufName = none from rfl, huf, if_true,
      Expr.evalList, hvals.1, hvals.2, Option.bind_some, Option.map_some]
  · rcases ids_paired ta tb with ⟨hu, hl⟩ | ⟨hu, hl⟩
    · simpa only [hu, hl] using hc
    · simpa only [hu, hl] using hc.symm

/-- An original action's successful result justifies every atom of its compiled block. -/
theorem encodeAction_sourceWrites {src post : Database} {sig : Signature} {ρ : Env}
    (hw : post.WF) (hcs : src.sig.AllConstructors) {a : Action}
    (hp : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, Prim.ofName f = none)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (sig (viewName fk.1)).isSome = true)
    (huf : (sig ufName).isSome = true)
    (heval : ∀ e ∈ actionExprs a, ∀ t, e.eval src.sig src.env = some t → e.eval sig ρ = some t)
    (run : evalAction src a = some post) : SourceWrites post sig ρ (encodeAction a) := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    exact encodeBuild_sourceWrites hw e (hp e (by simp [actionExprs]))
      (hd e (by simp [actionExprs])) (heval e (by simp [actionExprs]) _ he)
      (Database.mem_addTerm t src)
  · exact encodeUnion_sourceWrites hw hp hd huf
      (heval a (by simp [actionExprs]) _ ha)
      (heval b (by simp [actionExprs]) _ hb) (Cong.assert (Set.mem_insert _ _))

/-- Interleaving the runtime's merge phases between global writes preserves all data invariants. -/
theorem SourceWrites.execProgram {src : Database} (hw : src.WF) (hsafe : SourceSafe src)
    {as : List Action} {d e : FDatabase} (hs : SourceWrites src d.sig d.env as)
    (h : RunState src d) (run : d.execProgramM (as.map Cmd.action) = some e) : RunState src e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj run; exact h
  | cons a as ih =>
      obtain ⟨m, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨n, ha, hm⟩ := Option.bind_eq_some_iff.mp hfirst
      obtain ⟨ea, t, rfl, hev, ht⟩ := hs a List.mem_cons_self
      have ha' : execAction d (.expr ea) = some (d.addAtom t) := by simp [execAction, hev]
      obtain rfl : n = d.addAtom t := Option.some.inj (ha.symm.trans ha')
      have hmstate := (ht.preserves hw hsafe h).merge hm
      apply ih _ hmstate hrest
      intro a ha
      have hsig : m.sig = d.sig := (Egglog.FDatabase.mergeSaturateF_fields hm).1
      have henv : m.env = d.env := (Egglog.FDatabase.mergeSaturateF_fields hm).2.1
      rw [hsig, henv]
      exact hs a (List.mem_cons_of_mem _ ha)


mutual

theorem encodeBuild_isAtomWrite : ∀ (e : Expr), ∀ a ∈ encodeBuild e, a.IsAtomWrite
  | .lit _ | .var _ => by simp [encodeBuild]
  | .app f args => by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact encodeBuildArgs_isAtomWrite args a ha
      · obtain rfl := List.mem_singleton.mp ha
        exact prim_viewName f

theorem encodeBuildArgs_isAtomWrite : ∀ (es : List Expr), ∀ a ∈ encodeBuildArgs es, a.IsAtomWrite
  | [] => by simp [encodeBuildArgs]
  | e :: es => by
      intro a ha
      exact (List.mem_append.mp ha).elim (encodeBuild_isAtomWrite e a)
        (encodeBuildArgs_isAtomWrite es a)

end

theorem encodeAction_isAtomWrite (act : Action) : ∀ a ∈ encodeAction act, a.IsAtomWrite := by
  cases act with
  | expr e => exact encodeBuild_isAtomWrite e
  | union e f =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact (List.mem_append.mp ha).elim (encodeBuild_isAtomWrite e a)
          (encodeBuild_isAtomWrite f a)
      · obtain rfl := List.mem_singleton.mp ha
        rfl

/-- Global commands preserve source facts and target invariants with a merge after each write. -/
theorem global_action_simulation {src post : Database} {d D : FDatabase} {a : Action}
    (hw : post.WF) (hsafe : SourceSafe post) (hcs : src.sig.AllConstructors)
    (h : RunState src d) (hreads : SourceReads d.toDatabase src)
    (hρ : Env.Reads d.toDatabase src.env d.env)
    (hp : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, Prim.ofName f = none)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (heval : ∀ e ∈ actionExprs a, ∀ t,
      e.eval src.sig src.env = some t → e.eval d.sig d.env = some t)
    (hs : evalAction src a = some post)
    (run : d.execProgramM ((encodeAction a).map Cmd.action) = some D) :
    RunState post D ∧ SourceReads D.toDatabase post := by
  have huf : (d.sig ufName).isSome = true := by simp [h.uf]
  have hwrites := encodeAction_sourceWrites hw hcs hp hd huf heval hs
  have hD := hwrites.execProgram hw hsafe (h.mono_src (evalAction_contained hs)) run
  obtain ⟨m, hm, hr⟩ := encodeAction_reads hcs hp hc hd huf hρ hreads hs
  obtain ⟨m', hm', hmem⟩ := exists_execActions_of_execProgramM (encodeAction_isAtomWrite a) run
  have heq : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  have hn := execActions_noUnions (encodeAction_unionFree a) h.noUnions hm
  have hcont : m.toDatabase.Contained D.toDatabase :=
    Egglog.FDatabase.toDatabase_contained_of_lists hmem (by simp [hn.eqs])
  exact ⟨hD, hr.mono hcont⟩




/-- The source fragment supplies global-write premises at an original program prefix. -/
theorem global_action_simulation_of_programStep {P pre : Program}
    (hdom : P.EncodeDomain) (hsub : ∀ c ∈ pre, c ∈ P)
    {src post : Database} (hpre : ProgramStep Database.empty pre src)
    {a : Action} (ha : Cmd.action a ∈ P) (hs : CmdStep src (.action a) post)
    {d D : FDatabase} (h : RunState src d) (htables : RebuildTables P d)
    (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (hreads : SourceReads d.toDatabase src)
    (run : d.execProgramM ((encodeAction a).map Cmd.action) = some D) :
    RunState post D ∧ SourceReads D.toDatabase post := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))
  have hnext : ProgramStep Database.empty (pre ++ [.action a]) post :=
    hpre.append (.cons hs .nil)
  have hsub' : ∀ c ∈ pre ++ [Cmd.action a], c ∈ P := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsub c hc
    · exact List.mem_singleton.mp hc ▸ ha
  have hctor := sourceConstructors_of_programStep hdom hsub hpre hsig
  have hhead : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, fk ∈ P.ctors := by
    intro e he fk hk
    apply mem_program_ctors ha
    exact actionExprs_ctors he hk
  have hsenv : src.env = [] := hpre.env
  have hact : evalAction src a = some post := by
    obtain ⟨m, hm, hmerge⟩ := hs
    have hm' : evalAction src a = some m := hm
    have heq : post = m := hmerge.eq_of_allConstructors (by
      rw [evalAction_sig hm']; exact hcs.sig)
    exact heq.symm ▸ hm'
  apply global_action_simulation (hnext.wf Database.WF.empty)
    (sourceSafe_of_programStep hdom hsub' hnext) hcs.sig h hreads ?_ ?_ ?_ ?_ ?_ hact run
  · intro v t hv
    simp [hsenv] at hv
  · intro e he
    exact noPrim_fns fun fk hk => hdom.noPrim fk (hhead e he fk hk)
  · intro e he f hf
    exact hctor f
  · intro e he fk hk
    simp [htables.view fk.1 fk.2 (hhead e he fk hk)]
  · intro e he t ht
    exact eval_transport e (fun f _ => hctor f)
      (fun v _ => by rw [hsenv, henv]) ht


/-- A compiled global action and its rebuild preserve source readings and establish closure. -/
theorem global_cmd_simulation {P pre : Program}
    (hdom : P.EncodeDomain) (hsub : ∀ c ∈ pre, c ∈ P)
    {src post : Database} (hpre : ProgramStep Database.empty pre src)
    {a : Action} (ha : Cmd.action a ∈ P) (hs : CmdStep src (.action a) post)
    {d D : FDatabase} (h : RunState src d) (htables : RebuildTables P d)
    (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (hstore : RulesEncoded P src d) (hreads : SourceReads d.toDatabase src) {i : Nat}
    (run : d.execProgramM ((encodeCmd i (.action a)).map Command.command) = some D) :
    Rebuilt D ∧ SoundTerms D post ∧ SourceReads D.toDatabase post := by
  have run' : d.execProgramM ((encodeAction a).map Cmd.action ++
      [Cmd.saturate rebuildRuleset]) = some D := by
    simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def] using run
  obtain ⟨m, hm, hrb⟩ := Egglog.FDatabase.execProgramM_append run'
  obtain ⟨hmstate, hmreads⟩ := global_action_simulation_of_programStep hdom hsub hpre ha hs
    h htables hsig henv hreads hm
  have hmaint : ∀ r ∈ m.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
    intro r hr hR
    apply hstore.rebuild_only hdom hpre hsub r _ hR
    rcases (Egglog.FDatabase.execProgramM_mem_rules_iff hm r).mp hr with hr | hr
    · exact hr
    · obtain ⟨act, _, heq⟩ := List.mem_map.mp hr
      cases heq
  have hrb' : m.runSaturateM rebuildRuleset runFuel = some D := by
    simpa only [Egglog.FDatabase.execProgramM, Egglog.FDatabase.execCmdM, Option.bind_some,
      Option.bind_fun_some] using hrb
  obtain ⟨hre, hs⟩ := hmstate.rebuilt hmaint hrb'
  exact ⟨hre, hs, hmreads.mono (Egglog.FDatabase.runSaturateM_toDatabase_contained hrb')⟩

end Egglog.Congruence
