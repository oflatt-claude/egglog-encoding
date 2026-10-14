import EgglogSemantics.Proofs.Congruence.AbstractComplete
import EgglogSemantics.Proofs.Congruence.AbstractTermination

/-! Existence of mathematical compiled command executions at corresponding prefixes. -/

namespace Egglog.Congruence.Abstract

/-- Reflexive merge phases lift an action evaluation to a command execution. -/
private theorem programStep_of_evalActions {d e : Database} {as : List Action}
    (he : evalActions d as = some e) : ProgramStep d (as.map Cmd.action) e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj he; exact .nil
  | cons a as ih =>
      obtain ⟨mid, hm, he⟩ := Option.bind_eq_some_iff.mp he
      exact .cons (CmdStep.of_reach hm) (ih he)

/-- The declaration-and-rule prelude always has a finite mathematical execution. -/
theorem prelude_exists (P : Program) :
    ∃ d, ProgramStep Database.empty ((encodePrelude P).map Command.command) d := by
  have go : ∀ (p : Program), (∀ c ∈ p, c.DeclOrRule) → ∀ d,
      ∃ e, ProgramStep d p e := by
    intro p
    induction p with
    | nil => exact fun _ d => ⟨d, .nil⟩
    | cons c cs ih =>
        intro hall d
        have hc := hall c List.mem_cons_self
        have hs := fun c hc => hall c (List.mem_cons_of_mem _ hc)
        cases c with
        | decl f dc =>
            obtain ⟨e, he⟩ := ih hs {d with sig := Function.update d.sig f (some dc)}
            exact ⟨e, .cons (CmdStep.of_reach rfl) he⟩
        | rule r =>
            obtain ⟨e, he⟩ := ih hs {d with rules := insert r d.rules}
            exact ⟨e, .cons (CmdStep.of_reach rfl) he⟩
        | _ => contradiction
  exact go _ (prelude_setup P) Database.empty

/-- Successful source actions have compiled writes and a terminating trailing rebuild. -/
theorem Boundary.action_exists {P pre rest : Program} (hp : P.Fragment) {a : Action}
    (hP : P = pre ++ Cmd.action a :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hsrc : CmdStep src (.action a) post) :
    ∃ e, ProgramStep d ((encodeCmd pre.length (.action a)).map Command.command) e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have ha : Cmd.action a ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have hrt := prefix_runtime hp hsub htpre
  have hm := metadata_of_prefix hpre htpre
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hnext : ProgramStep Database.empty (pre ++ [.action a]) post :=
    hpre.append (.cons hsrc .nil)
  have hsub' : ∀ c ∈ pre ++ [Cmd.action a], c ∈ P := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsub c hc
    · exact List.mem_singleton.mp hc ▸ ha
  have hctor := sourceConstructors_of_programStep hp hsub hpre hm.sig
  have hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      (d.sig (viewName fk.1)).isSome = true := by
    intro x hx fk hk
    rw [hm.sig, (encodeSig_tables hp (mem_program_ctors ha (actionExprs_ctors hx hk))).2]
    rfl
  have hsenv : src.env = [] := hpre.env
  have hact : evalAction src a = some post := by
    obtain ⟨mid, hmid, hmerge⟩ := hsrc
    have hmid' : evalAction src a = some mid := hmid
    have heq : post = mid := hmerge.eq_of_allConstructors (by
      rw [evalAction_sig hmid']; exact hcs.sig)
    exact heq.symm ▸ hmid'
  have hof := Action.orderingFree_exprs (Program.OrderingFree.of_mem hp.noMin ha)
  have heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t := by
    intro x _ t ht
    exact eval_transport x (fun f _ => hctor f)
      (fun v _ => by rw [hsenv, hm.env]) ht
  have hwidth : Actions.WidthOk (encodeAction a) d.sig := by
    rw [hm.sig]
    exact encodeAction_width hp a (fun fk hk => mem_program_ctors ha hk)
  have hρ : Env.Reads d src.env d.env := by
    intro v t hv
    simp [hsenv] at hv
  obtain ⟨mid, hacts, _⟩ := encodeAction_reads hcs.sig hof (fun _ _ f _ => hctor f)
    hviews (by rw [hrt.uf]; rfl) hρ h.reads hact
  have hprog := programStep_of_evalActions hacts
  obtain ⟨hmid, hsound, _⟩ := encodeAction_program_preserves hcs.wf
    (sourceSafe_of_programStep hp hsub' hnext) hcs.sig hrt h.sound h.descend hof
    hviews heval hwidth hact hprog
  obtain ⟨e, he⟩ := rebuild_cmd_exists hmid hsound
    (evalActions_finite htpre.finite_from_empty.1 hacts)
    (Database.finite_terms hnext.finite_from_empty.1) (P := P) (by
      intro r hr hR
      exact hm.rules.rebuild_only hp hpre hsub r (evalActions_rules hacts ▸ hr) hR)
  refine ⟨e, ?_⟩
  simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def] using hprog.append (.cons he .nil)

/-- A source round needs one total target rule round and a finite trailing rebuild. -/
theorem Boundary.run_exists {P pre rest : Program} (hp : P.Fragment) {R : RulesetName}
    (hP : P = pre ++ Cmd.run R :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hsrc : CmdStep src (.run R) post) :
    ∃ e, ProgramStep d ((encodeCmd pre.length (.run R)).map Command.command) e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hrt := prefix_runtime hp hsub htpre
  have hm := metadata_of_prefix hpre htpre
  have hnext := hpre.append (.cons hsrc .nil)
  have hs : RunStep R src post := by
    obtain ⟨mid, rfl, hmerge⟩ := hsrc
    exact hmerge
  have ht : RunStep R d (RunRules R d) := .refl
  obtain ⟨hsound, _⟩ := source_round_preserves hp hP hpre hrt h.sound h.descend
    hm.sig hm.rules hs ht
  obtain ⟨e, he⟩ := rebuild_cmd_exists (hrt.runRules R) hsound
    (RunRules.finite_eqs htpre.finite_from_empty.1 htpre.finite_from_empty.2 R)
    (Database.finite_terms hnext.finite_from_empty.1)
    (hm.rules.rebuild_only hp hpre hsub)
  exact ⟨e, .cons (CmdStep.of_reach rfl) (.cons he .nil)⟩

/-- All ordinary source commands have finite compiled blocks at related prefixes. -/
theorem Boundary.nonSaturate_exists {P pre rest : Program} (hp : P.Fragment) {c : Cmd}
    (hP : P = pre ++ c :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hsrc : CmdStep src c post)
    (hn : ∀ R, c ≠ .saturate R) :
    ∃ e, ProgramStep d ((encodeCmd pre.length c).map Command.command) e := by
  cases c with
  | action a => exact h.action_exists hp hP hpre htpre hsrc
  | run R => exact h.run_exists hp hP hpre htpre hsrc
  | decl f dc => exact ⟨d, .nil⟩
  | rule r => exact ⟨_, .cons (CmdStep.of_reach rfl) .nil⟩
  | check q =>
      exact ⟨d, .cons ⟨(checkAgreement hp pre q rest src d hP hpre htpre).mp hsrc.1, rfl⟩
        .nil⟩
  | saturate R => exact (hn R rfl).elim

/-- A local existence obligation for successful source commands. Failed checks are
handled separately, without requiring a run of their unreachable suffix. -/
def CommandsTerminate (P : Program) : Prop :=
  ∀ pre rest c src post d, P = pre ++ c :: rest →
    ProgramStep Database.empty pre src →
    ProgramStep Database.empty ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d →
    CmdStep src c post →
    ∃ e, ProgramStep d ((encodeCmd pre.length c).map Command.command) e

private theorem eval_exists_from_prefix {P : Program} (hp : P.Fragment)
    (hcmd : CommandsTerminate P) :
    ∀ rest pre src d source,
      P = pre ++ rest → ProgramStep Database.empty pre src →
      ProgramStep Database.empty
        ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d →
      Eval src rest source →
      ∃ target, Eval d ((encodeCmds rest pre.length).map Command.command) target := by
  intro rest
  induction rest with
  | nil =>
      intro pre src d source _ _ _ _
      exact ⟨.ok d, .nil⟩
  | cons c cs ih =>
      intro pre src d source hP hpre htpre hs
      cases hs with
      | cons hc hs =>
          have hsc := CmdEval.ok_iff.mp hc
          obtain ⟨e, he⟩ := hcmd pre cs c src _ d hP hpre htpre hsc
          obtain ⟨target, ht⟩ := ih (pre ++ [c]) _ e source
            (by simpa only [List.append_assoc, List.singleton_append] using hP)
            (hpre.append (.cons hsc .nil)) (compiled_prefix_step htpre he) hs
          refine ⟨target, ?_⟩
          simpa only [encodeCmds, List.map_append, List.length_append, List.length_singleton]
            using Eval.append_of_ok he ht
      | fail hc =>
          cases hc with
          | checkFailed hq =>
              rename_i q
              have hqt : ¬ QueryHolds d (encodeQuery q 0).1 := by
                intro ht
                exact hq ((checkAgreement hp pre _ cs src d hP hpre htpre).mpr ht)
              exact ⟨.checkFailed, .fail (.checkFailed hqt)⟩

/-- Command existence and the established query correspondence compose to finite
evaluation existence, including immediate failure before a divergent suffix. -/
theorem termination_of_commands {P : Program} (hp : P.Fragment)
    (hc : CommandsTerminate P) {source : Result} (hs : Eval Database.empty P source) :
    ∃ target, Eval Database.empty (encode P) target := by
  obtain ⟨d, hd⟩ := prelude_exists P
  obtain ⟨target, ht⟩ := eval_exists_from_prefix hp hc P [] Database.empty d source
    (by simp) .nil (by simpa [encodeCmds] using hd) hs
  refine ⟨target, ?_⟩
  simpa only [encode, compile, List.map_append, List.length_nil] using Eval.append_of_ok hd ht

end Egglog.Congruence.Abstract
