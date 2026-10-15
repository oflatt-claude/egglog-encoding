import EgglogSemantics.Proofs.Congruence.LiveGlobal
import EgglogSemantics.Proofs.Congruence.LiveRebuildTermination
import EgglogSemantics.Proofs.Congruence.AbstractBoundary

/-! Finite compiled global writes, including their trailing rebuilding phase. -/

namespace Egglog.Congruence.Live

open Abstract

private theorem actions_unionFree {as : List Action} (h : Actions.UnionFree as) :
    Program.UnionFree (as.map Cmd.action) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨h.1, ih h.2⟩

private theorem actions_sig {d e : Database} {as : List Action}
    (h : ProgramStep d (as.map Cmd.action) e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => obtain rfl := h.nil_inv; rfl
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := h.cons_inv
      exact (ih hr).trans hm.sig

theorem global_command_exists {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) {a : Action} (ha : Cmd.action a ∈ P)
    (hsrc : CmdStep src (.action a) post) {d : Database} (h : Runtime d)
    (hn : MergeNormal d) (hsig : d.sig = encodeSig P) (henv : d.env = [])
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) (i : Nat) :
    ∃ e, ProgramStep d ((encodeCmd i (.action a)).map Command.command) e := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hact : evalAction src a = some post := by
    obtain ⟨mid, hm, hn⟩ := hsrc
    have he : post = mid := hn.1.eq_of_allConstructors (by
      rw [evalAction_sig hm]; exact hcs.sig)
    exact he.symm ▸ hm
  have hctor := sourceConstructors_of_programStep hp hsub hpre hsig
  have hof := Action.orderingFree_exprs (Program.OrderingFree.of_mem hp.noMin ha)
  have hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2) := by
    intro x hx fk hk
    exact hsig ▸ (encodeSig_tables hp (mem_program_ctors ha (actionExprs_ctors hx hk))).2
  have heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t := by
    intro x _ t ht
    apply eval_transport x (fun f _ => hctor f) ?_ ?_ ht
    · intro v _; rw [hpre.env, henv]; rfl
    · intro v _ t ht _; simp [hpre.env, Database.empty] at ht
  have hwrite := encodeAction_sourceWrites (evalAction_wf hcs.wf hact)
    hcs.sig hof hviews h.state.uf heval hact
  obtain ⟨mid, hm⟩ := sourceWrites_program_exists h hwrite
  have hmid := h.program (by
    intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    trivial) (actions_unionFree (encodeAction_unionFree a)) hm
  have hmrules : mid.rules = d.rules := by
    ext r
    rw [hm.mem_rules_iff]
    simp
  have hmsig := (actions_sig hm).trans hsig
  obtain ⟨e, he⟩ := rebuild_exists hp hmid (hm.mergeNormal hn) hmsig
    (fun r hr hR => honly r (hmrules ▸ hr) hR)
  refine ⟨e, ?_⟩
  have hlast : ProgramStep mid [.saturate rebuildRuleset] e :=
    .cons ((cmdStep_saturate_iff).mpr he) .nil
  simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def] using hm.append hlast

end Egglog.Congruence.Live
