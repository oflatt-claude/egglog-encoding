import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Source.WellFormed

/-! Well-formed constructor programs with bounded rounds have a finite result. -/

namespace Egglog

private theorem constructors_normal {d : Database} (hc : d.sig.AllConstructors) :
    MergeNormal d := by
  intro row hr
  obtain ⟨dc, hd, hm, _⟩ := hr.1
  exact (hm (by simpa [Signature.mergeOf, hd] using hc row.name)).elim

private theorem cmd_exists {d : Database} (hc : d.sig.AllConstructors) (_henv : d.env = [])
    {c : Cmd} (hw : c.WellFormed d.sig) (hn : c.NoSaturate) (hdecl : c.CtorDecl) :
    ∃ r, CmdEval d c r := by
  classical
  cases c with
  | run R => exact ⟨_, .ok (.of_reach rfl (constructors_normal hc))⟩
  | rule r => exact ⟨_, .ok (.of_reach rfl (constructors_normal hc))⟩
  | decl f dc =>
      exact ⟨_, .ok (.of_reach rfl (constructors_normal (hc.sigBind hdecl)))⟩
  | saturate R => exact hn.elim
  | check q =>
      by_cases hq : QueryHolds d q
      · exact ⟨.ok d, .ok ⟨hq, rfl⟩⟩
      · exact ⟨.checkFailed, .checkFailed hq⟩

theorem Program.WellFormedFrom.eval_exists {P : Program} {d : Database}
    (hw : P.WellFormedFrom d.sig) (hn : P.NoSaturate) (hctors : P.CtorDecls)
    (hc : d.sig.AllConstructors) (henv : d.env = []) : ∃ r, Eval d P r := by
  induction P generalizing d with
  | nil => exact ⟨.ok d, .nil⟩
  | cons c cs ih =>
      have hd := hctors c List.mem_cons_self
      obtain ⟨r, hr⟩ := cmd_exists hc henv hw.1 (hn c List.mem_cons_self) hd
      cases hr with
      | ok hs =>
          obtain ⟨r, hr⟩ := ih (by rw [hs.sig]; exact hw.2)
            (fun c' hm => hn c' (List.mem_cons_of_mem _ hm))
            (fun c' hm => hctors c' (List.mem_cons_of_mem _ hm))
            (by rw [hs.sig]; exact hc.sigBind hd) (hs.env.trans henv)
          exact ⟨r, .cons (.ok hs) hr⟩
      | checkFailed hq => exact ⟨.checkFailed, .fail (.checkFailed hq)⟩

/-- Source termination follows from syntax; no finite-execution premise is needed. -/
theorem Program.WellFormed.eval_exists {P : Program} (hw : P.WellFormed)
    (hn : P.NoSaturate) (hc : P.CtorDecls) : ∃ r, Eval Database.empty P r :=
  Program.WellFormedFrom.eval_exists hw hn hc Database.CtorState.empty.sig rfl

end Egglog
