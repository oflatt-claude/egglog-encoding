import EgglogSemantics.Proofs.StepMonotone
import EgglogSemantics.Proofs.ActionMonotone
import EgglogSemantics.Proofs.Step

/-! Mathematical action blocks retain their facts when command-level merges interleave. -/

namespace Egglog

/-- A successful command execution contains every fact of the same action block evaluated
without intermediate merges. Expressions read only the signature and environment. -/
theorem evalActions_contained_programStep {d e D : Database} {as : List Action}
    (he : evalActions d as = some e) (hr : ProgramStep d (as.map Cmd.action) D) :
    e.Contained D := by
  induction as generalizing d e with
  | nil =>
      obtain rfl := Option.some.inj he
      obtain rfl := hr.nil_inv
      exact .refl _
  | cons a as ih =>
      obtain ⟨m, hm, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨M, hM, hr⟩ := hr.cons_inv
      obtain ⟨n, hn, hmerge⟩ := hM
      obtain rfl : n = m := Option.some.inj (hn.symm.trans hm)
      obtain ⟨e', he', hc, _, _⟩ := evalActions_mono (MergeClosure.contained hmerge)
        hmerge.sig.symm hmerge.envRules.1.symm he
      exact hc.trans (ih he' hr)

/-- Split a successful mathematical execution at a command-list boundary. -/
theorem ProgramStep.append_inv {p q : Program} {d e : Database}
    (hr : ProgramStep d (p ++ q) e) : ∃ mid, ProgramStep d p mid ∧ ProgramStep mid q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, hr⟩
  | cons c cs ih =>
      obtain ⟨mid, hc, hrest⟩ := hr.cons_inv
      obtain ⟨post, hp, hq⟩ := ih hrest
      exact ⟨post, .cons hc hp, hq⟩

end Egglog
