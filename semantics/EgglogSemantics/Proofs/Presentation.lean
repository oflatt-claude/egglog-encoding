import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Step

namespace Egglog

/-- Successful execution preserves the environment at every command boundary. -/
theorem Eval.env {db d : Database} {P : Program} (h : Eval db P (.ok d)) :
    d.env = db.env := (Eval.ok_iff.mp h).env

theorem Eval.empty_env {d : Database} {P : Program} (h : Eval Database.empty P (.ok d)) :
    d.env = [] := h.env

end Egglog
