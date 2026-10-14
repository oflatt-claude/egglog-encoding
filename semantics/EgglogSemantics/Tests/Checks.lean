import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.Egg

/-! Check outcomes, shared substitutions, read-only execution, and static rejection. -/

namespace Egglog.Tests.Checks

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def decl (f : FnName) (n : Nat) : Cmd := .decl f (Congruence.ctorDecl n)
private def missing : Query := [.expr (atom "Missing")]
private def baseProgram : Program :=
  [decl "A" 0, decl "B" 0, decl "F" 1, decl "G" 1, decl "Missing" 0,
   .action (.expr (.app "F" [atom "A"])),
   .action (.expr (.app "G" [atom "B"]))]
private def joined : Query :=
  [.expr (.app "F" [.var "x"]), .expr (.app "G" [.var "x"])]

private def observation (r : Option ExecutionResult) : Option Bool :=
  r.map ExecutionResult.succeeded

private def compiledObservation (p : Program) : Option Bool :=
  observation (Relational.observe (Congruence.encode p) (Congruence.encode_unionFree p))

-- A declaration does not invent an instance. The whole conjunction needs one substitution.
#guard observation (observeM (baseProgram ++ [.check missing])) == some false
#guard observation (observeM (baseProgram ++ [.check joined])) == some false
#guard compiledObservation (baseProgram ++ [.check missing]) == some false
#guard compiledObservation (baseProgram ++ [.check joined]) == some false

private def unionPrefix : Program := baseProgram ++ [.action (.union (atom "A") (atom "B"))]
#guard observation (observeM (unionPrefix ++ [.check joined])) == some true
#guard compiledObservation (unionPrefix ++ [.check joined]) == some true
#guard observation (observeM [.check []]) == some true
#guard compiledObservation [.check []] == some true

private def nested : Query := [.eq (.app "F" [atom "A"]) (.app "F" [atom "B"])]
#guard observation (observeM (baseProgram ++ [.check nested])) == some false
#guard compiledObservation (baseProgram ++ [.check nested]) == some false
#guard observation (observeM (unionPrefix ++ [.check nested])) == some true
#guard compiledObservation (unionPrefix ++ [.check nested]) == some true

-- Check bindings do not escape. An interpreter's inability to run remains `none`.
#guard observation (observeM (baseProgram ++ [.check [.expr (.app "F" [.var "x"])],
  .action (.expr (.app "F" [.var "x"]))])) == none
#guard observation (observeM (baseProgram ++ [.check missing,
  .action (.expr (.app "Undeclared" []))])) == some false

-- Even a runner with no fuel reaches a failed check, but cannot execute a later command.
#guard observation (observeWith (fun _ _ => none) (fun _ _ => false) FDatabase.empty
  [.check missing, .saturate "R"]) == some false
#guard observation (observeWith (fun _ _ => none) (fun _ _ => true) FDatabase.empty
  [.check [], .saturate "R"]) == none

-- Well-formedness concerns syntax; absence is a valid runtime observation.
#guard (Program.WellFormed (baseProgram ++ [.check missing]))
#guard (Program.WellFormed (baseProgram ++ [.check joined]))
#guard Program.Fragment (unionPrefix ++ [.check joined])
#guard !(Program.WellFormed ([.check missing] : Program))
#guard !(Program.WellFormed ([.check missing, decl "Missing" 0] : Program))
#guard !(Program.WellFormed ([decl "F" 1, .check [.expr (.app "F" [])]] : Program))
#guard !(Program.WellFormed ([decl "A" 0, decl "A" 0] : Program))
#guard !(Program.WellFormed (baseProgram ++ [.check joined, .action (.expr (.app "F" [.var "x"]))]))
#guard !(Program.WellFormed ([.action (.union (.lit (.int 0)) (.lit (.int 1)))] : Program))

-- Query compilation and provenance instrumentation must retain checks.
private def provenancedObservation (p : Program) : Option Bool :=
  (Provenance.encode (Congruence.encode p)).bind fun p' =>
    observation (observeWith Relational.execCmd
      (fun d q => !(Relational.matchQuery d q).isEmpty) FDatabase.empty p')
#guard provenancedObservation (baseProgram ++ [.check joined]) == some false
#guard provenancedObservation (unionPrefix ++ [.check joined]) == some true

-- Parsing and rendering preserve both empty and nonempty checks.
private def checkText : String :=
  "(sort Math)\n(constructor Missing () Math)\n(check)\n(check (Missing))\n"
#guard ((Program.ofEgg checkText).toOption.map Program.render) == some checkText
#guard observation ((Program.ofEgg checkText).toOption.bind observeM) == some false

-- Semantic short-circuiting imposes no condition on the suffix or its termination.
example {db : Database} {q : Query} (h : ¬ QueryHolds db q) (suffix : Program) :
    Eval db (.check q :: suffix) .checkFailed := .fail (.checkFailed h)

-- A successful semantic check is exactly the identity on the entire state.
example {db db' : Database} {q : Query} (h : CmdStep db (.check q) db') : db' = db := h.2

end Egglog.Tests.Checks
