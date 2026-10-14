import EgglogSemantics.Impl.Merge

/-! Outcomes for executable sanity checks. `none` means the interpreter did not produce
an outcome (for example, exhausted fuel); it never means that a language check failed. -/

namespace Egglog

inductive ExecutionResult where
  | ok (db : FDatabase)
  | checkFailed

def ExecutionResult.succeeded : ExecutionResult → Bool
  | .ok _ => true
  | .checkFailed => false

/-- Execute checks with an explicit failure result. The ordinary command runner retains
its existing `Option` interface; its inability to execute is outside the result type. -/
def observeWith (step : FDatabase → Cmd → Option FDatabase)
    (holds : FDatabase → Query → Bool) (db : FDatabase) : Program → Option ExecutionResult
  | [] => some (.ok db)
  | .check q :: cs =>
      if holds db q then observeWith step holds db cs else some .checkFailed
  | c :: cs => (step db c).bind fun db' => observeWith step holds db' cs

/-- The general interpreter with observable check failure, for sanity tests. -/
def observeM (P : Program) : Option ExecutionResult :=
  observeWith FDatabase.execCmdM (fun d q => !(matchQuery d q).isEmpty) FDatabase.empty P

end Egglog
