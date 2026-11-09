import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Provenance.Log
import EgglogSemantics.Proofs.Provenance.Main
import EgglogSemantics.Proofs.Provenance.Compiled
import EgglogSemantics.Source.WellFormed
import Architect

/-! The paper's provenance-pass correctness theorem. Both evaluations use mathematical
`Database` states. The proof is a simulation between the original and the instrumented
schedules up to the meaning of the original state (`Proofs/Provenance/`): the
instrumented state is the original state plus log rows, which no query reads; the
executable provenance gate in `DiffTest.lean` checks the state clause on the corpus. -/

namespace Egglog.Provenance

/-- The paper's statement: the outcomes agree, so does divergence, and erasing the log from
the instrumented program's final state gives the original's final state up to meaning. -/
def Correctness : Prop :=
  ∀ P P' : Program, Instrumentable P → encode P = some P' →
    (∀ o : Result, Eval Database.empty P' o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty P'.schedule ↔ Diverges Database.empty P.schedule) ∧
    (∀ d e, Reach Database.empty P'.schedule d → Reach Database.empty P.schedule e →
      d.eraseLog.SameMeaning e)

/-- The paper's theorem, proved: a simulation between the original and the instrumented
schedules up to the meaning of the original state. An instrumented state is the original
state plus log rows; no query or check names a log row and every query variable is an
argument of an application pattern, so the rules fire under the same substitutions, write
the same data rows and subsume the same rows. An instrumented saturation may run passes
after the original has settled, since a log row changes the meaning of the state, but they
write only log rows from a finite set, so they terminate. -/
@[blueprint "thm:provenance"
  (title := /-- Provenance pass correctness -/)
  (statement := /-- Let $P'$ be a union-free program whose names avoid the
  $\mathtt{fire}$ prefix and in which every variable of a rule query or of the check is
  an argument of an application pattern, and let $P''=\operatorname{instrument}(P')$ be its
  instrumentation. Then for each outcome $o\in\{\kw{ok},\kw{error}\}$,
  \[
    \langle P'',\emptyset\rangle\Downarrow o\iff\langle P',\emptyset\rangle\Downarrow o,
  \]
  $P''$ has a nonterminating execution if and only if $P'$ has one, and if
  $\langle P'',\emptyset\rangle\Downarrow G''$ and $\langle P',\emptyset\rangle\Downarrow G'$
  then erasing the $\mathtt{fire}_i$ rows from $G''$ gives an e-graph equivalent to $G'$. -/)
  (proof := /-- By a simulation between the original and the instrumented schedules up to
  the meaning of the original state. An instrumented state is the original state plus log
  rows; no query or check names a log row and every query variable is an argument of an
  application pattern, so the rules fire under the same substitutions, write the same data
  rows and subsume the same rows. An instrumented saturation may run passes after the
  original has settled, since a log row changes the meaning of the state, but they write
  only log rows from a finite set, so they terminate. -/)
  (latexEnv := "theorem")]
theorem correctness : Correctness := fun _ _ hI h => encode_correct hI h

/-- The congruence compiler's output satisfies the premise (`encode_instrumentable`), so the
pass is correct for it: the instrumented compilation of a well-formed source program in the
fragment has the compilation's outcomes, divergence, and final state under the log. -/
theorem correctness_compiled (P : Program) (hW : P.WellFormed) (hP : P.Fragment)
    {P'' : Program} (h : encode (Congruence.encode P) = some P'') :
    (∀ o : Result, Eval Database.empty P'' o ↔ Eval Database.empty (Congruence.encode P) o) ∧
    (Diverges Database.empty P''.schedule ↔
      Diverges Database.empty (Congruence.encode P).schedule) ∧
    (∀ d e, Reach Database.empty P''.schedule d →
      Reach Database.empty (Congruence.encode P).schedule e → d.eraseLog.SameMeaning e) :=
  correctness _ _ (encode_instrumentable P hW hP) h

end Egglog.Provenance
