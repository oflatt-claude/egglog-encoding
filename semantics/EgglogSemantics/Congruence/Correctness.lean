import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Proofs.Congruence.Main
import Architect

/-! The paper's compiler-correctness theorem. Both evaluations use mathematical `Database`
states. No executable interpreter or fuel bound occurs in the statement. The proof for the
view-free union-find encoding is a simulation between the source and compiled schedules up
to source meaning (`Proofs/Congruence/`); the executable gates in `DiffTest.lean` check the
statement on the corpus as well. -/

namespace Egglog.Congruence

/-- Compilation preserves success, failed checks, and divergence. Neither side's
termination is a premise. -/
def PreservesBehaviors : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ behavior : Behavior,
    Behaves Database.empty (encode P) behavior ↔ Behaves Database.empty P behavior

/-- For a well-formed supported source program, every pair of finite evaluations agrees
on success versus check failure. This does not assert either evaluation exists. -/
def PreservesObservations : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source target : Result,
    Eval Database.empty P source → Eval Database.empty (encode P) target →
      source.succeeded = target.succeeded

/-- The paper's statement: the outcomes agree, and so does divergence. -/
def Correctness : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment →
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule)

/-- The paper's theorem, proved: a simulation between the source and the compiled
schedules. One source round corresponds to its compiled round followed by the rebuild
saturation, which terminates and leaves the union-find canonical, so that compiled queries
match exactly when the source queries do; a compiled saturation may run passes after the
source has settled, but they terminate because the related source states keep one meaning
and build terms of bounded size. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence pass correctness -/)
  (statement := /-- Let $P$ be a well-formed program in the source fragment, and let
  $P\leadsto P'$. Then for each outcome $o\in\{\kw{ok},\kw{error}\}$,
  \[
    \langle P',\emptyset\rangle\Downarrow o\iff\langle P,\emptyset\rangle\Downarrow o,
  \]
  and $P'$ has a nonterminating execution, a saturation that never settles, if and only
  if $P$ has one. -/)
  (proof := /-- By a simulation between the source and the compiled schedules up to the
  meaning of the source state. A source run corresponds to its compiled run followed by the
  rebuild saturation, which terminates and leaves the union-find canonical: every key has
  one live edge, to the representative of its source class, so the compiled queries match
  exactly when the source queries do. A compiled saturation may run further passes after
  the source has settled; they terminate because the related source states keep one meaning
  and build terms of bounded size. -/)
  (latexEnv := "theorem")]
theorem correctness : Correctness := fun P hW hP => encode_correct P hW hP

/-- Every source evaluation has a compiled evaluation. -/
def PreservesTermination : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source : Result,
    Eval Database.empty P source → ∃ target, Eval Database.empty (encode P) target

end Egglog.Congruence
