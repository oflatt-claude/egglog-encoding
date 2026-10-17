import EgglogSemantics.Spec.Divergence

namespace Egglog

@[blueprint "def:behavior"
  (statement := /--
\[
  \begin{gathered}
  \delta(D,\kw{declare}\ f:d)=D[\Sigma\gets\Sigma[f\mapsto d]]\qquad
  \delta(D,\kw{rule}\ \rho)=D[\mathcal R\gets\mathcal R\cup\{\rho\}]\\
  \delta(D,\kw{run}\ R)=\fire_R(D)\qquad
  \operatorname{holds}_D(Q)\iff\exists\sigma.\ D,\sigma\models Q
  \end{gathered}
  \]
  \[
  \ir{Command}{\delta(D,C)=D_0\\D_0\Downarrow_m D'}{\langle C,D\rangle\Downarrow D'}\quad
  \ir{Saturate}{D\Downarrow_R D'}{\langle\kw{saturate}\ R,D\rangle\Downarrow D'}\quad
  \ir{Check}{\operatorname{holds}_D(Q)}{\langle\kw{check}\ Q,D\rangle\Downarrow D}\quad
  \ir{Fail}{\neg\operatorname{holds}_D(Q)}{\langle\kw{check}\ Q,D\rangle\Downarrow\kw{error}}
  \]
  \[
  \ir{Done}{}{\langle\epsilon,D\rangle\Downarrow D}\quad
  \ir{Next}{\langle C,D\rangle\Downarrow D_1\\\langle P,D_1\rangle\Downarrow o}
    {\langle C;P,D\rangle\Downarrow o}\quad
  \ir{Abort}{\langle C,D\rangle\Downarrow\kw{error}}{\langle C;P,D\rangle\Downarrow\kw{error}}
  \qquad o\in\mathit{Database}\cup\{\kw{error}\}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive Behavior where
  | success
  | checkFailed
  | diverges

/-- Finite outcomes and infinite execution, observed without exposing the final store. -/
def Behaves (db : Database) (P : Program) : Behavior → Prop
  | .success => ∃ d, Eval db P (.ok d)
  | .checkFailed => Eval db P .checkFailed
  | .diverges => ProgramDiverges db P

end Egglog
