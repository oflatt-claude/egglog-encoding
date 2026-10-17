import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`: an **inductive predicate** over the
asserted equalities, not a set of pairs the state carries.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. A **partial equivalence
relation**: symmetric and transitive, but reflexive only where an equation makes it so. -/
@[blueprint "def:congruence"
  (statement := /--
\[
  \ir{Direct}{(s,t)\in E}{s\sim_E t}\quad
  \ir{Sym}{s\sim_E t}{t\sim_E s}\quad
  \ir{Trans}{s\sim_E t\\t\sim_E u}{s\sim_E u}\quad
  \ir{Subterm}{t\sim_E t\\s\unlhd t}{s\sim_E s}
  \quad
  \ir{Cong}{f(\bar s)\sim_E f(\bar s)\\
    \forall j.\ s_j\sim_E t_j}{f(\bar s)\sim_E f(\bar t)}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive Cong (db : Database) : Term → Term → Prop where
  | direct {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | subterm {t s : Term} : Cong db t t → s ∈ t.subterms → Cong db s s
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Cong db (.app f as) (.app f as) →
      CongList db as bs → Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-- Terms explicitly occurring in the store, including subterms. -/
@[blueprint "def:stored-terms"
  (statement := /--
  \[ T_E\triangleq\{t\mid\exists(a,b)\in E.\ t\unlhd a\lor t\unlhd b\} \]
  -/)
  (latexEnv := "paperfragment")]
def Database.terms (db : Database) : Set Term :=
  {t | ∃ p ∈ db.eqs, t ∈ p.1.subterms ∨ t ∈ p.2.subterms}

/-- Every application the database holds is a **declared** function's entry: its head is
declared, and it carries that declaration's `entryWidth` children. -/
def Database.DeclaredTerms (db : Database) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → ∃ d, db.sig f = some d ∧ as.length = d.entryWidth

/-- Literals only occur beside themselves in asserted equations. -/
def Database.LitsIsolated (db : Database) : Prop :=
  ∀ p ∈ db.eqs, p.1.isLit ∨ p.2.isLit → p.1 = p.2

/-- Environment bindings exist, and literals have singleton equivalence classes. -/
structure Database.WF (db : Database) : Prop where
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms
  litsIsolated : db.LitsIsolated

/-- Completed states agree on semantic equality and represented existence. -/
structure Database.SameMeaning (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  env : d₁.env = d₂.env
  rules : d₁.rules = d₂.rules
  congr : ∀ a b, Cong d₁ a b ↔ Cong d₂ a b

end Egglog
