import EgglogSemantics.Spec.Scope
import EgglogSemantics.Proofs.Step

namespace Egglog
/-- The scope describes the environment's domain exactly. This is the induction invariant
`Eval.exists_of_scoped` carries across a run. -/
def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

theorem Scope.Models.empty : Scope.Models [] ([] : Env) := by simp [Models]

/-! ### Scoped, evaluable expressions evaluate -/
theorem Expr.eval_isSome_of_scoped {sig : Signature} {e : Expr} {Γ : Scope} {σ : Env}
    (hm : Γ.Models σ) (h : e.Scoped Γ) (he : e.Evaluable sig) :
    ∃ t, e.eval sig σ = some t :=
  e.eval_isSome (fun v hv => (hm v).mp (h v hv)) he

theorem Expr.evalAtom_isSome_of_scoped {sig : Signature} {e : Expr} {Γ : Scope} {σ : Env}
    (hm : Γ.Models σ) (h : e.Scoped Γ) (he : e.AtomEvaluable sig) :
    ∃ t, e.evalAtom sig σ = some t := by
  cases e with
  | lit l => exact ⟨.lit l, rfl⟩
  | var v => exact Expr.eval_isSome_of_scoped hm h he
  | min a b => exact Expr.eval_isSome_of_scoped hm h he
  | app f cols =>
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome cols (fun v hv => (hm v).mp (h v hv)) he.2
    exact ⟨.app f ts, by simp [Expr.evalAtom, he.1, hts]⟩

/-- An `Evaluable` application builds, so its value is not a literal. This is what
`Action.Evaluable` asks of a `union` operand, and what `evalAction`'s check then needs. -/
theorem Expr.not_isLit_of_isApp {sig : Signature} {e : Expr} {σ : Env} {t : Term}
    (ha : e.IsApp) (he : e.Evaluable sig) (h : e.eval sig σ = some t) : ¬ t.isLit := by
  match e with
  | .app f args =>
    have hc := he f (by simp [Expr.fns])
    rw [Expr.eval_app_ctor hc] at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Term.isLit]

/-! ### Actions do not get stuck -/
theorem evalAction_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {a : Action} (h : a.Scoped Γ) (he : a.Evaluable db.sig) :
    ∃ db', evalAction db a = some db' ∧ Γ.Models db'.env := by
  cases a with
  | expr e =>
    obtain ⟨t, ht⟩ := Expr.evalAtom_isSome_of_scoped hm h.2 he
    cases hentry : e.entry db.sig with
    | none =>
        rw [Expr.evalAtom_eq_eval_of_entry_none hentry] at ht
        exact ⟨db.addTerm t, evalAction_expr_of_eval ht, hm⟩
    | some row =>
        obtain ⟨f, keys, vals⟩ := row
        obtain ⟨decl, _, _, rfl⟩ := Expr.entry_some hentry
        obtain ⟨ts, hcols, _⟩ := Expr.evalAtom_app_inv ht
        rw [Expr.evalList_append_map, Option.bind_eq_some_iff] at hcols
        obtain ⟨ks, hk, hrest⟩ := hcols
        obtain ⟨vs, hv, _⟩ := Option.map_eq_some_iff.mp hrest
        exact ⟨db.putEntry ⟨f, ks, vs⟩,
          by simp [evalAction, hentry, hk, hv], by simpa only [Database.putEntry_env] using hm⟩
  | union e₁ e₂ =>
    obtain ⟨t₁, ht₁⟩ := Expr.eval_isSome_of_scoped hm h.1 he.1.2
    obtain ⟨t₂, ht₂⟩ := Expr.eval_isSome_of_scoped hm h.2 he.2.2
    have hl₁ := Expr.not_isLit_of_isApp he.1.1 he.1.2 ht₁
    have hl₂ := Expr.not_isLit_of_isApp he.2.1 he.2.2 ht₂
    exact ⟨db.addEq t₁ t₂, by simp [evalAction, ht₁, ht₂, hl₁, hl₂], hm⟩

theorem evalActions_isSome_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {as : List Action} (h : Actions.Scoped as Γ) (he : Actions.Evaluable as db.sig) :
    ∃ db', evalActions db as = some db' ∧ Γ.Models db'.env := by
  induction as generalizing db Γ with
  | nil => exact ⟨db, rfl, hm⟩
  | cons a as ih =>
    obtain ⟨db₁, h₁, hm₁⟩ := evalAction_isSome_of_scoped hm h.1 he.1
    obtain ⟨db₂, h₂, hm₂⟩ := ih hm₁ h.2 (by rw [evalAction_sig h₁]; exact he.2)
    exact ⟨db₂, by simp [h₁, h₂], hm₂⟩

/-! ### A scoped, evaluable rule contributes on every match

`RunRules` unions the results of the firings whose actions succeed, so a rule whose
actions get stuck silently contributes nothing. This says that never happens for a
scoped, evaluable rule: the query binds exactly the pattern variables the actions were
checked against. -/
/-- A query substitution together with the globals models exactly the scope the
query binds. -/
theorem Query.bind_models {db : Database} {Γ : Scope} (hm : Γ.Models db.env) {q : Query}
    {σ : Env} (hσ : ValidQuerySubst db q σ) : (Query.bind q Γ).Models (σ ++ db.env) := by
  intro v
  rw [Query.bind, List.mem_union_iff, Env.dom_append, List.mem_append, hm v,
    hσ.mem_dom_iff, Query.mem_vars]
  constructor
  · rintro (hv | ⟨p, hp, hv⟩)
    · exact Or.inr hv
    · exact Or.inl ⟨p, hp, p.mem_freeVars.mpr ⟨hv, by simp⟩⟩
  · rintro (⟨p, hp, hv⟩ | hv)
    · exact Or.inr ⟨p, hp, (p.mem_freeVars.mp hv).1⟩
    · exact Or.inl hv

theorem evalLocalActions_isSome_of_scoped {db : Database} {Γ : Scope}
    (hm : Γ.Models db.env) {r : Rule} (hr : r.Scoped Γ) (hre : r.Evaluable db.sig)
    {σ : Env} (hσ : ValidQuerySubst db r.query σ) :
    ∃ d, evalLocalActions db r.actions σ = some d := by
  obtain ⟨d, hd, _⟩ := evalActions_isSome_of_scoped
    (db := { db with env := σ ++ db.env }) (Query.bind_models hm hσ) hr.2 hre
  exact ⟨{ d with env := db.env, rules := db.rules }, by simp [evalLocalActions, hd]⟩

/-! ### Scoped, evaluable programs whose normalization terminates

Finite runs may stop at a failed check. The result theorem therefore establishes a
finite evaluation. Scope guarantees that evaluation produces writes; terminating their
merge bodies is a separate obligation, including for programs with bounded rounds. -/

/-- Every raw result of this command can finish resolving its entry collisions. -/
def Cmd.NormalizeTotal (c : Cmd) (db : Database) : Prop :=
  ∀ mid, cmdReach db c mid → ∃ post, MergeNormalize mid post

/-- Normalization terminates after every command at its actual reachable prefix state.
This does not assume successful checks or that a saturation command terminates. -/
def Program.NormalizeTotal (p : Program) (db : Database) : Prop :=
  ∀ pre c rest d, p = pre ++ c :: rest → ProgramStep db pre d → c.NormalizeTotal d

theorem CmdEval.exists_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {c : Cmd} (hns : c.NoSaturate) (h : c.Scoped Γ) (he : c.Evaluable db.sig)
    (hnorm : c.NormalizeTotal db) :
    ∃ r, CmdEval db c r := by
  classical
  cases c with
  | action a =>
    obtain ⟨db', hv, _⟩ := evalAction_isSome_of_scoped hm h he
    obtain ⟨post, hp⟩ := hnorm db' hv
    exact ⟨.ok post, .ok ⟨db', hv, hp⟩⟩
  | rule r =>
      obtain ⟨post, hp⟩ := hnorm _ rfl
      exact ⟨_, .ok ⟨_, rfl, hp⟩⟩
  | run R =>
      obtain ⟨post, hp⟩ := hnorm _ rfl
      exact ⟨_, .ok ⟨_, rfl, hp⟩⟩
  | saturate R => exact (hns : False).elim
  | decl f d =>
      obtain ⟨post, hp⟩ := hnorm _ rfl
      exact ⟨_, .ok ⟨_, rfl, hp⟩⟩
  | check q =>
    by_cases hq : QueryHolds db q
    · exact ⟨.ok db, .ok ⟨hq, rfl⟩⟩
    · exact ⟨.checkFailed, .checkFailed hq⟩

/-- Scoped, evaluable programs with bounded rounds and terminating normalization have
a finite result. A false check is a terminating result. -/
theorem Eval.exists_of_scoped {db : Database} {Γ : Scope} (hm : Γ.Models db.env)
    {p : Program} (hns : p.NoSaturate) (h : Program.Scoped p Γ)
    (he : Program.Evaluable p db.sig) (hnorm : p.NormalizeTotal db) : ∃ r, Eval db p r := by
  induction p generalizing db with
  | nil => exact ⟨.ok db, .nil⟩
  | cons c cs ih =>
    obtain ⟨r, hc⟩ := CmdEval.exists_of_scoped hm (hns c List.mem_cons_self) h.1 he.1
      (hnorm [] c cs db rfl .nil)
    cases hc with
    | ok hs =>
        obtain ⟨r, hr⟩ := ih (by rw [hs.env]; exact hm)
          (fun c' hc' => hns c' (List.mem_cons_of_mem c hc')) h.2
          (by rw [hs.sig]; exact he.2)
          (by
            intro pre next rest d hp hpre
            exact hnorm (c :: pre) next rest d (by simp [hp]) (.cons hs hpre))
        exact ⟨r, .cons (.ok hs) hr⟩
    | checkFailed hq => exact ⟨.checkFailed, .fail (.checkFailed hq)⟩

end Egglog
