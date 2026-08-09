import EgglogSemantics.Spec.Eval
import EgglogSemantics.Proofs.Congruence

namespace Egglog
namespace Expr
@[simp] theorem eval_lit {sig : Signature} {l : Lit} {σ : Env} :
    (Expr.lit l).eval sig σ = some (.lit l) := rfl

@[simp] theorem eval_var {sig : Signature} {v : Var} {σ : Env} :
    (Expr.var v).eval sig σ = Env.lookup v σ := rfl

/-- The building case, which is the only one the constructor fragment ever takes. -/
@[simp] theorem eval_app_ctor {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : sig.IsCtor f) :
    (Expr.app f args).eval sig σ = (Expr.evalList sig args σ).map (Term.app f) := by
  simp only [Expr.eval, hp, if_pos hc]

/-- The computing case. A reserved name shadows a user function, so this needs no
condition on the signature. -/
theorem eval_app_prim {sig : Signature} {f : FnName} {p : Prim} {args : List Expr}
    {σ : Env} (hp : Prim.ofName f = some p) :
    (Expr.app f args).eval sig σ = (Expr.evalList sig args σ).bind p.apply := by
  simp only [Expr.eval, hp]

/-- The reading case, which has no rule: an application of a non-constructor is a lookup,
and `Impl/Check.lean`'s `noLookup` rejects one in every position this is called from. -/
theorem eval_app_merge {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    {body : List Action} {res : List Expr} (hp : Prim.ofName f = none)
    (hc : sig.mergeOf f = some (MergeSpec.merge body res)) :
    (Expr.app f args).eval sig σ = none := by
  simp only [Expr.eval, hp, if_neg (Signature.not_isCtor hc)]

/-- `eval_app_merge` for a `:no-merge` function, which is a lookup for the same reason. -/
theorem eval_app_noMerge {sig : Signature} {f : FnName} {args : List Expr} {σ : Env}
    (hp : Prim.ofName f = none) (hc : sig.mergeOf f = some MergeSpec.noMerge) :
    (Expr.app f args).eval sig σ = none := by
  simp only [Expr.eval, hp, if_neg (Signature.not_isCtor hc)]

@[simp] theorem evalList_nil {sig : Signature} {σ : Env} :
    Expr.evalList sig [] σ = some [] := rfl

@[simp] theorem evalList_cons {sig : Signature} {e : Expr} {es : List Expr} {σ : Env} :
    Expr.evalList sig (e :: es) σ =
      (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·) := rfl

end Expr
mutual

/-- Evaluation reads the environment only through `lookup`, so environments that
agree are interchangeable. This is what lets `Env-Union`'s duplicate bindings be
ignored. -/
theorem Expr.eval_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (e : Expr) :
    e.eval sig σ₁ = e.eval sig σ₂ := by
  match e with
  | .lit _ => rfl
  | .var v => exact h v
  | .app f args => simp only [Expr.eval, Expr.evalList_agree h args]

theorem Expr.evalList_agree {sig : Signature} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂)
    (es : List Expr) : Expr.evalList sig es σ₁ = Expr.evalList sig es σ₂ := by
  match es with
  | [] => rfl
  | e :: es =>
    rw [Expr.evalList_cons, Expr.evalList_cons, Expr.eval_agree h e, Expr.evalList_agree h es]

end

mutual

/-- Evaluation gets stuck on an unbound variable, on a lookup and on a primitive; an
expression with none of the three evaluates. The two conditions are exactly
`Expr.Scoped` and `Expr.Evaluable`: the Redex's type checker, and what a sort discipline
would add (`Spec/Scope.lean`). -/
theorem Expr.eval_isSome {sig : Signature} {σ : Env} (e : Expr)
    (h : ∀ v ∈ e.vars, v ∈ Env.dom σ)
    (hf : ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f) :
    ∃ t, e.eval sig σ = some t := by
  match e with
  | .lit l => exact ⟨.lit l, rfl⟩
  | .var v =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (Env.lookup_isSome_iff_mem_dom.mpr (h v (by simp)))
    exact ⟨t, ht⟩
  | .app f args =>
    obtain ⟨hp, hc⟩ := hf f (by simp)
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (by simpa using h)
      (fun g hg => hf g (by simp [hg]))
    exact ⟨.app f ts, by rw [Expr.eval_app_ctor hp hc, hts, Option.map_some]⟩

theorem Expr.evalList_isSome {sig : Signature} {σ : Env} (es : List Expr)
    (h : ∀ v ∈ Expr.varsList es, v ∈ Env.dom σ)
    (hf : ∀ f ∈ Expr.fnsList es, Prim.ofName f = none ∧ sig.IsCtor f) :
    ∃ ts, Expr.evalList sig es σ = some ts := by
  match es with
  | [] => exact ⟨[], rfl⟩
  | e :: es =>
    obtain ⟨t, ht⟩ := Expr.eval_isSome e (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inl hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inl hg)))
    obtain ⟨ts, hts⟩ := Expr.evalList_isSome es (fun v hv =>
      h v (List.mem_union_iff.mpr (Or.inr hv)))
      (fun g hg => hf g (List.mem_union_iff.mpr (Or.inr hg)))
    exact ⟨t :: ts, by rw [Expr.evalList_cons, ht, Option.bind_some, hts, Option.map_some]⟩

end

@[simp] theorem evalActions_nil {db : Database} : evalActions db [] = some db := rfl

@[simp] theorem evalActions_cons {db : Database} {a : Action} {as : List Action} :
    evalActions db (a :: as) = (evalAction db a).bind fun db' => evalActions db' as := rfl

/-! ### Actions only add -/
/-- What an action produces, per case. Every fact below about `evalAction` is a
three-way `rcases` on this rather than a repeat of the case analysis. -/
theorem evalAction_eq_some {db db' : Database} {a : Action}
    (h : evalAction db a = some db') :
    (∃ e t, a = .expr e ∧ e.eval db.sig db.env = some t ∧ db' = db.addTerm t) ∨
      (∃ v e t, a = .letBind v e ∧ e.eval db.sig db.env = some t ∧
        db' = { db.addTerm t with env := (v, t) :: db.env }) ∨
      (∃ e₁ e₂ t₁ t₂, a = .union e₁ e₂ ∧ e₁.eval db.sig db.env = some t₁ ∧
        e₂.eval db.sig db.env = some t₂ ∧ db' = db.addEq t₁ t₂) ∨
      (∃ f args out as vs, a = .set f args out ∧ Expr.evalList db.sig args db.env = some as ∧
        Expr.evalList db.sig out db.env = some vs ∧ db' = db.addRow f as vs) := by
  cases a with
  | expr e =>
    cases hv : e.eval db.sig db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨e, t, rfl, hv, h.symm⟩
  | letBind v e =>
    cases hv : e.eval db.sig db.env with
    | none => simp [evalAction, hv] at h
    | some t =>
      simp only [evalAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨v, e, t, rfl, hv, h.symm⟩)
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval db.sig db.env with
    | none => simp [evalAction, hv₁] at h
    | some t₁ =>
      cases hv₂ : e₂.eval db.sig db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some t₂ =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inl ⟨e₁, e₂, t₁, t₂, rfl, hv₁, hv₂, h.symm⟩))
  | set f args out =>
    cases hv₁ : Expr.evalList db.sig args db.env with
    | none => simp [evalAction, hv₁] at h
    | some as =>
      cases hv₂ : Expr.evalList db.sig out db.env with
      | none => simp [evalAction, hv₁, hv₂] at h
      | some vs =>
        simp only [evalAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr ⟨f, args, out, as, vs, rfl, hv₁, hv₂, h.symm⟩))

theorem evalAction_contained {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db.Contained db' := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact .addTerm t db
  · exact ⟨Set.subset_union_left, Set.subset_union_left, subset_rfl⟩
  · exact .addEq t₁ t₂ db
  · exact .addRow f as vs db

theorem evalAction_rules {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.rules = db.rules := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩
  · rfl
  · rfl
  · rfl
  · simp

/-- No action touches the signature; only `Cmd.decl` writes it. -/
theorem evalAction_sig {db db' : Database} {a : Action}
    (h : evalAction db a = some db') : db'.sig = db.sig := by
  rcases evalAction_eq_some h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩ |
    ⟨_, _, _, _, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, rfl⟩
  · rfl
  · rfl
  · rfl
  · simp

theorem evalAction_wf {db db' : Database} (hw : db.WF) {a : Action}
    (h : evalAction db a = some db') : db'.WF := by
  rcases evalAction_eq_some h with ⟨_, t, -, -, rfl⟩ | ⟨_, _, t, -, -, rfl⟩ |
    ⟨_, _, t₁, t₂, -, -, -, rfl⟩ | ⟨f, _, _, as, vs, -, -, -, rfl⟩
  · exact hw.addTerm t
  · refine ⟨(hw.addTerm t).subtermClosed, (hw.addTerm t).eqsInTerms, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact db.mem_addTerm t
    · exact (hw.addTerm t).envInTerms b hb
  · exact hw.addEq t₁ t₂
  · exact hw.addRow f as vs

theorem evalActions_contained {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db.Contained db' := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ .refl db
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact (evalAction_contained hv).trans (ih h)

theorem evalActions_sig {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.sig = db.sig := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_sig hv]

theorem evalActions_rules {db db' : Database} {as : List Action}
    (h : evalActions db as = some db') : db'.rules = db.rules := by
  induction as generalizing db with
  | nil => simp only [evalActions_nil, Option.some.injEq] at h; simp [← h]
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      rw [ih h, evalAction_rules hv]

theorem evalActions_wf {db db' : Database} (hw : db.WF) {as : List Action}
    (h : evalActions db as = some db') : db'.WF := by
  induction as generalizing db with
  | nil => exact (Option.some.injEq .. ▸ h : db = db') ▸ hw
  | cons a as ih =>
    cases hv : evalAction db a with
    | none => simp [hv] at h
    | some db₁ =>
      simp only [evalActions_cons, hv, Option.bind_some] at h
      exact ih (evalAction_wf hw hv) h

/-! ### Agreeing environments are interchangeable

`Expr.eval_agree` says evaluation reads the environment only through `lookup`. Lifting
that to whole action sequences is what justifies two places the semantics is loose
about environments on purpose: the Redex `Env-Union` can leave a variable bound twice,
and `ValidEnv` fixes a substitution's domain only up to permutation. -/
theorem evalAction_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a : Action) :
    Option.Rel Database.EnvAgree (evalAction d₁ a) (evalAction d₂ a) := by
  cases a with
  | expr e =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e]
    cases e.eval d₁.sig d₁.env with
    | none => exact .none
    | some t =>
      exact .some ⟨h.sig, by simp [Database.addTerm, h.terms],
        by simp [Database.addTerm, h.rows], h.eqs, h.rules, h.env⟩
  | letBind v e =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e]
    cases e.eval d₁.sig d₁.env with
    | none => exact .none
    | some t =>
      refine .some ⟨h.sig, by simp [Database.addTerm, h.terms],
        by simp [Database.addTerm, h.rows], h.eqs, h.rules, fun w => ?_⟩
      by_cases hw : w = v <;> simp [hw, h.env w]
  | union e₁ e₂ =>
    simp only [evalAction, ← h.sig, ← Expr.eval_agree (sig := d₁.sig) h.env e₁,
      ← Expr.eval_agree (sig := d₁.sig) h.env e₂]
    cases e₁.eval d₁.sig d₁.env with
    | none => exact .none
    | some t₁ =>
      cases e₂.eval d₁.sig d₁.env with
      | none => exact .none
      | some t₂ =>
        exact .some ⟨h.sig, by simp [Database.addEq, Database.addTerm, h.terms],
          by simp [Database.addEq, Database.addTerm, h.rows],
          by simp [Database.addEq, h.eqs], h.rules, h.env⟩
  | set f args out =>
    simp only [evalAction, ← h.sig, ← Expr.evalList_agree (sig := d₁.sig) h.env args,
      ← Expr.evalList_agree (sig := d₁.sig) h.env out]
    cases Expr.evalList d₁.sig args d₁.env with
    | none => exact .none
    | some as =>
      cases Expr.evalList d₁.sig out d₁.env with
      | none => exact .none
      | some vs =>
        exact .some (h.addRow f as vs)

theorem evalActions_envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (as : List Action) :
    Option.Rel Database.EnvAgree (evalActions d₁ as) (evalActions d₂ as) := by
  induction as generalizing d₁ d₂ with
  | nil => exact .some h
  | cons a as ih =>
    have hrel := evalAction_envAgree h a
    cases h₁ : evalAction d₁ a with
    | none =>
      cases h₂ : evalAction d₂ a with
      | none => simp only [evalActions_cons, h₁, h₂, Option.bind_none]; exact .none
      | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₁ =>
      cases h₂ : evalAction d₂ a with
      | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
      | some e₂ =>
        rw [h₁, h₂] at hrel
        cases hrel with
        | some he =>
          simp only [evalActions_cons, h₁, h₂, Option.bind_some]
          exact ih he

/-- Local actions cannot tell agreeing substitutions apart. -/
theorem evalLocalActions_agree {db : Database} (as : List Action) {σ₁ σ₂ : Env}
    (h : Env.Agree σ₁ σ₂) : evalLocalActions db as σ₁ = evalLocalActions db as σ₂ := by
  have hE : Database.EnvAgree { db with env := db.env ++ σ₁ } { db with env := db.env ++ σ₂ } :=
    ⟨rfl, rfl, rfl, rfl, rfl, Env.Agree.append_left db.env h⟩
  have hrel := evalActions_envAgree hE as
  simp only [evalLocalActions]
  cases h₁ : evalActions { db with env := db.env ++ σ₁ } as with
  | none =>
    cases h₂ : evalActions { db with env := db.env ++ σ₂ } as with
    | none => rfl
    | some e₂ => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
  | some e₁ =>
    cases h₂ : evalActions { db with env := db.env ++ σ₂ } as with
    | none => rw [h₁, h₂] at hrel; exact absurd hrel (by intro hc; cases hc)
    | some e₂ =>
      rw [h₁, h₂] at hrel
      cases hrel with
      | some he => simp only [Option.map_some, he.eq_of_env_rules db.env db.rules]

/-! ### Local actions preserve the caller's environment and rules -/
/-- Local actions run the actions with `σ` in scope and then put the caller's
environment and rules back. -/
theorem evalLocalActions_eq_some {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') :
    ∃ d, evalActions { db with env := db.env ++ σ } as = some d ∧
      db' = { d with env := db.env, rules := db.rules } := by
  cases hv : evalActions { db with env := db.env ++ σ } as with
  | none => simp [evalLocalActions, hv] at h
  | some d =>
    simp only [evalLocalActions, hv, Option.map_some, Option.some.injEq] at h
    exact ⟨d, rfl, h.symm⟩

theorem evalLocalActions_env {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.env = db.env := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_rules {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db'.rules = db.rules := by
  obtain ⟨_, _, rfl⟩ := evalLocalActions_eq_some h; rfl

theorem evalLocalActions_contained {db db' : Database} {as : List Action} {σ : Env}
    (h : evalLocalActions db as σ = some db') : db.Contained db' := by
  obtain ⟨_, hv, rfl⟩ := evalLocalActions_eq_some h
  exact ⟨(evalActions_contained hv).terms, (evalActions_contained hv).rows,
    (evalActions_contained hv).eqs⟩

/-- Local actions preserve well-formedness provided the substitution only mentions
terms the database holds — which is what `ValidEnv` guarantees. -/
theorem evalLocalActions_wf {db db' : Database} (hw : db.WF) {as : List Action} {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ db.terms) (h : evalLocalActions db as σ = some db') : db'.WF := by
  have hw' : Database.WF { db with env := db.env ++ σ } := by
    refine ⟨hw.subtermClosed, hw.eqsInTerms, fun b hb => ?_⟩
    exact (List.mem_append.mp hb).elim (hw.envInTerms b) (hσ b)
  obtain ⟨d, hv, rfl⟩ := evalLocalActions_eq_some h
  have hd := evalActions_wf hw' hv
  exact ⟨hd.subtermClosed, hd.eqsInTerms,
    fun b hb => (evalActions_contained hv).terms (hw.envInTerms b hb)⟩

end Egglog
