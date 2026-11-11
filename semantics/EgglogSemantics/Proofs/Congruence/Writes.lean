import EgglogSemantics.Proofs.Congruence.Target
import EgglogSemantics.Proofs.Congruence.Sound
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.Writes
import EgglogSemantics.Proofs.Diagonal

/-! The writes of a compiled head: a build writes the self-loop of every subexpression's
value, a union adds the two edges to the smaller side. Each compiled row is between
congruent source terms, goes down the term order, comes with the self-loops of its
endpoints, and every source write is derivable from the compiled rows. -/

namespace Egglog.Congruence

theorem orderingFreeList_mem {a : Expr} : ∀ {es : List Expr}, a ∈ es →
    Expr.OrderingFreeList es → a.OrderingFree
  | [], h, _ => by simp at h
  | e :: es, h, ho => by
      obtain ⟨hoe, hoes⟩ := Expr.orderingFreeList_cons ho
      rcases List.mem_cons.mp h with rfl | h
      · exact hoe
      · exact orderingFreeList_mem h hoes

/-- A variable of an argument is a variable of the list. -/
theorem var_mem_varsList_of_mem {v : Var} {e : Expr} : ∀ {es : List Expr}, e ∈ es →
    v ∈ e.vars → v ∈ Expr.varsList es
  | [], h, _ => by simp at h
  | e' :: es, h, hv => by
      rw [Expr.varsList_cons, List.mem_union_iff]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hv
      · exact Or.inr (var_mem_varsList_of_mem h hv)

/-- The values a build writes self-loops for: every subexpression's value. -/
inductive BuildTerm (σ : Env) : Expr → Term → Prop
  | lit (l : Lit) : BuildTerm σ (.lit l) (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → BuildTerm σ (.var v) t
  | app_self {f : FnName} {args : List Expr} {ts : List Term} :
      Expr.evalList args σ = some ts → BuildTerm σ (.app f args) (.app f ts)
  | app_arg {f : FnName} {args : List Expr} {e : Expr} {u : Term} :
      e ∈ args → BuildTerm σ e u → BuildTerm σ (.app f args) u

/-- The value of an ordering-free expression is a build term of it. -/
theorem BuildTerm.self {σ : Env} : ∀ {e : Expr} {t : Term}, e.OrderingFree →
    e.eval σ = some t → BuildTerm σ e t
  | .lit _, _, _, h => by
      rw [Expr.eval_lit, Option.some.injEq] at h
      rw [← h]; exact .lit _
  | .var _, _, _, h => .var h
  | .min _ _, _, ho, _ => (Expr.not_orderingFree_min ho).elim
  | .app f args, t, _, h => by
      rw [Expr.eval_app_ctor] at h
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .app_self hts

/-- An argument's value is among the evaluated arguments. -/
theorem eval_mem_of_evalList {σ : Env} {es : List Expr} {ts : List Term}
    (hts : Expr.evalList es σ = some ts) {e : Expr} (he : e ∈ es) :
    ∃ t, e.eval σ = some t ∧ t ∈ ts := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hts i (List.getElem?_eq_getElem hi)
  exact ⟨t, hev, List.mem_of_getElem? ht⟩

/-- Build terms are subterms of the value. -/
theorem BuildTerm.subterm {σ : Env} {e : Expr} {u t : Term} (hb : BuildTerm σ e u)
    (h : e.eval σ = some t) : Term.IsSubterm u t := by
  induction hb generalizing t with
  | lit l =>
    rw [Expr.eval_lit, Option.some.injEq] at h
    rw [← h]; exact .refl _
  | var hv =>
    rw [Expr.eval_var] at h
    rw [Option.some.inj (hv.symm.trans h)]
    exact .refl _
  | app_self hts =>
    rw [Expr.eval_app_ctor, hts, Option.map_some, Option.some.injEq] at h
    rw [← h]; exact .refl _
  | app_arg he _ ih =>
    rw [Expr.eval_app_ctor] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨te, hev, hmem⟩ := eval_mem_of_evalList hts he
    exact (ih hev).trans (.arg hmem (.refl _))

/-- Every subterm of a value is a build term or lies inside a variable's binding. -/
theorem subterm_build {σ : Env} (e : Expr) : ∀ {t u : Term}, e.OrderingFree →
    e.eval σ = some t → Term.IsSubterm u t →
    BuildTerm σ e u ∨ ∃ v ∈ e.vars, ∃ w, Env.lookup v σ = some w ∧ Term.IsSubterm u w := by
  induction e using Expr.recExpr with
  | lit l =>
    intro t u _ h hu
    rw [Expr.eval_lit, Option.some.injEq] at h
    subst h
    cases hu with
    | refl => exact Or.inl (.lit l)
  | var v =>
    intro t u _ h hu
    rw [Expr.eval_var] at h
    exact Or.inr ⟨v, by simp, t, h, hu⟩
  | min a b _ _ =>
    intro _ _ ho _ _
    exact (Expr.not_orderingFree_min ho).elim
  | app f args ih =>
    intro t u ho h hu
    rw [Expr.eval_app_ctor] at h
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    cases hu with
    | refl => exact Or.inl (.app_self hts)
    | arg ha hua =>
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have hi' : i < args.length := by rw [← Expr.evalList_length hts]; exact hi
      obtain ⟨te, hte, hev⟩ := Expr.getElem?_of_evalList hts i (List.getElem?_eq_getElem hi')
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hte
      rw [hte] at hua
      have hoa : args[i].OrderingFree :=
        orderingFreeList_mem (List.getElem_mem hi') (Expr.orderingFree_app ho)
      rcases ih _ (List.getElem_mem hi') hoa hev hua with hb | ⟨v, hv, w, hw, huw⟩
      · exact Or.inl (.app_arg (List.getElem_mem hi') hb)
      · exact Or.inr ⟨v, by
          rw [Expr.vars_app]
          exact var_mem_varsList_of_mem (List.getElem_mem hi') hv, w, hw, huw⟩

/-! ### The writes of a build -/

/-- The self-loop row of a value. -/
abbrev selfRow (u : Term) : Term × Term := (ufRowT u u, ufRowT u u)

theorem build_lit (l : Lit) : encodeBuildWith {} (.lit l) = [.expr (ufRow (.lit l) (.lit l))] := rfl
theorem build_var (v : Var) : encodeBuildWith {} (.var v) = [.expr (ufRow (.var v) (.var v))] := rfl
theorem build_app (f : FnName) (args : List Expr) : encodeBuildWith {} (.app f args) =
    encodeBuildArgsWith {} args ++ [.expr (ufRow (.app f args) (.app f args))] := by
  simp [encodeBuildWith]
theorem buildArgs_nil : encodeBuildArgsWith {} [] = [] := rfl
theorem buildArgs_cons (e : Expr) (es : List Expr) :
    encodeBuildArgsWith {} (e :: es) = encodeBuildWith {} e ++ encodeBuildArgsWith {} es := rfl

theorem write_ufRow {σ : Env} {a b : Expr} {s t : Term} (ha : a.eval σ = some s)
    (hb : b.eval σ = some t) :
    Action.write σ (.expr (ufRow a b)) = some {(ufRowT s t, ufRowT s t)} := by
  simp [Action.write, ufRow, Expr.evalList, ha, hb]

theorem writes_ufRow {σ : Env} {a b : Expr} {s t : Term} (ha : a.eval σ = some s)
    (hb : b.eval σ = some t) :
    Action.writes σ [.expr (ufRow a b)] = some {(ufRowT s t, ufRowT s t)} := by
  rw [Action.writes_singleton, write_ufRow ha hb]

mutual

/-- A build writes exactly the self-loops of its build terms. -/
theorem build_writes {σ : Env} : ∀ (e : Expr), e.OrderingFree →
    (∀ v ∈ e.vars, (Env.lookup v σ).isSome) →
    ∃ W, Action.writes σ (encodeBuildWith {} e) = some W ∧
      ∀ q, q ∈ W ↔ ∃ u, BuildTerm σ e u ∧ q = selfRow u
  | .lit l, _, _ => by
      refine ⟨{selfRow (.lit l)}, writes_ufRow rfl rfl, fun q => ?_⟩
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact ⟨_, .lit l, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        cases hu; rfl
  | .var v, _, hb => by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hb v (by simp))
      refine ⟨{selfRow t}, writes_ufRow (by simpa using ht) (by simpa using ht), fun q => ?_⟩
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact ⟨t, .var ht, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        cases hu with
        | var hu => rw [Option.some.inj (hu.symm.trans ht)]
  | .min _ _, ho, _ => (Expr.not_orderingFree_min ho).elim
  | .app f args, ho, hb => by
      obtain ⟨W, hW, hmem⟩ := buildArgs_writes args (Expr.orderingFree_app ho) (by simpa using hb)
      obtain ⟨ts, hts⟩ := Expr.evalList_isSome args (fun v hv =>
        Env.lookup_isSome_iff_mem_dom.mp (hb v (by simpa using hv)))
      have hself : Action.writes σ [.expr (ufRow (.app f args) (.app f args))] =
          some {selfRow (.app f ts)} :=
        writes_ufRow (by rw [Expr.eval_app_ctor, hts]; rfl) (by rw [Expr.eval_app_ctor, hts]; rfl)
      refine ⟨W ∪ {selfRow (.app f ts)}, ?_, fun q => ?_⟩
      · rw [build_app, Action.writes_append, hW, Option.bind_some, hself, Option.map_some]
      · simp only [Set.mem_union, Set.mem_singleton_iff, hmem]
        constructor
        · rintro (⟨e, he, u, hu, rfl⟩ | rfl)
          · exact ⟨u, .app_arg he hu, rfl⟩
          · exact ⟨_, .app_self hts, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          cases hu with
          | app_self hts' =>
            right
            rw [Option.some.inj (hts'.symm.trans hts)]
          | app_arg he hu => exact Or.inl ⟨_, he, u, hu, rfl⟩

theorem buildArgs_writes {σ : Env} : ∀ (es : List Expr), Expr.OrderingFreeList es →
    (∀ v ∈ Expr.varsList es, (Env.lookup v σ).isSome) →
    ∃ W, Action.writes σ (encodeBuildArgsWith {} es) = some W ∧
      ∀ q, q ∈ W ↔ ∃ e ∈ es, ∃ u, BuildTerm σ e u ∧ q = selfRow u
  | [], _, _ => ⟨∅, by rw [buildArgs_nil]; rfl, by simp⟩
  | e :: es, ho, hb => by
      obtain ⟨hoe, hoes⟩ := Expr.orderingFreeList_cons ho
      obtain ⟨W₁, hW₁, hmem₁⟩ := build_writes e hoe (fun v hv => hb v (by simp [hv]))
      obtain ⟨W₂, hW₂, hmem₂⟩ := buildArgs_writes es hoes (fun v hv => hb v (by simp [hv]))
      refine ⟨W₁ ∪ W₂, ?_, fun q => ?_⟩
      · rw [buildArgs_cons, Action.writes_append, hW₁, Option.bind_some, hW₂, Option.map_some]
      · simp only [Set.mem_union, hmem₁, hmem₂, List.mem_cons]
        constructor
        · rintro (⟨u, hu, rfl⟩ | ⟨e', he', u, hu, rfl⟩)
          · exact ⟨e, Or.inl rfl, u, hu, rfl⟩
          · exact ⟨e', Or.inr he', u, hu, rfl⟩
        · rintro ⟨e', rfl | he', u, hu, rfl⟩
          · exact Or.inl ⟨u, hu, rfl⟩
          · exact Or.inr ⟨e', he', u, hu, rfl⟩

end

end Egglog.Congruence
