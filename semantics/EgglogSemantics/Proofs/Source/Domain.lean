import EgglogSemantics.Source.Domain
import EgglogSemantics.Proofs.Step
import Mathlib.Data.List.Dedup

/-! Facts about the source fragment's definitions. -/

namespace Egglog

/-- The clause moves to a state that still builds what it built and still binds what it
bound. -/
theorem Database.GlobalsInline.mono_src {src src' : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G)
    (hsig : ∀ (e : Expr) (t : Term), e.eval src.sig [] = some t → e.eval src'.sig [] = some t)
    (henv : ∀ v t, Env.lookup v src.env = some t → Env.lookup v src'.env = some t) :
    src'.GlobalsInline G := by
  intro v e he
  obtain ⟨hcl, t, hev, hlk⟩ := h v e he
  exact ⟨hcl, t, hsig e t hev, henv v t hlk⟩

/-- The static half of the clause, which is what the three text conditions need. -/
theorem Database.GlobalsInline.closed {src : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) : Expr.ClosedG G := fun v e he => (h v e he).1

/-- The environment and the signature are both unmoved, which is the shape a run, a
saturation and a rule declaration all have. -/
theorem Database.GlobalsInline.of_eq {src src' : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) (hsig : src'.sig = src.sig) (henv : src'.env = src.env) :
    src'.GlobalsInline G :=
  h.mono_src (fun _ _ he => by rw [hsig]; exact he) (fun _ _ hv => by rw [henv]; exact hv)

@[inherit_doc Pattern.GroundedAt]
theorem Pattern.Grounded.groundedAt {src : Database} :
    ∀ {p : Pattern}, p.Grounded → p.GroundedAt src
  | .expr _, h => fun l he => absurd he (h l)
  | .eq _ _, h => h.imp (fun h₁ l he => absurd he (h₁ l)) (fun h₂ l he => absurd he (h₂ l))

theorem Action.unionFreeB_iff (a : Action) : a.unionFreeB = true ↔ a.UnionFree := by
  cases a <;> simp [Action.unionFreeB, Action.UnionFree]

theorem Actions.unionFreeB_iff : ∀ as : List Action,
    as.all Action.unionFreeB = true ↔ Actions.UnionFree as
  | [] => by simp
  | a :: as => by
      simp only [List.all_cons, Bool.and_eq_true, Actions.UnionFree, Action.unionFreeB_iff,
        Actions.unionFreeB_iff as]

@[inherit_doc Cmd.ruleUnionFreeB]
theorem Cmd.ruleUnionFreeB_iff (r : Rule) :
    (Cmd.rule r).ruleUnionFreeB = true ↔ r.UnionFree :=
  Actions.unionFreeB_iff r.actions

end Egglog
