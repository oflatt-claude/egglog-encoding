import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Source.WellFormed

/-! Well-formed constructor programs with bounded rounds have a finite result. -/

namespace Egglog

private theorem declared_ctor {sig : Signature} (hc : sig.AllConstructors)
    {f : FnName} {k : Nat} (h : (sig f).map FnDecl.arity = some k) : sig.IsCtor f := by
  obtain ⟨dc, hd, _⟩ := Option.map_eq_some_iff.mp h
  exact ⟨dc, hd, by simpa [Signature.mergeOf, hd] using hc f⟩

private theorem expr_evaluable {sig : Signature} (hc : sig.AllConstructors) {e : Expr}
    (h : ∀ fk ∈ e.ctors, (sig fk.1).map FnDecl.arity = some fk.2) :
    e.Evaluable sig := by
  intro f hf
  obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hf
  exact declared_ctor hc (h (f, k) hk)

mutual
private theorem expr_width {sig : Signature} : ∀ e : Expr,
    (∀ fk ∈ e.ctors, (sig fk.1).map FnDecl.arity = some fk.2) → e.WidthOk sig
  | .lit _, _ => trivial
  | .var _, _ => trivial
  | .app f args, h => by
      refine ⟨?_, exprs_width args (fun fk hk => h fk (List.mem_cons_of_mem _ hk))⟩
      intro dc hd
      have hh := h (f, args.length) List.mem_cons_self
      simpa [hd] using hh.symm
  | .min a b, h =>
      ⟨expr_width a (fun fk hk => h fk (List.mem_append_left _ hk)),
       expr_width b (fun fk hk => h fk (List.mem_append_right _ hk))⟩

private theorem exprs_width {sig : Signature} : ∀ es : List Expr,
    (∀ fk ∈ Expr.ctorsList es, (sig fk.1).map FnDecl.arity = some fk.2) →
      Expr.WidthOkList es sig
  | [], _ => trivial
  | e :: es, h =>
      ⟨expr_width e (fun fk hk => h fk (List.mem_append_left _ hk)),
       exprs_width es (fun fk hk => h fk (List.mem_append_right _ hk))⟩
end

private theorem atom_properties {sig : Signature} (hc : sig.AllConstructors) {e : Expr}
    (h : ∀ fk ∈ e.ctors, (sig fk.1).map FnDecl.arity = some fk.2) :
    e.AtomEvaluable sig ∧ e.AtomWidthOk sig := by
  have he := expr_evaluable hc h
  have hw := expr_width e h
  cases e with
  | app f args =>
      obtain ⟨dc, hd, hm⟩ := he f List.mem_cons_self
      refine ⟨⟨by simp [hd], fun g hg => he g (List.mem_cons_of_mem _ hg)⟩, ?_, hw.2⟩
      intro dc' hd'
      have hdc : dc' = dc := Option.some.inj (hd'.symm.trans hd)
      subst dc'
      simpa [FnDecl.entryWidth, hm] using hw.1 dc hd
  | lit | var | min => exact ⟨he, hw⟩

private theorem constructors_normal {d : Database} (hc : d.sig.AllConstructors) :
    MergeNormal d := by
  intro row hr
  obtain ⟨dc, hd, hm, _⟩ := hr.1
  exact (hm (by simpa [Signature.mergeOf, hd] using hc row.name)).elim

private theorem cmd_exists {d : Database} (hc : d.sig.AllConstructors) (henv : d.env = [])
    {c : Cmd} (hw : c.WellFormed d.sig) (hn : c.NoSaturate) (hdecl : c.CtorDecl) :
    ∃ r, CmdEval d c r := by
  classical
  cases c with
  | action a =>
      have he : a.Evaluable d.sig ∧ a.WidthOk d.sig := by
        cases a with
        | expr e => exact atom_properties hc hw.2.2
        | union a b =>
            have ha := fun fk hk => hw.2.2 fk (List.mem_append_left b.ctors hk)
            have hb := fun fk hk => hw.2.2 fk (List.mem_append_right a.ctors hk)
            exact ⟨⟨⟨hw.2.1.1, expr_evaluable hc ha⟩, hw.2.1.2, expr_evaluable hc hb⟩,
              expr_width a ha, expr_width b hb⟩
      obtain ⟨e, heval, _⟩ := evalAction_isSome_of_scoped
        (by rw [henv]; exact Scope.Models.empty) hw.1 he.1
        (by simp [henv]) he.2
      exact ⟨.ok e, .ok (.of_reach heval (constructors_normal (by
        rw [evalAction_sig heval]; exact hc)))⟩
  | run R => exact ⟨_, .ok (.of_reach rfl (constructors_normal hc))⟩
  | rule r => exact ⟨_, .ok (.of_reach rfl (constructors_normal hc))⟩
  | decl f dc =>
      exact ⟨_, .ok (.of_reach rfl (constructors_normal (hc.sigBind hdecl)))⟩
  | saturate R => exact hn.elim
  | check q =>
      by_cases hq : QueryHolds d q
      · exact ⟨.ok d, .ok ⟨hq, rfl⟩⟩
      · exact ⟨.checkFailed, .checkFailed hq⟩

theorem Program.WellFormedFrom.eval_exists {P : Program} {d : Database}
    (hw : P.WellFormedFrom d.sig) (hn : P.NoSaturate) (hctors : P.CtorDecls)
    (hc : d.sig.AllConstructors) (henv : d.env = []) : ∃ r, Eval d P r := by
  induction P generalizing d with
  | nil => exact ⟨.ok d, .nil⟩
  | cons c cs ih =>
      have hd := hctors c List.mem_cons_self
      obtain ⟨r, hr⟩ := cmd_exists hc henv hw.1 (hn c List.mem_cons_self) hd
      cases hr with
      | ok hs =>
          obtain ⟨r, hr⟩ := ih (by rw [hs.sig]; exact hw.2)
            (fun c' hm => hn c' (List.mem_cons_of_mem _ hm))
            (fun c' hm => hctors c' (List.mem_cons_of_mem _ hm))
            (by rw [hs.sig]; exact hc.sigBind hd) (hs.env.trans henv)
          exact ⟨r, .cons (.ok hs) hr⟩
      | checkFailed hq => exact ⟨.checkFailed, .fail (.checkFailed hq)⟩

/-- Source termination follows from syntax; no finite-execution premise is needed. -/
theorem Program.WellFormed.eval_exists {P : Program} (hw : P.WellFormed)
    (hn : P.NoSaturate) (hc : P.CtorDecls) : ∃ r, Eval Database.empty P r :=
  Program.WellFormedFrom.eval_exists hw hn hc Database.CtorState.empty.sig rfl

end Egglog
