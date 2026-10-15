import EgglogSemantics.Proofs.Congruence.LiveRead
import EgglogSemantics.Proofs.Congruence.AbstractRuntime

/-! Sequential merging retains the readings of a block evaluated without merges. -/

namespace Egglog.Congruence.Live

structure Covers (d e : Database) : Prop where
  sig : d.sig = e.sig
  rows : ∀ f cs a, Entry.mk f cs [a] ∈ d.entries →
    ∃ b, Entry.mk f cs [b] ∈ e.entries ∧ Joined e a b

theorem Covers.refl (d : Database) : Covers d d :=
  ⟨rfl, fun _ _ a ha => ⟨a, ha, .refl a⟩⟩

theorem Covers.joined {d e : Database} (h : Covers d e)
    {a b : Term} (hj : Joined d a b) : Joined e a b := by
  induction hj with
  | refl a => exact .refl a
  | edge hr =>
      obtain ⟨c, hc, hbc⟩ := h.rows ufName [_] _ hr
      exact (Joined.edge hc).trans hbc.symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Covers.trans {d e f : Database} (h : Covers d e) (h' : Covers e f) :
    Covers d f := by
  refine ⟨h.sig.trans h'.sig, fun g cs a ha => ?_⟩
  obtain ⟨b, hb, hab⟩ := h.rows g cs a ha
  obtain ⟨c, hc, hbc⟩ := h'.rows g cs b hb
  exact ⟨c, hc, (h'.joined hab).trans hbc⟩

theorem Covers.of_entries {d e : Database} (hsig : d.sig = e.sig)
    (h : d.entries ⊆ e.entries) : Covers d e :=
  ⟨hsig, fun _ _ a ha => ⟨a, h ha, .refl a⟩⟩

theorem Covers.repr {d e : Database} (h : Covers d e)
    {t i : Term} (hr : Repr d t i) : Repr e t i :=
  hr.transport h.rows (fun _ _ hj => h.joined hj)

theorem Covers.reads {d e src : Database} (h : Covers d e) (hr : Reads d src) :
    Reads e src := hr.transport (fun _ _ ht => h.repr ht)

theorem Covers.mergeClosure {d e : Database} (h : State d) (hd : d.Diag)
    (hc : MergeClosure d e) : Covers d e :=
  ⟨hc.sig.symm, fun _ _ _ hr => by
    obtain ⟨b, hb, hj, _⟩ := row_closure h hd hc hr
    exact ⟨b, hb, hj⟩⟩

theorem Covers.addTerm {d e : Database} (h : Covers d e) (t : Term) :
    Covers (d.addTerm t) (e.addTerm t) := by
  refine ⟨h.sig, fun f cs a ha => ?_⟩
  rcases Database.mem_addTerm_entries.mp ha with ha | ⟨hv, ht⟩
  · obtain ⟨b, hb, hj⟩ := h.rows f cs a ha
    exact ⟨b, Database.mem_addTerm_entries.mpr (Or.inl hb),
      hj.mono (fun _ hr => Database.mem_addTerm_entries.mpr (Or.inl hr))⟩
  · exact ⟨a, Database.mem_addTerm_entries.mpr (Or.inr ⟨h.sig ▸ hv, ht⟩), .refl a⟩

theorem evalAction_covers {d e post : Database} (h : Covers d e) (henv : d.env = e.env)
    {a : Action} (hf : evalAction d a = some post) :
    ∃ out, evalAction e a = some out ∧ Covers post out ∧ post.env = out.env := by
  rcases evalAction_eq_some hf with ⟨exp, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, hl, rfl⟩
  · exact ⟨e.addTerm t, by simp [evalAction, ← h.sig, ← henv, he], h.addTerm t, henv⟩
  · refine ⟨e.addEq ta tb, ?_, ?_, henv⟩
    · simp only [not_or, Bool.not_eq_true] at hl
      simp [evalAction, ← h.sig, ← henv, ha, hb, hl.1, hl.2]
    · have hva := Expr.eval_isValue ha
      have hvb := Expr.eval_isValue hb
      refine ⟨h.sig, ?_⟩
      rw [Database.addEq_entries hva hvb,
        Database.addEq_entries (h.sig ▸ hva) (h.sig ▸ hvb)]
      exact fun f cs x hx => by
        obtain ⟨y, hy, hj⟩ := h.rows f cs x hx
        exact ⟨y, hy, hj.mono (by rw [Database.addEq_entries (h.sig ▸ hva) (h.sig ▸ hvb)])⟩

theorem evalActions_covers_program {d e post final : Database} (h : Covers d e)
    (henv : d.env = e.env) (he : Runtime e) {as : List Action}
    (hu : Actions.UnionFree as) (hf : evalActions d as = some post)
    (hr : ProgramStep e (as.map Cmd.action) final) : Covers post final := by
  induction as generalizing d e with
  | nil =>
      obtain rfl := Option.some.inj hf
      obtain rfl := hr.nil_inv
      exact h
  | cons a as ih =>
      obtain ⟨mid, hm, hrest⟩ := Option.bind_eq_some_iff.mp hf
      obtain ⟨next, hc, hr⟩ := hr.cons_inv
      obtain ⟨raw, hraw, hmerge⟩ := hc
      obtain ⟨raw', hraw', hcov, henv'⟩ := evalAction_covers h henv hm
      obtain rfl := Option.some.inj (hraw'.symm.trans hraw)
      have hmrg := Covers.mergeClosure (he.state.evalAction he.generated hraw')
        (evalAction_diag hu.1 he.noUnions.diag hraw') hmerge.1
      exact ih (hcov.trans hmrg) (henv'.trans hmerge.1.envRules.1.symm)
        (he.cmd (c := .action a) trivial hu.1 ⟨raw', hraw', hmerge⟩) hu.2 hrest hr

end Egglog.Congruence.Live
