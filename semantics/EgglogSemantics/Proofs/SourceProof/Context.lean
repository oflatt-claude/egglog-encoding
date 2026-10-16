import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Step

namespace Egglog.SourceProof

structure Context.Sound (C : Context) (db : Database) : Prop where
  sig : C.sig = db.sig

theorem Context.Sound.step {C C' : Context} {db db' : Database} {cmd : Cmd}
    (hc : C.Sound db) (hs : CmdStep db cmd db')
    (hr : C.step cmd = some C') : C'.Sound db' := by
  cases cmd with
  | decl f d =>
      simp only [Context.step] at hr
      split at hr
      · contradiction
      · cases Option.some.inj hr
        exact ⟨by simpa [Cmd.sigBind, hc.sig] using hs.sig.symm⟩
  | rule _ | run _ | saturate _ | check _ =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm⟩

theorem Context.Sound.program {db db' : Database} {P : Program}
    (hs : ProgramStep db P db') {C C' : Context} (hc : C.Sound db)
    (hr : P.foldlM Context.step C = some C') : C'.Sound db' := by
  induction hs generalizing C with
  | nil => cases Option.some.inj hr; exact hc
  | cons hstep hrest ih =>
      obtain ⟨D, hD, htail⟩ := Option.bind_eq_some_iff.mp hr
      exact ih (hc.step hstep hD) htail

/-- Context collection agrees with the source execution's signature. -/
theorem contextOf_sound {P : Program} {C : Context} {db : Database}
    (hr : contextOf P = some C) (hs : ProgramStep Database.empty P db) : C.Sound db :=
  Context.Sound.program hs ⟨rfl⟩ hr

end Egglog.SourceProof
