import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Merge

namespace Egglog.SourceProof

structure Context.Sound (C : Context) (db : Database) : Prop where
  sig : C.sig = db.sig
  globals : ∀ c ∈ C.globals, c.Holds db

theorem Context.Sound.step {C C' : Context} {db db' : Database} {cmd : Cmd}
    (hc : C.Sound db) (he : db.env = []) (hs : CmdStep db cmd db')
    (hr : C.step cmd = some C') : C'.Sound db' := by
  have hkeep : ∀ c ∈ C.globals, c.Holds db' := fun c h =>
    (hc.globals c h).mono hs.contained
  cases cmd with
  | decl f d =>
      simp only [Context.step] at hr
      split at hr
      · contradiction
      · cases Option.some.inj hr
        exact ⟨by simpa [Cmd.sigBind, hc.sig] using hs.sig.symm, hkeep⟩
  | action a =>
      obtain ⟨fs, hf, hC⟩ := Option.map_eq_some_iff.mp hr
      cases hC
      have hf' : actionFacts db.sig db.env a = some fs := by rw [he, ← hc.sig]; exact hf
      obtain ⟨d, hd, hfs⟩ := actionFacts_sound hf'
      obtain ⟨d', hd', hm⟩ := hs
      have hd'e : evalAction db a = some d' := hd'
      rw [hd] at hd'e
      cases Option.some.inj hd'e
      refine ⟨hc.sig.trans ((evalAction_sig hd).symm.trans hm.sig.symm), ?_⟩
      intro c hmemb
      rcases List.mem_append.mp hmemb with h | h
      · exact hkeep c h
      · exact (hfs c h).mono hm.contained
  | rule r =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩
  | run R =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩
  | saturate R =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩

theorem Context.Sound.program {db db' : Database} {P : Program}
    (hs : ProgramStep db P db') {C C' : Context} (hc : C.Sound db) (he : db.env = [])
    (hr : P.foldlM Context.step C = some C') : C'.Sound db' := by
  induction hs generalizing C with
  | nil => cases Option.some.inj hr; exact hc
  | cons hstep hrest ih =>
      obtain ⟨D, hD, htail⟩ := Option.bind_eq_some_iff.mp hr
      exact ih (hc.step he hstep hD) (hstep.env.trans he) htail

/-- Every `Fiat` fact is justified by the original program's execution. -/
theorem contextOf_sound {P : Program} {C : Context} {db : Database}
    (hr : contextOf P = some C) (hs : ProgramStep Database.empty P db) : C.Sound db :=
  Context.Sound.program hs ⟨rfl, by simp [Context.empty]⟩ rfl hr

theorem fiat_sound {P : Program} {C : Context} {db : Database} {c : Claim}
    (hr : contextOf P = some C) (hs : ProgramStep Database.empty P db)
    (hc : c ∈ C.globals) : c.Holds db := (contextOf_sound hr hs).globals c hc

end Egglog.SourceProof
