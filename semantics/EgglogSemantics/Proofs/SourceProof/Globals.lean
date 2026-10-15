import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Step

namespace Egglog.SourceProof

private theorem sourceReach_contained {db db' : Database} {R : RulesetName}
    (hc : db.sig.AllConstructors)
    (h : Relation.ReflTransGen (RunStep R) db db') : db.Contained db' := by
  induction h with
  | refl => exact .refl _
  | @tail mid post hr hs ih =>
      apply ih.trans
      rw [hs.eq_of_allConstructors (by rw [RunReach.sig hr]; exact hc)]
      exact ⟨fun _ hp => Or.inl hp⟩

private theorem sourceStep_contained {db db' : Database} {cmd : Cmd}
    (hc : db.sig.AllConstructors) (hd : cmd.CtorDecl) (hs : CmdStep db cmd db') :
    db.Contained db' := by
  obtain ⟨mid, hm, hn⟩ := hs.reach
  rw [hn.eq_of_allConstructors (cmdReach_allConstructors hc hd hm)]
  cases cmd with
  | action a => exact evalAction_contained hm
  | decl _ _ | rule _ => subst mid; exact ⟨fun _ hp => hp⟩
  | run _ => subst mid; exact ⟨fun _ hp => Or.inl hp⟩
  | saturate _ => exact sourceReach_contained hc hm.reach
  | check _ => rw [hm.2]; exact .refl _

structure Context.Sound (C : Context) (db : Database) : Prop where
  sig : C.sig = db.sig
  globals : ∀ c ∈ C.globals, c.Holds db

theorem Context.Sound.step {C C' : Context} {db db' : Database} {cmd : Cmd}
    (hc : C.Sound db) (hctor : db.sig.AllConstructors) (hd : cmd.CtorDecl)
    (he : db.env = []) (hs : CmdStep db cmd db')
    (hr : C.step cmd = some C') : C'.Sound db' := by
  have hkeep : ∀ c ∈ C.globals, c.Holds db' := fun c h =>
    (hc.globals c h).mono (sourceStep_contained hctor hd hs)
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
      obtain rfl := hm.1.eq_of_allConstructors (by rw [evalAction_sig hd]; exact hctor)
      refine ⟨hc.sig.trans (evalAction_sig hd).symm, ?_⟩
      intro c hmemb
      rcases List.mem_append.mp hmemb with h | h
      · exact hkeep c h
      · exact hfs c h
  | rule r =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩
  | run R =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩
  | saturate R =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩
  | check q =>
      cases Option.some.inj hr
      exact ⟨hc.sig.trans hs.sig.symm, hkeep⟩

theorem Context.Sound.program {db db' : Database} {P : Program}
    (hs : ProgramStep db P db') (hctor : db.CtorState) (hd : P.CtorDecls)
    {C C' : Context} (hc : C.Sound db) (he : db.env = [])
    (hr : P.foldlM Context.step C = some C') : C'.Sound db' := by
  induction hs generalizing C with
  | nil => cases Option.some.inj hr; exact hc
  | cons hstep hrest ih =>
      obtain ⟨D, hD, htail⟩ := Option.bind_eq_some_iff.mp hr
      exact ih (hstep.ctorState hctor (hd _ List.mem_cons_self))
        (fun c hm => hd c (List.mem_cons_of_mem _ hm))
        (hc.step hctor.sig (hd _ List.mem_cons_self) he hstep hD)
        (hstep.env.trans he) htail

/-- Every `Fiat` fact is justified by the original program's execution. -/
theorem contextOf_sound {P : Program} {C : Context} {db : Database}
    (hr : contextOf P = some C) (hs : ProgramStep Database.empty P db)
    (hd : P.CtorDecls) : C.Sound db :=
  Context.Sound.program hs Database.CtorState.empty hd ⟨rfl, by simp [Context.empty]⟩ rfl hr

theorem fiat_sound {P : Program} {C : Context} {db : Database} {c : Claim}
    (hr : contextOf P = some C) (hs : ProgramStep Database.empty P db)
    (hd : P.CtorDecls) (hc : c ∈ C.globals) : c.Holds db :=
  (contextOf_sound hr hs hd).globals c hc

end Egglog.SourceProof
