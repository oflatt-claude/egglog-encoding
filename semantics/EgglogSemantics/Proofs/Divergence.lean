import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.Source.Ctors
import Mathlib.Order.WellFounded

namespace Egglog

theorem InfiniteTrace.reachable {rel : Database → Database → Prop} {d : Database}
    {trace : Nat → Database} (hstart : trace 0 = d)
    (hstep : ∀ n, rel (trace n) (trace (n + 1))) :
    ∀ n, Relation.ReflTransGen rel d (trace n) := by
  intro n
  induction n with
  | zero => rw [hstart]
  | succ n ih => exact ih.tail (hstep n)

theorem not_infiniteTrace_of_wellFounded {rel : Database → Database → Prop} {d : Database}
    (hw : WellFounded (fun e' e => Relation.ReflTransGen rel d e ∧ rel e e')) :
    ¬ InfiniteTrace rel d := by
  rintro ⟨trace, hstart, hstep⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp hw).false
    ⟨trace, fun n => ⟨InfiniteTrace.reachable hstart hstep n, hstep n⟩⟩

theorem not_mergeDiverges_of_wellFounded {d : Database}
    (hw : WellFounded (fun e' e => MergeClosure d e ∧ MergeStep e e')) :
    ¬ MergeDiverges d := not_infiniteTrace_of_wellFounded hw

theorem changingRunStep_iff {R : RulesetName} {db db' : Database} :
    ChangingRunStep R db db' ↔ RunStep R db db' ∧ ¬ db.SameMeaning db' := by
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨hs, fun hm => hc ((hs.sameMeaning_iff).mp hm)⟩
  · rintro ⟨hs, hm⟩
    exact ⟨hs, fun hc => hm ((hs.sameMeaning_iff).mpr hc)⟩

theorem changingRunReach_runReach {R : RulesetName} {d e : Database}
    (h : Relation.ReflTransGen (ChangingRunStep R) d e) :
    Relation.ReflTransGen (RunStep R) d e :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.1) _ _ h

theorem not_saturateDiverges_of_wellFounded {R : RulesetName} {d : Database}
    (hrounds : WellFounded (fun e' e => Relation.ReflTransGen (RunStep R) d e ∧
      RunStep R e e' ∧ ¬ e.SameMeaning e'))
    (hmerges : ∀ mid, Relation.ReflTransGen (RunStep R) d mid →
      WellFounded (fun e' e => MergeClosure (RunRules R mid) e ∧ MergeStep e e')) :
    ¬ SaturateDiverges R d := by
  rintro (htrace | ⟨mid, hreach, hmerge⟩)
  · apply not_infiniteTrace_of_wellFounded ?_ htrace
    exact hrounds.mono (fun _ _ h => ⟨changingRunReach_runReach h.1, changingRunStep_iff.mp h.2⟩)
  · exact not_mergeDiverges_of_wellFounded
      (hmerges mid (changingRunReach_runReach hreach)) hmerge

theorem ProgramDiverges.append_iff {p q : Program} {d : Database} :
    ProgramDiverges d (p ++ q) ↔
      ProgramDiverges d p ∨ ∃ mid, ProgramStep d p mid ∧ ProgramDiverges mid q := by
  induction p generalizing d with
  | nil =>
      constructor
      · exact fun h => Or.inr ⟨d, .nil, h⟩
      · rintro (h | ⟨mid, hm, h⟩)
        · cases h
        · obtain rfl := hm.nil_inv; exact h
  | cons c cs ih =>
      constructor
      · intro h
        cases h with
        | head hc => exact Or.inl (.head hc)
        | tail hc hs =>
            rcases ih.mp hs with hs | ⟨mid, hm, htail⟩
            · exact Or.inl (.tail hc hs)
            · exact Or.inr ⟨mid, .cons hc hm, htail⟩
      · rintro (h | ⟨mid, hm, h⟩)
        · cases h with
          | head hc => exact .head hc
          | tail hc hs => exact .tail hc (ih.mpr (Or.inl hs))
        · obtain ⟨next, hc, ht⟩ := hm.cons_inv
          exact .tail hc (ih.mpr (Or.inr ⟨mid, ht, h⟩))

theorem not_mergeDiverges_of_allConstructors {d : Database}
    (hc : d.sig.AllConstructors) : ¬ MergeDiverges d := by
  rintro ⟨trace, hstart, hstep⟩
  exact MergeStep.not_of_allConstructors hc (hstart ▸ hstep 0)

theorem not_cmdDiverges_of_allConstructors {d : Database} {c : Cmd}
    (hc : d.sig.AllConstructors) (hd : c.CtorDecl) (hn : c.NoSaturate) :
    ¬ CmdDiverges d c := by
  intro h
  cases h with
  | saturate _ => exact hn.elim
  | run hm => exact not_mergeDiverges_of_allConstructors (d := RunRules _ d) hc hm

/-- Bounded constructor programs have no divergent schedule, even without assuming progress. -/
theorem not_programDiverges_of_allConstructors {d : Database} {P : Program}
    (hc : d.sig.AllConstructors) (hd : P.CtorDecls) (hn : P.NoSaturate) :
    ¬ ProgramDiverges d P := by
  intro h
  induction h with
  | @head d c cs h =>
      exact not_cmdDiverges_of_allConstructors hc (hd c List.mem_cons_self)
        (hn c List.mem_cons_self) h
  | @tail d mid c cs hs _ ih =>
      apply ih (by rw [hs.sig]; exact hc.sigBind (hd c List.mem_cons_self))
        (fun c hc => hd c (List.mem_cons_of_mem _ hc))
        (fun c hc => hn c (List.mem_cons_of_mem _ hc))

end Egglog
