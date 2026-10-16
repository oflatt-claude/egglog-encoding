import EgglogSemantics.Proofs.Provenance.Model
import EgglogSemantics.Proofs.Provenance.GeneratedContext
import EgglogSemantics.Proofs.Provenance.GeneratedRules
import EgglogSemantics.Proofs.Provenance.GeneratedMerges

namespace Egglog.Provenance.Generated

open Congruence Congruence.Abstract InferredFacts

theorem model {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src) :
    Model (encode P) (encodeSig P) (Fact P src.completion) where
  ruleFacts := by
    intro r σ premises fs hr hprem hf
    obtain ⟨d, hd, hm⟩ := Fact.collect hp (fun t ht => (hprem t ht).1)
    have hf' : Provenance.ruleFacts d.sig r σ premises = some fs := hd.signature ▸ hf
    obtain ⟨post, _, hrt, hsig, henv, hrules, hsound, hdesc, hbound, hmem⟩ :=
      ruleFacts_sound hp hs hclosed hd.runtime hd.signature hd.environment
        hd.sound hd.descending hr hm hf'
    have hw : World P src.completion post :=
      ⟨hrt, hsig.trans hd.signature, henv.trans hd.environment,
        hrules.trans hd.rules, hsound, hdesc,
        hbound.trans (Set.union_subset hd.bound (Set.Subset.refl _))⟩
    exact fun t ht => ⟨post, hw, hmem t ht⟩
  mergeFacts := by
    intro f old new fs ho hn hf
    exact mergeFacts_closed hp ho.1 hn.1 ho.2 hn.2 hf
  subterms := fun h _ ht => h.1.subterm ht

/-- Acceptance preserves source meaning, including certificates for replaced rows. -/
theorem check_fact {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {pf : Proof} {t : Term} (hc : check (encode P) pf = some t) :
    Fact P src.completion t := by
  have hh := hc
  unfold check at hh
  split at hh
  · contradiction
  · obtain ⟨C, hC, _⟩ := Option.bind_eq_some_iff.mp hh
    exact check_sound_in_model (model hp hs hclosed) hC (contextOf_encode_sig hC) hc

theorem check_uf_infers {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {pf : Proof} {a b : Term} (hc : check (encode P) pf = some (.app ufName [a, b])) :
    src.Infers a b := by
  obtain ⟨d, hd, ht⟩ := check_fact hp hs hclosed hc
  exact (Database.cong_completion_iff (hs.ctorState Database.CtorState.empty hp.ctorsOnly).wf).mp
    (hd.sound.2 a b ht)

theorem entrySound_infers {src : Database} (hw : src.WF) {f : FnName}
    {cs : List Term} {e : Term} (h : EntrySound src.completion f cs e) :
    src.Infers e (.app f cs) := by
  obtain ⟨as, ha, hl, he⟩ := h
  have hargs : List.Forall₂ src.Infers as cs := by
    clear ha he
    induction as generalizing cs with
    | nil => cases hl; exact .nil
    | cons a as ih =>
        cases hl with
        | cons hab hrest => exact .cons ((Database.cong_completion_iff hw).mp hab) (ih hrest)
  exact infers_trans hw (infers_symm hw ((Database.cong_completion_iff hw).mp he))
    (infers_congr hw ((Database.mem_completion_iff hw).mp ha) hargs)

theorem check_view_infers {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {pf : Proof} {f : FnName} {cs : List Term} {e : Term}
    (hc : check (encode P) pf = some (.app (viewName f) (cs ++ [e]))) :
    src.Infers e (.app f cs) := by
  obtain ⟨d, hd, ht⟩ := check_fact hp hs hclosed hc
  exact entrySound_infers (hs.ctorState Database.CtorState.empty hp.ctorsOnly).wf
    (hd.sound.1 f cs e ht)

end Egglog.Provenance.Generated
