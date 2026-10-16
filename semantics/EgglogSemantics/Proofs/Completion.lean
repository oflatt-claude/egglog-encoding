import EgglogSemantics.Proofs.SourceMeaning

/-! A proof-only completion records exactly the facts already inferred. -/

namespace Egglog

open InferredFacts

/-- This may be infinite; operational executions still use the original database. -/
def Database.completion (d : Database) : Database :=
  {d with eqs := {p | d.Infers p.1 p.2}}

theorem Database.contained_completion (d : Database) : d.Contained d.completion :=
  ⟨fun _ hp => infers_of_cong (.direct hp)⟩

theorem Database.cong_completion_iff {d : Database} (hw : d.WF) {a b : Term} :
    Cong d.completion a b ↔ d.Infers a b := by
  refine ⟨fun hc => ?_, fun hi => .direct hi⟩
  exact infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)
    (infers_of_cong hc)

theorem Database.mem_completion_iff {d : Database} (hw : d.WF) {t : Term} :
    t ∈ d.completion.terms ↔ d.Infers t t := cong_completion_iff hw

theorem Database.WF.completion {d : Database} (hw : d.WF) : d.completion.WF where
  envInTerms := fun b hb => (d.contained_completion).terms (hw.envInTerms b hb)
  litsIsolated := fun _ hp hl => infers_eq_of_isLit hw hp hl

theorem Database.sameMeaning_completion {d : Database} (hw : d.WF) :
    d.SameMeaning d.completion :=
  ⟨rfl, rfl, rfl, fun _ _ => ⟨infers_mono d.contained_completion,
    infers_of_assertions_only (e := d.completion) hw (fun _ hp => hp)⟩⟩

theorem Database.completion_idempotent {d : Database} (hw : d.WF) :
    d.completion.completion = d.completion := by
  apply Database.ext <;> try rfl
  ext p
  exact (d.sameMeaning_completion hw).inferred p.1 p.2 |>.symm

theorem Database.SameMeaning.completion_eq {d e : Database} (h : d.SameMeaning e) :
    d.completion = e.completion := by
  apply Database.ext
  · exact h.sig
  · exact Set.ext (fun p => h.inferred p.1 p.2)
  · exact h.env
  · exact h.rules

theorem Database.sameMeaning_iff_completion_eq {d e : Database} :
    d.SameMeaning e ↔ d.completion = e.completion := by
  refine ⟨Database.SameMeaning.completion_eq, fun h => ?_⟩
  exact ⟨show d.completion.sig = e.completion.sig from congrArg Database.sig h,
    show d.completion.env = e.completion.env from congrArg Database.env h,
    show d.completion.rules = e.completion.rules from congrArg Database.rules h,
    fun a b => Set.ext_iff.mp (congrArg Database.eqs h) (a, b)⟩

theorem InferredFacts.supported_isValue {d : Database} (hw : d.WF)
    (hv : ∀ t ∈ d.terms, t.IsValue d.sig) :
    ∀ t, Supported d t → t.IsValue d.sig := by
  intro t
  induction t using Term.rec (motive_2 := fun ts =>
      (∀ t ∈ ts, Supported d t) → ∀ t ∈ ts, t.IsValue d.sig) with
  | lit l => intro _; rfl
  | app f args ih =>
      intro ht
      have ha := ih (fun t hm => supported_subterm hw (.arg hm (.refl t)) ht)
      obtain ⟨w, _, hi⟩ := ht
      change interpretApp d f (interpretList d args) = _ at hi
      rw [interpretApp] at hi
      split at hi
      next hex =>
        exact Term.IsValue.app (Term.isValue_app_iff.mp (hv _ hex.choose_spec.1)).1
          ha
      next => cases hi
  | nil => simp_all
  | cons t ts iht ihts =>
      rename_i hs s hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact iht (hs s (by simp))
      · exact ihts (fun s hm => hs s (List.mem_cons_of_mem t hm)) s hm

theorem Database.StoreOk.values_of_allConstructors {d : Database} (hs : d.StoreOk)
    (hc : d.sig.AllConstructors) : ∀ t ∈ d.terms, t.IsValue d.sig := by
  intro t ht
  obtain ⟨p, hp, ht⟩ := Database.mem_terms_iff.mp ht
  rcases hs.typed p hp with hv | ⟨row, hr, _⟩
  · exact ht.elim hv.1.subterm hv.2.subterm
  · obtain ⟨decl, hd, hn, _⟩ := hr
    exact (hn (by simpa [Signature.mergeOf, hd] using hc row.name)).elim

theorem Database.StoreOk.completion {d : Database} (hw : d.WF) (hs : d.StoreOk)
    (hc : d.sig.AllConstructors) : d.completion.StoreOk := by
  have hv : ∀ t ∈ d.completion.terms, t.IsValue d.sig := fun t ht =>
    supported_isValue hw (hs.values_of_allConstructors hc) t
      ((infers_self_iff_supported hw).mp ((Database.mem_completion_iff hw).mp ht))
  have hnone : ∀ row, row ∉ d.completion.entries := by
    intro row hr
    obtain ⟨decl, hd, hn, _⟩ := hr.1
    have hd' : d.sig row.name = some decl := hd
    exact hn (by simpa [Signature.mergeOf, hd'] using hc row.name)
  exact ⟨fun row hr => (hnone row hr).elim, fun row hr => (hnone row hr).elim,
    fun p hp => Or.inl ⟨hv p.1 (Cong.direct hp).mem_left,
      hv p.2 (Cong.direct hp).mem_right⟩, hs.envValues⟩

theorem SourceMeaning.queryHolds_completion_iff {d : Database}
    (hw : d.WF) (hs : d.StoreOk) (hc : d.sig.AllConstructors)
    {q : Query} (hq : ∀ p ∈ q, p.OrderingFree) :
    QueryHolds d.completion q ↔ QueryHolds d q :=
  (queryHolds_iff hw hw.completion hs (hs.completion hw hc) hc
    (d.sameMeaning_completion hw) hq).symm

end Egglog
