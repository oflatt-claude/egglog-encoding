import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.Congruence.AbstractFiniteRows

/-! Finite proof premises may coexist here without being current runtime rows. -/

namespace Egglog.Provenance.Generated

open Congruence Congruence.Abstract

structure World (P : Program) (src d : Database) : Prop where
  runtime : Live.Runtime d
  signature : d.sig = encodeSig P
  environment : d.env = []
  rules : d.rules = ∅
  sound : SoundTerms d src
  descending : Descending d
  bound : d.terms ⊆ src.terms ∪ SoundRows src

def Fact (P : Program) (src : Database) (t : Term) : Prop :=
  ∃ d, World P src d ∧ t ∈ d.terms

def emptyWorld (P : Program) : Database :=
  { Database.empty with sig := encodeSig P }

theorem World.empty {P : Program} (hp : P.Fragment) (src : Database) :
    World P src (emptyWorld P) := by
  have hw : (emptyWorld P).WF := Database.WF.empty.congr rfl rfl
  have hg := Live.generatedTables_of_mergeShape (encodeSig_mergeShape P)
  have hs : (emptyWorld P).StoreOk := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro row hr; exact hr.2.elim
    · intro row hr; exact hr.2.elim
    · intro p hp; exact hp.elim
    · simp [emptyWorld, Database.empty]
  refine ⟨⟨hw, hs, ⟨?_, (encodeSig_mergeShape P).unionFree, ?_⟩,
    Live.State.of_generated ?_ (encodeSig_ufName hp) hg, hg⟩,
    rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro p hp; exact hp.elim
  · intro r hr; exact hr.elim
  · exact Database.FiniteStore.of_eqs_rules Set.finite_empty Set.finite_empty
  · constructor <;> intros <;>
      simp_all [Database.terms_empty_of_eqs_empty (d := emptyWorld P) rfl]
  · intro a b hm
    simp [Database.terms_empty_of_eqs_empty (d := emptyWorld P) rfl] at hm
  · simp [Database.terms_empty_of_eqs_empty (d := emptyWorld P) rfl]

theorem World.combine {P : Program} {src d e : Database}
    (hd : World P src d) (he : World P src e) : World P src (d.sUnion {e}) := by
  have hsig : e.sig = d.sig := he.signature.trans hd.signature.symm
  have hw := hd.runtime.wf.sUnion (S := {e}) (by intro x hx; simpa using hx ▸ he.runtime.wf)
  have hterms : (d.sUnion {e}).terms = d.terms ∪ e.terms := by simp
  have heqs : (d.sUnion {e}).eqs = d.eqs ∪ e.eqs := by simp
  have hs : (d.sUnion {e}).StoreOk := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro row hr
      obtain ⟨decl, hdecl, hm, _⟩ := hr.1
      exact ⟨decl, hdecl, hm⟩
    · intro row hr t ht
      exact hw.subtermClosed _ (.direct hr.2) (Term.arg_subterms ht t.self_mem_subterms)
    · intro p hp
      rw [heqs] at hp
      rcases hp with hp | hp
      · exact hd.runtime.storeOk.typed p hp
      · simpa only [Database.sUnion_sig, hsig] using he.runtime.storeOk.typed p hp
    · simp [hd.environment]
  have hn : (d.sUnion {e}).NoUnions := by
    refine ⟨?_, hd.runtime.noUnions.sig, hd.runtime.noUnions.rules⟩
    intro p hp
    rw [heqs] at hp
    exact hp.elim (hd.runtime.noUnions.diag p) (he.runtime.noUnions.diag p)
  refine ⟨⟨hw, hs, hn, Live.State.of_generated ?_ hd.runtime.state.uf
    hd.runtime.generated, hd.runtime.generated⟩,
    hd.signature, hd.environment, hd.rules, ?_, ?_, ?_⟩
  · apply Database.FiniteStore.of_eqs_rules
    · rw [heqs]; exact hd.runtime.state.finite.eqs.union he.runtime.state.finite.eqs
    · exact hd.runtime.state.finite.rules
  · exact hd.sound.sUnion (by intro x hx; simpa using hx ▸ he.sound)
  · intro a b ht
    rw [hterms] at ht
    exact ht.elim (hd.descending a b) (he.descending a b)
  · rw [hterms]
    exact Set.union_subset hd.bound he.bound

theorem Fact.collect {P : Program} {src : Database} (hp : P.Fragment)
    {ts : List Term} (ht : ∀ t ∈ ts, Fact P src t) :
    ∃ d, World P src d ∧ ∀ t ∈ ts, t ∈ d.terms := by
  induction ts with
  | nil => exact ⟨emptyWorld P, World.empty hp src, by simp⟩
  | cons t ts ih =>
      obtain ⟨d, hd, htd⟩ := ht t List.mem_cons_self
      obtain ⟨e, he, hte⟩ := ih (fun t hm => ht t (List.mem_cons_of_mem _ hm))
      refine ⟨d.sUnion {e}, hd.combine he, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact (Database.Contained.sUnion _ _).terms htd
      · exact (Database.Contained.mem_sUnion (Set.mem_singleton e)).terms (hte s hs)

theorem Fact.subterm {P : Program} {src : Database} {t s : Term}
    (ht : Fact P src t) (hs : s ∈ t.subtermList) : Fact P src s := by
  obtain ⟨d, hd, ht⟩ := ht
  exact ⟨d, hd, hd.runtime.wf.subtermClosed t ht ((Term.mem_subtermList t).mp hs)⟩

end Egglog.Provenance.Generated
