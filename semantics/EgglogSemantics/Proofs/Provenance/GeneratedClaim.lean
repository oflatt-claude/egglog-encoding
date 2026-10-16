import EgglogSemantics.Resugar.Claim
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness

/-! Mapping an accepted generated fact to a source equality needs no proof lifting. -/

namespace Egglog.Provenance.Generated

open Congruence Congruence.Abstract

private theorem tableRole_uf {P : Program} {f : FnName}
    (h : tableRole P f = some .unionFind) : f = ufName := by
  unfold tableRole at h
  split at h
  · assumption
  · obtain ⟨fk, _, he⟩ := Option.map_eq_some_iff.mp h
    cases he

private theorem tableRole_view {P : Program} {f ctor : FnName}
    (h : tableRole P f = some (.view ctor)) : f = viewName ctor := by
  unfold tableRole at h
  split at h
  · cases h
  · obtain ⟨fk, hf, he⟩ := Option.map_eq_some_iff.mp h
    obtain rfl : fk.1 = ctor := TableRole.view.inj he
    have hname := List.find?_some (p := fun fk : FnName × Nat => viewName fk.1 == f) hf
    exact (beq_iff_eq.mp hname).symm

private theorem columns_eq_take_append {cols : List Term} {k : Nat} {t : Term}
    (hlen : cols.length = k + 1) (ht : cols[k]? = some t) :
    cols = cols.take k ++ [t] := by
  obtain ⟨hbound, he⟩ := List.getElem?_eq_some_iff.mp ht
  have hh := List.take_append_getElem hbound
  rw [he, ← hlen, List.take_length] at hh
  exact hh.symm

/-- A generated fact recognized as a source value is supported by the source model. -/
theorem Fact.value_infers {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) {t : Term}
    (hf : Fact P src.completion t) (hv : t.IsValue src.sig) : src.Infers t t := by
  have hw := (hs.ctorState Database.CtorState.empty hp.ctorsOnly).wf
  have hn := sourceNames_of_programStep hp (fun _ h => h) hs
  obtain ⟨d, hd, ht⟩ := hf
  apply (Database.mem_completion_iff hw).mp
  rcases hd.bound ht with ht | ht
  · exact ht
  · rcases ht with ⟨f, cs, e, rfl, _⟩ | ⟨a, b, rfl, _⟩
    · obtain ⟨dc, hdc, _⟩ := (Term.isValue_app_iff.mp hv).1
      exact (hn _ dc hdc (by
        simp [viewName, String.isPrefixOf, String.startsWith_string_iff,
          String.toList_append])).elim
    · obtain ⟨dc, hdc, _⟩ := (Term.isValue_app_iff.mp hv).1
      exact (hn _ dc hdc (by decide +kernel)).elim

/-- Finite source-sound witnesses justify each branch of the claim mapping. -/
theorem factClaim_infers {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) {C : SourceProof.Context}
    (hC : SourceProof.contextOf P = some C) {t : Term} {claim : SourceProof.Claim}
    (hf : Fact P src.completion t) (hm : Resugar.factClaim P C t = some claim) :
    src.Infers claim.lhs claim.rhs := by
  have hw := (hs.ctorState Database.CtorState.empty hp.ctorsOnly).wf
  have hsig : C.sig = src.sig := (contextOf_signature hC).trans hs.sig.symm
  unfold Resugar.factClaim at hm
  split at hm
  · rename_i hv
    cases Option.some.inj hm
    exact hf.value_infers hp hs (hsig ▸ SourceProof.valueOk_isValue hv)
  · cases t with
    | lit _ => contradiction
    | app f cols =>
      cases hrole : tableRole P f with
      | none => simp [hrole] at hm
      | some role =>
        cases role with
        | unionFind =>
          obtain rfl := tableRole_uf hrole
          simp only [hrole] at hm
          split at hm
          next a b he =>
            cases Option.some.inj hm
            obtain ⟨d, hd, ht⟩ := hf
            exact (Database.cong_completion_iff hw).mp (hd.sound.2 a b ht)
          next => contradiction
        | view ctor =>
          obtain rfl := tableRole_view hrole
          simp only [hrole] at hm
          obtain ⟨dc, _, hm⟩ := Option.bind_eq_some_iff.mp hm
          split at hm
          · contradiction
          · rename_i hlen
            have hlen' : cols.length = dc.arity + 1 := by simpa using hlen
            obtain ⟨e, he, hm⟩ := Option.bind_eq_some_iff.mp hm
            cases Option.some.inj hm
            obtain ⟨d, hd, ht⟩ := hf
            rw [columns_eq_take_append hlen' he] at ht
            exact entrySound_infers hw (hd.sound.1 ctor (cols.take dc.arity) e ht)

/-- An accepted generated certificate implies its mapped source equality directly. -/
theorem check_claim_infers {P : Program} {src : Database} (hp : P.Fragment)
    (hs : ProgramStep Database.empty P src) (hclosed : ∀ R, RunSaturated R src)
    {C : SourceProof.Context} (hC : SourceProof.contextOf P = some C)
    {pf : Proof} {t : Term} {claim : SourceProof.Claim}
    (hc : check (encode P) pf = some t)
    (hm : Resugar.factClaim P C t = some claim) : src.Infers claim.lhs claim.rhs :=
  factClaim_infers hp hs hC (check_fact hp hs hclosed hc) hm

end Egglog.Provenance.Generated
