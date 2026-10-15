import EgglogSemantics.Proofs.Congruence.AbstractBoundary
import EgglogSemantics.Proofs.Congruence.SourceSetup

/-! Boundary preservation for source declarations, rule registrations, and checks. -/

namespace Egglog.Congruence.Abstract

/-- A source declaration is already hoisted into the target prelude. -/
theorem Boundary.decl {src post d e : Database} (h : Boundary src d)
    (hcs : src.sig.AllConstructors) {f : FnName} {dc : FnDecl}
    (hdecl : (Cmd.decl f dc).CtorDecl) (hs : CmdStep src (.decl f dc) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.decl f dc)).map Command.command) e) :
    Boundary post e := by
  obtain rfl := ht.nil_inv
  have heq := source_setup_eqs hcs (c := .decl f dc) trivial hdecl hs
  exact ⟨h.sound.mono_src hs.contained.eqs, h.descend,
    h.reads.restrict ⟨heq.subset⟩, h.saturated⟩

/-- Registering a source rule preserves data and the dedicated maintenance fixed point.
Its compiled counterpart is outside the reserved rebuilding ruleset. -/
theorem Boundary.rule {src post d e : Database} (h : Boundary src d)
    (hcs : src.sig.AllConstructors) {r : Rule} (hR : r.ruleset ≠ rebuildRuleset)
    (hs : CmdStep src (.rule r) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.rule r)).map Command.command) e) :
    Boundary post e := by
  change ProgramStep d [.rule (encodeRule r)] e at ht
  obtain ⟨m, hm, hnil⟩ := ht.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨n, hn, hcl⟩ := hm.reach
  change n = { d with rules := insert (encodeRule r) d.rules } at hn
  subst n
  have hsat := runSaturated_addRule h.saturated (r := encodeRule r) hR
  rw [hcl.eq_of_mergeNormal hsat.2]
  have heq := source_setup_eqs hcs (c := .rule r) trivial trivial hs
  refine ⟨?_, ?_, ?_, hsat⟩
  · exact (h.sound.mono_src hs.contained.eqs).congr_terms Database.terms_setRules
  · exact h.descend.mono_terms Database.terms_setRules.subset
  · exact (h.reads.restrict (src' := post) ⟨heq.subset⟩).mono ⟨Set.Subset.refl _⟩

/-- Paired successful checks leave the boundary relation unchanged. Their possible
failure is handled separately by the check-observation theorem. -/
theorem Boundary.check {src post d e : Database} (h : Boundary src d) {q : Query}
    (hs : CmdStep src (.check q) post) {i : Nat}
    (ht : ProgramStep d ((encodeCmd i (.check q)).map Command.command) e) :
    Boundary post e := by
  obtain ⟨_, rfl⟩ := hs
  change ProgramStep d [.check (encodeQuery q 0).1] e at ht
  obtain ⟨m, hm, hnil⟩ := ht.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨_, rfl⟩ := hm
  exact h

end Egglog.Congruence.Abstract
