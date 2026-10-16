import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Proofs.Congruence.MetadataSyntax

/-! Context signatures depend only on declarations in the program syntax. -/

namespace Egglog.Provenance.Generated

open Congruence SourceProof

private theorem context_step_sig {C D : Context} {c : Cmd}
    (h : Context.step C c = some D) : D.sig = c.sigBind C.sig := by
  cases c with
  | decl f dc =>
      simp only [Context.step] at h
      split at h
      · contradiction
      · cases Option.some.inj h; rfl
  | rule r | run R | saturate R | check q =>
      cases Option.some.inj h; rfl

private theorem context_fold_sig {P : Program} {C D : Context}
    (h : P.foldlM Context.step C = some D) :
    D.sig = P.foldl (fun sig c => c.sigBind sig) C.sig := by
  induction P generalizing C with
  | nil => cases Option.some.inj h; rfl
  | cons c cs ih =>
      obtain ⟨mid, hm, ht⟩ := Option.bind_eq_some_iff.mp h
      rw [List.foldl_cons, ← context_step_sig hm]
      exact ih ht

/-- A successful context fold has exactly the signature installed by its declarations. -/
theorem contextOf_signature {P : Program} {C : Context}
    (h : contextOf P = some C) :
    C.sig = P.foldl (fun sig c => c.sigBind sig) (fun _ => none) :=
  context_fold_sig h

private theorem fold_noDecl {P : Program} (h : ∀ c ∈ P, NoDecl c) (sig : Signature) :
    P.foldl (fun s c => c.sigBind s) sig = sig := by
  induction P generalizing sig with
  | nil => rfl
  | cons c cs ih =>
      rw [List.foldl_cons, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
      have hc := h c List.mem_cons_self
      cases c <;> first | rfl | contradiction

/-- The encoded command suffix installs no declarations after the prelude. -/
theorem contextOf_encode_sig {P : Program} {C : Context}
    (h : contextOf (encode P) = some C) : C.sig = encodeSig P := by
  rw [contextOf_signature h, encode, compile, List.map_append, List.foldl_append]
  exact fold_noDecl (cmds_noDecl P 0) _

end Egglog.Provenance.Generated
