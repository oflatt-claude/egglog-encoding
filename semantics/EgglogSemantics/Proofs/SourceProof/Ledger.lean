import EgglogSemantics.Proofs.SourceProof.Support

namespace Egglog.SourceProof

open Conservativity

theorem Claim.Supported.addEq_wf {A db : Database} (hA : A.WF) (hw : db.WF)
    {c : Claim} (hc : c.Supported db) : (A.addEq c.lhs c.rhs).WF := by
  refine hA.addEq _ _ (Cong.eq_of_isLit ?_ hc.equality)
  intro p hp hl
  exact (show p ∈ db.eqs ∨ p.1 = p.2 from hp).elim (fun hp => hw.litsIsolated p hp hl) id

def ledger (sig : Signature) : List Claim → Database
  | [] => { Database.empty with sig := sig }
  | c :: cs => (ledger sig cs).addEq c.lhs c.rhs

@[simp] theorem ledger_sig (sig : Signature) (cs : List Claim) : (ledger sig cs).sig = sig := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

@[simp] theorem ledger_env (sig : Signature) (cs : List Claim) : (ledger sig cs).env = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

theorem ledger_contained_completion {db : Database} (hw : db.WF)
    (sig : Signature) {cs : List Claim} (hc : ∀ c ∈ cs, c.Supported db) :
    (ledger sig cs).Contained db.completion := by
  induction cs with
  | nil => exact ⟨by simp [ledger, Database.empty]⟩
  | cons c cs ih =>
      have hclaim := (hc c (by simp)).completion hw
      have htail := ih (fun c h => hc c (by simp [h]))
      refine ⟨?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact (Database.cong_completion_iff hw).mp hclaim
      · rcases hp with hp | ⟨s, hs, rfl⟩
        · rcases hp with hp | ⟨s, hs, rfl⟩
          · exact htail.eqs hp
          · exact hw.completion.eqsRefl s
              (hw.completion.subtermClosed c.lhs hclaim.mem_left hs)
        · exact hw.completion.eqsRefl s
            (hw.completion.subtermClosed c.rhs hclaim.mem_right hs)

theorem ledger_wf {db : Database} (hw : db.WF) (sig : Signature) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Supported db) : (ledger sig cs).WF := by
  induction cs with
  | nil => exact Database.WF.congr Database.WF.empty rfl rfl
  | cons c cs ih =>
      exact (hc c (by simp)).addEq_wf (ih fun c h => hc c (by simp [h])) hw

theorem ledger_holds {sig : Signature} {cs : List Claim} {c : Claim} (hc : c ∈ cs) :
    c.Holds (ledger sig cs) := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Cong.direct (Set.mem_insert _ _)
      · exact (ih hc).mono (Database.Contained.addEq _ _ _)

end Egglog.SourceProof
