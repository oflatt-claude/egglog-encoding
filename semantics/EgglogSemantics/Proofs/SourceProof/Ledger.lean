import EgglogSemantics.Proofs.SourceProof.Support

namespace Egglog.SourceProof

open Conservativity

private theorem pin {db : Database} (hw : db.WF) {s u : Term} {ts : List Term}
    (hu : u ∈ db.terms) (hs : s ∈ ts) (h : Cong (ambient db) s u) :
    CongOn db ts s u :=
  Cong.mono ⟨withOperands_mono_list (by simpa using hs)⟩
    (cong_pin hw.subtermClosed (fun _ hp => mem_amb_eqs hp) hu h)

theorem Supports.record {A db : Database} (hr : A.Recorded db) (hw : db.WF)
    {t : Term} (ht : Supports db t) : (A.addTerm t).Recorded db := by
  refine ⟨fun p hp => ?_⟩
  rcases hp with hp | ⟨s, hs, rfl⟩
  · exact hr.eqs p hp
  · obtain ⟨u, hu, hsu⟩ := ht s hs
    have hc : CongOn db [s, s] s u := pin hw hu (by simp) hsu
    exact ⟨(u, u), hw.eqsRefl u hu, hc, hc⟩

theorem Claim.Supported.record {A db : Database} (hr : A.Recorded db) (hw : db.WF)
    {c : Claim} (hc : c.Supported db) : (A.addEq c.lhs c.rhs).Recorded db := by
  have hterms := hc.rhs.record (hc.lhs.record hr hw) hw
  refine ⟨fun p hp => ?_⟩
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · obtain ⟨u, hu, hlu⟩ := hc.lhs c.lhs (Term.self_mem_subterms _)
    exact ⟨(u, u), hw.eqsRefl u hu, pin hw hu (by simp) hlu,
      pin hw hu (by simp) (hc.equality.symm.trans hlu)⟩
  · exact hterms.eqs p hp

theorem Claim.Supported.addEq_wf {A db : Database} (hA : A.WF) (hw : db.WF)
    {c : Claim} (hc : c.Supported db) : (A.addEq c.lhs c.rhs).WF := by
  refine hA.addEq _ _ (Cong.eq_of_isLit ?_ hc.equality)
  intro p hp hl
  exact (mem_amb_eqs hp).elim (fun hp => hw.litsIsolated p hp hl) id

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

theorem ledger_recorded {db : Database} (hw : db.WF) (sig : Signature) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Supported db) : (ledger sig cs).Recorded db := by
  induction cs with
  | nil => exact ⟨by simp [ledger, Database.empty]⟩
  | cons c cs ih =>
      exact (hc c (by simp)).record (ih fun c h => hc c (by simp [h])) hw

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
      · exact Cong.assert (Set.mem_insert _ _)
      · exact (ih hc).mono (Database.Contained.addEq _ _ _)

end Egglog.SourceProof
