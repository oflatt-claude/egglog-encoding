import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.Congruence.AbstractWrites
import EgglogSemantics.Proofs.Congruence.AbstractMerge

/-! Source-justified writes remain sound across the merge after every command. -/

namespace Egglog.Congruence.Live

open Abstract

theorem sourceWrites_program_preserves {src d e : Database} {as : List Action}
    (hw : src.WF) (hsafe : SourceSafe src) (h : Runtime d)
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) (hd : Descending d)
    (hwrites : SourceWrites src d.sig d.env as)
    (hr : ProgramStep d (as.map Cmd.action) e) :
    Runtime e ∧ SoundTerms e src ∧ Descending e := by
  induction as generalizing d with
  | nil => obtain rfl := hr.nil_inv; exact ⟨h, hs, hd⟩
  | cons a as ih =>
      obtain ⟨ea, t, rfl, hev, ht⟩ := hwrites a List.mem_cons_self
      obtain ⟨mid, hcmd, hrest⟩ := hr.cons_inv
      obtain ⟨raw, hraw, hm⟩ := hcmd
      have heval : evalAction d (.expr ea) = some (d.addTerm t) := by
        simp [evalAction, hev]
      obtain rfl : raw = d.addTerm t := Option.some.inj (hraw.symm.trans heval)
      have hrawstate := h.action (by trivial) heval
      obtain ⟨hsraw, hdraw⟩ := sourceAtom_preserves hw hsafe hs hd ht
      have hmid := hrawstate.merge hm.1
      have hsmid := mergeClosure_soundTerms (d := d.addTerm t) hshape hrawstate.noUnions.diag
        hrawstate.wf hrawstate.storeOk hrawstate.state.uf hsraw hm.1
      have hdmid := mergeClosure_descending (d := d.addTerm t) hshape hrawstate.noUnions.diag
        hrawstate.wf hrawstate.storeOk hrawstate.state.uf hdraw hm.1
      have hsig : mid.sig = d.sig := hm.1.sig
      have henv : mid.env = d.env := hm.1.envRules.1
      apply ih hmid (by rw [hsig]; exact hshape) hsmid hdmid _ hrest
      rw [hsig, henv]
      exact fun a ha => hwrites a (List.mem_cons_of_mem _ ha)

/-- Checked generated states can always finish the finite list of individual writes. -/
theorem sourceWrites_program_exists {src d : Database} {as : List Action}
    (h : Runtime d) (hwrites : SourceWrites src d.sig d.env as) :
    ∃ e, ProgramStep d (as.map Cmd.action) e := by
  induction as generalizing d with
  | nil => exact ⟨d, .nil⟩
  | cons a as ih =>
      obtain ⟨ea, t, rfl, hev, _⟩ := hwrites a List.mem_cons_self
      have heval : evalAction d (.expr ea) = some (d.addTerm t) := by
        simp [evalAction, hev]
      have hraw := h.action (by trivial) heval
      obtain ⟨mid, hm⟩ := normalize_exists hraw.state
      have hmid := hraw.merge hm.1
      have hsig : mid.sig = d.sig := hm.1.sig
      have henv : mid.env = d.env := hm.1.envRules.1
      have htail : SourceWrites src mid.sig mid.env as := by
        rw [hsig, henv]
        exact fun a ha => hwrites a (List.mem_cons_of_mem _ ha)
      obtain ⟨e, he⟩ := ih hmid htail
      exact ⟨e, .cons ⟨d.addTerm t, heval, hm⟩ he⟩

end Egglog.Congruence.Live
