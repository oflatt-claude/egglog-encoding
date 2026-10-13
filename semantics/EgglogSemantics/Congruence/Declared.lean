import EgglogSemantics.Congruence.Execution
import EgglogSemantics.Encoding.SourceArity
import EgglogSemantics.Proofs.Signature

/-! Exact declarations installed by the congruence prelude. -/

namespace Egglog.Congruence

/-- The prelude installs all declarations before any data is written. -/
def encodeSig (P : Program) : Signature :=
  ((encodePrelude P).map Command.command).foldl (fun s c => c.sigBind s) (fun _ => none)

private theorem maintenance_rule (P : Program) :
    ∀ c ∈ maintenanceRules P, ∃ r, c.command = .rule r := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · exact ⟨_, rfl⟩
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> exact ⟨_, rfl⟩

private theorem allMaintenance_rule (P : Program) :
    ∀ c ∈ allMaintenanceRules P, ∃ r, c.command = .rule r := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_rule P c hc
  · obtain ⟨r, hr⟩ := maintenance_rule P c hc
    simp [inRuleset, hr]

private theorem prelude_decl_iff {P : Program} {f : FnName} {dc : FnDecl} :
    Cmd.decl f dc ∈ (encodePrelude P).map Command.command ↔
      (f = ufName ∧ dc = tableDecl 1) ∨ ∃ g k, (g, k) ∈ P.ctors ∧
        ((f = g ∧ dc = skolemDecl k) ∨ (f = viewName g ∧ dc = tableDecl k)) := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := List.mem_map.mp h
    simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | ⟨⟨g, k⟩, hg, hc⟩) | hc
    · exact Or.inl (by simpa using he.symm)
    · refine Or.inr ⟨g, k, hg, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (by simpa using he.symm)
    · obtain ⟨r, hr⟩ := allMaintenance_rule P c hc
      rw [hr] at he
      cases he
  · intro h
    apply List.mem_map.mpr
    rcases h with ⟨rfl, rfl⟩ | ⟨g, k, hg, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, rfl⟩
    · refine ⟨⟨.decl f (skolemDecl k), none⟩,
        List.mem_append_left _ (List.mem_cons_of_mem _ ?_), rfl⟩
      exact List.mem_flatMap.mpr ⟨(f, k), hg, List.mem_cons_self⟩
    · refine ⟨⟨.decl (viewName g) (tableDecl k), none⟩,
        List.mem_append_left _ (List.mem_cons_of_mem _ ?_), rfl⟩
      exact List.mem_flatMap.mpr ⟨(g, k), hg, by simp⟩

private theorem source_ne_view {P : Program} (hdom : P.EncodeDomain)
    {f : FnName} {k : Nat} (hf : (f, k) ∈ P.ctors) (g : FnName) : f ≠ viewName g := by
  intro he
  exact noAt_of_mem_ctors hdom hf (he ▸ (by simp [viewName, String.isPrefixOf]))

private theorem source_ne_uf {P : Program} (hdom : P.EncodeDomain)
    {f : FnName} {k : Nat} (hf : (f, k) ∈ P.ctors) : f ≠ ufName := by
  intro he
  exact noAt_of_mem_ctors hdom hf (he ▸ (by decide +kernel : "@".isPrefixOf ufName = true))

/-- The generated union-find declaration cannot be shadowed by source names or views. -/
theorem encodeSig_ufName {P : Program} (hdom : P.EncodeDomain) :
    encodeSig P ufName = some (tableDecl 1) := by
  apply foldl_sigBind_found _ (prelude_decl_iff.mpr (Or.inl ⟨rfl, rfl⟩))
  intro dc hd
  rcases prelude_decl_iff.mp hd with ⟨_, hd⟩ | ⟨g, k, hg, (⟨he, _⟩ | ⟨he, _⟩)⟩
  · exact hd
  · exact False.elim (source_ne_uf hdom hg he.symm)
  · exact False.elim (viewName_ne_ufName he.symm)

/-- Every source constructor keeps its structural id constructor and gains its view. -/
theorem encodeSig_tables {P : Program} (hdom : P.EncodeDomain) {f : FnName} {k : Nat}
    (hf : (f, k) ∈ P.ctors) :
    encodeSig P f = some (skolemDecl k) ∧
      encodeSig P (viewName f) = some (tableDecl k) := by
  constructor
  · apply foldl_sigBind_found _
      (prelude_decl_iff.mpr (Or.inr ⟨f, k, hf, Or.inl ⟨rfl, rfl⟩⟩))
    intro dc hd
    rcases prelude_decl_iff.mp hd with ⟨he, _⟩ | ⟨g, l, hg, (⟨he, hd⟩ | ⟨he, _⟩)⟩
    · exact False.elim (source_ne_uf hdom hf he)
    · exact hd.trans (congrArg skolemDecl (hdom.aritiesAgree' (g, l) hg (f, k) hf he.symm))
    · exact False.elim (source_ne_view hdom hf g he)
  · apply foldl_sigBind_found _
      (prelude_decl_iff.mpr (Or.inr ⟨f, k, hf, Or.inr ⟨rfl, rfl⟩⟩))
    intro dc hd
    rcases prelude_decl_iff.mp hd with ⟨he, _⟩ | ⟨g, l, hg, (⟨he, _⟩ | ⟨he, hd⟩)⟩
    · exact False.elim (viewName_ne_ufName he)
    · exact False.elim (source_ne_view hdom hg f he.symm)
    · exact hd.trans
        (congrArg tableDecl (hdom.aritiesAgree' (g, l) hg (f, k) hf (viewName_inj he).symm))

/-- All commands following the prelude preserve its signature. -/
theorem execProgram_sig_of_noDecl {p : Program} (hp : ∀ c ∈ p, NoDecl c) :
    ∀ {d e : FDatabase}, d.execProgramM p = some e → e.sig = d.sig := by
  induction p with
  | nil => intro d e h; exact Option.some.inj h ▸ rfl
  | cons c cs ih =>
      intro d e h
      obtain ⟨m, hm, he⟩ := Option.bind_eq_some_iff.mp h
      rw [ih (fun c' hc' => hp c' (List.mem_cons_of_mem c hc')) he,
        FDatabase.execCmdM_sig hm]
      have hc := hp c List.mem_cons_self
      cases c <;> first | rfl | contradiction

theorem execM_encode_sig {P : Program} {d : FDatabase}
    (h : execM (encode P) = some d) : d.sig = encodeSig P := by
  change FDatabase.empty.execProgramM _ = some d at h
  rw [encode, compile, List.map_append] at h
  obtain ⟨m, hm, hd⟩ := FDatabase.execProgramM_append h
  rw [execProgram_sig_of_noDecl (cmds_noDecl P 0) hd]
  exact Egglog.FDatabase.execProgramM_sig hm

/-- Every constructor available in a source prefix has an id constructor in the target. -/
theorem sourceConstructors_of_programStep {P p : Program} (hdom : P.EncodeDomain)
    (hp : ∀ c ∈ p, c ∈ P) {src : Database} (hsrc : ProgramStep Database.empty p src)
    {sig : Signature} (hsig : sig = encodeSig P) :
    ∀ f, src.sig.IsCtor f → sig.IsCtor f := by
  intro f hf
  obtain ⟨dc, hd, _⟩ := hf
  rcases hsrc.declared hd with he | hc
  · cases he
  · have hk : (f, dc.arity) ∈ P.ctors := List.mem_dedup.mpr
      (List.mem_flatMap.mpr ⟨.decl f dc, hp _ hc, by simp [Cmd.ctors]⟩)
    exact ⟨skolemDecl dc.arity, hsig ▸ (encodeSig_tables hdom hk).1, rfl⟩

end Egglog.Congruence
