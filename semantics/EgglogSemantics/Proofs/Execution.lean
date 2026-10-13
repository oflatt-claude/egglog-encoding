import EgglogSemantics.Proofs.Merge

/-! Monotonicity of recorded terms and equations through executable commands and runs. -/

namespace Egglog.FDatabase

theorem execRunRules_terms {R : RulesetName} {d : FDatabase} :
    ∀ t ∈ d.terms, t ∈ (execRunRules R d).terms :=
  execRunRules_induction (P := fun x => ∀ t ∈ d.terms, t ∈ x.terms) (fun _ h => h)
    fun _ _ _ _ hacc _ _ _ t ht => mem_terms_union.mpr (Or.inl (hacc t ht))

theorem runRoundM_terms {R : RulesetName} {d e : FDatabase} (h : d.runRoundM R = some e) :
    ∀ t ∈ d.terms, t ∈ e.terms :=
  fun t ht => mergeSaturateF_terms h t (execRunRules_terms t ht)

theorem runSaturateM_terms {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → ∀ t ∈ d.terms, t ∈ e.terms := by
  intro n
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, -, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact absurd hxe (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact fun t ht => ih hxe t (runRoundM_terms hx t ht)

theorem execCmdM_terms {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    ∀ t ∈ d.terms, t ∈ d'.terms := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun t ht =>
      mergeSaturateF_terms h₂ t ((execAction_lists (h₁)).1 t ht)
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h
  | run R => exact runRoundM_terms hs
  | saturate R => exact runSaturateM_terms _ hs
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h

theorem execProgramM_terms {p : Program} : ∀ {d d' : FDatabase},
    d.execProgramM p = some d' → ∀ t ∈ d.terms, t ∈ d'.terms := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ fun _ h => h
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun t ht => ih h₂ t (execCmdM_terms h₁ t ht)

/-! Retained equations make historical table readings monotone too. -/

theorem mergeSaturateF_eqs {n : Nat} : ∀ {d e : FDatabase},
    d.mergeSaturateF n = some e → ∀ p ∈ d.eqs, p ∈ e.eqs := by
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact fun p hp => hs ▸ hp
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact fun p hp => hs ▸ hp
    · exact fun p hp => ih hs p (mergeRound_confined.2.1 p hp)

theorem execRunRules_eqs {R : RulesetName} {d : FDatabase} :
    ∀ p ∈ d.eqs, p ∈ (execRunRules R d).eqs :=
  execRunRules_induction (P := fun x => ∀ p ∈ d.eqs, p ∈ x.eqs) (fun _ h => h)
    fun _ _ _ _ hacc _ _ _ p hp => mem_eqs_union.mpr (Or.inl (hacc p hp))

theorem runRoundM_eqs {R : RulesetName} {d e : FDatabase} (h : d.runRoundM R = some e) :
    ∀ p ∈ d.eqs, p ∈ e.eqs :=
  fun p hp => mergeSaturateF_eqs h p (execRunRules_eqs p hp)

theorem runSaturateM_eqs {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateM R n = some e → ∀ p ∈ d.eqs, p ∈ e.eqs := by
  intro n
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, -, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact absurd hxe (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.runSaturateM] at hs
    obtain ⟨x, hx, hxe⟩ := Option.bind_eq_some_iff.mp hs
    split at hxe
    · rw [Option.some.injEq] at hxe; exact hxe ▸ fun _ h => h
    · exact fun p hp => ih hxe p (runRoundM_eqs hx p hp)

theorem execCmdM_eqs {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    ∀ p ∈ d.eqs, p ∈ d'.eqs := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun p hp =>
      mergeSaturateF_eqs h₂ p ((execAction_lists (h₁)).2 p hp)
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h
  | run R => exact runRoundM_eqs hs
  | saturate R => exact runSaturateM_eqs _ hs
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ fun _ h => h

theorem execProgramM_eqs {p : Program} : ∀ {d d' : FDatabase},
    d.execProgramM p = some d' → ∀ q ∈ d.eqs, q ∈ d'.eqs := by
  induction p with
  | nil =>
    intro d d' hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact hs ▸ fun _ h => h
  | cons c cs ih =>
    intro d d' hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    exact fun q hq => ih h₂ q (execCmdM_eqs h₁ q hq)

/-- **A block only adds, at the denotation.** `FDatabase.execProgramM_contained` is the
*specification*-relative statement and needs `Program.NoSaturate`; this is the one between the
interpreter's own two states, and it holds of every program. -/
theorem execProgramM_toDatabase_contained {p : Program} {d d' : FDatabase}
    (hs : d.execProgramM p = some d') : d.toDatabase.Contained d'.toDatabase :=
  toDatabase_contained_of_lists (execProgramM_terms hs) (execProgramM_eqs hs)

/-- A round retains every recorded fact even when its merge phase replaces live rows. -/
theorem runRoundM_toDatabase_contained {R : RulesetName} {d e : FDatabase}
    (run : d.runRoundM R = some e) : d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (runRoundM_terms run) (runRoundM_eqs run)

/-- Saturation retains every recorded fact from its initial state. -/
theorem runSaturateM_toDatabase_contained {R : RulesetName} {n : Nat} {d e : FDatabase}
    (run : d.runSaturateM R n = some e) : d.toDatabase.Contained e.toDatabase :=
  toDatabase_contained_of_lists (runSaturateM_terms n run) (runSaturateM_eqs n run)

/-- Every command preserves its input environment. -/
theorem execCmdM_env {d d' : FDatabase} {c : Cmd}
    (hs : d.execCmdM c = some d') : d'.env = d.env := by
  cases c with
  | action a =>
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
      exact (mergeSaturateF_fields h₂).2.1.trans (FDatabase.execAction_env h₁)
  | rule r => cases Option.some.inj hs; rfl
  | run R => exact (runRoundM_fields hs).2.1
  | saturate R => exact (runSaturateM_fields runFuel hs).2.1
  | decl f dc => cases Option.some.inj hs; rfl

/-- Executing a program preserves its initial environment. -/
theorem execProgramM_env {p : Program} {d D : FDatabase}
    (h : d.execProgramM p = some D) : D.env = d.env := by
  induction p generalizing d with
  | nil => cases Option.some.inj h; rfl
  | cons c cs ih =>
      obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      exact (ih h₂).trans (execCmdM_env h₁)

end Egglog.FDatabase

namespace Egglog

/-- A complete nonprimitive atom, which is all a build emits. -/
def Action.IsAtomWrite : Action → Prop
  | .expr (.app f _) => Prim.ofName f = none
  | _ => False

/-- Atom writes evaluate identically under equal signatures and environments. -/
theorem execActions_parallel {as : List Action} (hs : ∀ a ∈ as, a.IsAtomWrite) :
    ∀ {d₁ d₂ e₂ : FDatabase}, d₂.sig = d₁.sig → d₂.env = d₁.env →
      (∀ t ∈ d₁.terms, t ∈ d₂.terms) → execActions d₂ as = some e₂ →
      ∃ e₁, execActions d₁ as = some e₁ ∧ (∀ t ∈ e₁.terms, t ∈ e₂.terms) := by
  induction as with
  | nil =>
    intro d₁ d₂ e₂ _ _ hmem h
    rw [execActions, Option.some.injEq] at h
    exact ⟨d₁, rfl, h ▸ hmem⟩
  | cons a as ih =>
    intro d₁ d₂ e₂ hsig henv hmem h
    cases a with
    | union _ _ => exact (hs _ List.mem_cons_self).elim
    | expr e =>
      obtain ⟨m₂, hm₂, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hm₂
      rw [hsig, henv] at ht
      have hm₁ : execAction d₁ (.expr e) = some (d₁.addAtom t) := by simp [execAction, ht]
      obtain ⟨e₁, he₁, hmem₁⟩ :=
        ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
          (d₁ := d₁.addAtom t) (d₂ := d₂.addAtom t) hsig henv
          (fun u hu => FDatabase.mem_addTerm_terms.mpr
            ((FDatabase.mem_addTerm_terms.mp hu).imp id (hmem u))) hrest
      exact ⟨e₁, by rw [execActions, hm₁, Option.bind_some]; exact he₁, hmem₁⟩

/-- Retained writes of a block survive interleaved top-level merge phases. -/
theorem exists_execActions_of_execProgramM {as : List Action} (hs : ∀ a ∈ as, a.IsAtomWrite) :
    ∀ {d D : FDatabase}, d.execProgramM (as.map Cmd.action) = some D →
      ∃ e, execActions d as = some e ∧ (∀ t ∈ e.terms, t ∈ D.terms) := by
  induction as with
  | nil =>
    intro d D h
    rw [List.map_nil, FDatabase.execProgramM, Option.some.injEq] at h
    exact ⟨d, rfl, h ▸ fun _ ht => ht⟩
  | cons a as ih =>
    intro d D h
    rw [List.map_cons, FDatabase.execProgramM] at h
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [FDatabase.execCmdM] at h₁
    obtain ⟨d₀, hact, hmerge⟩ := Option.bind_eq_some_iff.mp h₁
    replace hact : execAction d a = some d₀ := hact
    obtain ⟨e₁, he₁, hmem₁⟩ := ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h₂
    obtain ⟨hsig, henv, -⟩ := FDatabase.mergeSaturateF_fields hmerge
    obtain ⟨e₀, he₀, hmem₀⟩ :=
      execActions_parallel (fun b hb => hs b (List.mem_cons_of_mem _ hb))
        (d₁ := d₀) (d₂ := d₁) hsig henv (FDatabase.mergeSaturateF_terms hmerge) he₁
    exact ⟨e₀, by rw [execActions, hact, Option.bind_some]; exact he₀,
      fun t ht => hmem₁ t (hmem₀ t ht)⟩


end Egglog
