import EgglogSemantics.Provenance.Checker

namespace Egglog.Provenance

/-- A semantic interpretation closed under the checker's certificate rules. This does
not assert that certified facts are current rows in an execution endpoint. -/
structure Model (P : Program) (sig : Signature) (H : Term → Prop) : Prop where
  ruleFacts : ∀ {r : Rule} {σ : Env} {premises fs : List Term},
    Cmd.rule r ∈ P → (∀ t ∈ premises, H t ∧ SourceProof.atomOk sig t = true) →
      Egglog.Provenance.ruleFacts sig r σ premises = some fs → ∀ t ∈ fs, H t
  mergeFacts : ∀ {f : FnName} {old new : Term} {fs : MergeFacts},
    H old ∧ SourceProof.atomOk sig old = true →
    H new ∧ SourceProof.atomOk sig new = true →
    Egglog.Provenance.mergeFacts sig f old new = some fs →
      ∀ t, t ∈ fs.body ∨ t ∈ fs.result.subtermList → H t
  subterms : ∀ {parent : Term}, H parent ∧ SourceProof.atomOk sig parent = true →
    ∀ t ∈ parent.subtermList, H t

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

/-- Each accepted node preserves the chosen model and its syntactic atom check. -/
theorem checkNode_sound_in_model {P : Program} {C : SourceProof.Context} {H : Term → Prop}
    (model : Model P C.sig H) {pf : Proof}
    (hp : ∀ q ∈ pf.subproofs, H q.fact ∧ SourceProof.atomOk C.sig q.fact = true)
    (h : checkNode P C pf = true) : H pf.fact ∧ SourceProof.atomOk C.sig pf.fact = true := by
  have hchecks : SourceProof.atomOk C.sig pf.fact = true ∧
      checkReason P C.sig pf = true := by
    exact Bool.and_eq_true_iff.mp h
  refine ⟨?_, hchecks.1⟩
  have hr := hchecks.2
  cases pf with
  | rule t i σ ps =>
      simp only [checkReason] at hr
      obtain ⟨cmd, hcmd, hr⟩ := Option.bind_eq_some_iff.mp (option_true hr)
      cases cmd with
      | rule r =>
          obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp hr
          refine model.ruleFacts (List.mem_of_getElem? hcmd) ?_ hfs t (by simpa using hr)
          intro u hu
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
          exact hp q hq
      | run _ | saturate _ | decl _ _ | check _ => simp at hr
  | merge t f old new =>
      simp only [checkReason] at hr
      obtain ⟨fs, hfs, hr⟩ := Option.bind_eq_some_iff.mp (option_true hr)
      exact model.mergeFacts (hp old (by simp [Proof.subproofs]))
        (hp new (by simp [Proof.subproofs])) hfs t (by simpa using hr)
  | subterm t parent =>
      simp only [checkReason, decide_eq_true_eq] at hr
      exact model.subterms (hp parent (by simp [Proof.subproofs])) t hr

mutual

theorem valid_sound_in_model {P : Program} {C : SourceProof.Context} {H : Term → Prop}
    (model : Model P C.sig H) : (pf : Proof) → valid P C pf = true →
      H pf.fact ∧ SourceProof.atomOk C.sig pf.fact = true
  | .rule t i σ ps, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      exact checkNode_sound_in_model model (allValid_sound_in_model model ps h.1) h.2
  | .merge t f p q, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ihp := valid_sound_in_model model p h.1.1
      have ihq := valid_sound_in_model model q h.1.2
      refine checkNode_sound_in_model model ?_ h.2
      intro r hr
      simp only [Proof.subproofs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ihp
      · exact ihq
  | .subterm t p, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ih := valid_sound_in_model model p h.1
      refine checkNode_sound_in_model model ?_ h.2
      intro q hq
      simp only [Proof.subproofs, List.mem_singleton] at hq
      subst hq
      exact ih
termination_by structural pf => pf

theorem allValid_sound_in_model {P : Program} {C : SourceProof.Context} {H : Term → Prop}
    (model : Model P C.sig H) : (ps : List Proof) → allValid P C ps = true →
      ∀ q ∈ ps, H q.fact ∧ SourceProof.atomOk C.sig q.fact = true
  | [], _, _, hq => by simp at hq
  | p :: ps, h, q, hq => by
      simp only [allValid, Bool.and_eq_true_iff] at h
      rcases List.mem_cons.mp hq with hqp | hq
      · rw [hqp]
        exact valid_sound_in_model model p h.1
      · exact allValid_sound_in_model model ps h.2 q hq
termination_by structural ps => ps

end

/-- Successful checking establishes model-relative meaning and atom validity. -/
theorem check_sound_and_atom_in_model {P : Program} {C : SourceProof.Context}
    {sig : Signature} {H : Term → Prop} {pf : Proof} {t : Term}
    (model : Model P sig H) (hC : SourceProof.contextOf P = some C) (hsig : C.sig = sig)
    (h : check P pf = some t) : H t ∧ SourceProof.atomOk sig t = true := by
  have model' : Model P C.sig H := hsig.symm ▸ model
  unfold check at h
  split at h
  · contradiction
  · simp only [hC, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hv
      cases Option.some.inj h
      simpa only [hsig] using valid_sound_in_model model' pf hv
    · contradiction

/-- Checker soundness relative to an explicitly supplied semantic model. -/
theorem check_sound_in_model {P : Program} {C : SourceProof.Context}
    {sig : Signature} {H : Term → Prop} {pf : Proof} {t : Term}
    (model : Model P sig H) (hC : SourceProof.contextOf P = some C) (hsig : C.sig = sig)
    (h : check P pf = some t) : H t :=
  (check_sound_and_atom_in_model model hC hsig h).1

end Egglog.Provenance
