import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.Rules

namespace Egglog.Provenance

theorem actionFacts_sound {db : Database} {a : Action} {fs : List Term}
    (h : actionFacts db.sig db.env a = some fs) :
    ∃ d, evalAction db a = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  cases a with
  | union _ _ => simp [actionFacts] at h
  | expr e =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases Option.some.inj h
      refine ⟨db.addTerm t, by simp [evalAction, ht], ?_⟩
      intro s hs
      exact Cong.assert (Or.inr ⟨s, (Term.mem_subtermList t).mp hs, rfl⟩)
    · contradiction

theorem actionsFacts_sound {db : Database} {as : List Action} {fs : List Term}
    (h : actionsFacts db.sig db.env as = some fs) :
    ∃ d, evalActions db as = some d ∧ ∀ t ∈ fs, t ∈ d.terms := by
  induction as generalizing db fs with
  | nil => cases Option.some.inj h; exact ⟨db, rfl, by simp⟩
  | cons a as ih =>
    obtain ⟨first, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hr, heq⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj heq
    obtain ⟨d₁, hd₁, hm₁⟩ := actionFacts_sound hf
    have hr' : actionsFacts d₁.sig d₁.env as = some rest := by
      rw [evalAction_sig hd₁, evalAction_env hd₁]; exact hr
    obtain ⟨d₂, hd₂, hm₂⟩ := ih hr'
    refine ⟨d₂, by simp [evalActions, hd₁, hd₂], ?_⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (evalActions_contained hd₂).terms (hm₁ t ht)
    · exact hm₂ t ht

/-- A fact premise is a complete atom, so it is matched by `Expr.evalAtom` rather than by
the source checker's `Expr.eval`; an equality premise is the source checker's. -/
theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {t : Term}
    (ht : t ∈ db.terms) (h : premiseMatches db.sig σ p t = true) : Matches db p σ := by
  cases p with
  | expr e =>
    simp only [premiseMatches, beq_iff_eq] at h
    exact .expr ht h (Cong.mono (Database.Contained.addTerms _ _) ht)
  | eq a b =>
    apply SourceProof.premiseMatches_sound (c := ⟨t, t⟩) ht
    simpa [premiseMatches, SourceProof.premiseMatches] using h

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {ts : List Term}
    (ht : ∀ t ∈ ts, t ∈ db.terms) (h : premisesMatch db.sig σ q ts = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing ts with
  | nil => simp
  | cons p ps ih =>
    cases ts with
    | nil => simp [premisesMatch] at h
    | cons t ts =>
      simp only [premisesMatch, Bool.and_eq_true_iff] at h
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact premiseMatches_sound (ht t (by simp)) h.1
      · exact ih (fun t ht' => ht t (by simp [ht'])) h.2 p' hp'

theorem ruleFacts_sound {P : Program} {db : Database}
    (hs : ProgramStep Database.empty P db) (hw : db.WF)
    (hclosed : ∀ R, RunSaturated R db) {r : Rule} (hr : Cmd.rule r ∈ P)
    {σ : Env} {premises fs : List Term} (hp : ∀ t ∈ premises, t ∈ db.terms)
    (hf : ruleFacts db.sig r σ premises = some fs) : ∀ t ∈ fs, t ∈ db.terms := by
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    have hval : ∀ b ∈ σ, b.2 ∈ db.terms := by
      intro b hb
      obtain ⟨p, hpm, hsub⟩ := List.any_eq_true.mp (hchecks.1.2 b hb).2
      exact hw.subtermClosed p (hp p hpm) ((Term.mem_subtermList p).mp (of_decide_eq_true hsub))
    obtain ⟨τ, hτ, hag⟩ := SourceProof.querySubst_of_matches hchecks.1.1 hval
      (premisesMatch_sound hp hchecks.2)
    obtain ⟨d, hd, hfs⟩ := actionsFacts_sound (db := { db with env := σ }) hf
    let post : Database := { d with env := db.env, rules := db.rules }
    have henv : db.env = [] := hs.env
    have hlocal : evalLocalActions db r.actions σ = some post := by
      simp only [evalLocalActions, henv, List.append_nil, hd, Option.map_some]
      simp only [post, henv]
    have hresult : post ∈ RuleResults db r :=
      ⟨τ, hτ, by rw [evalLocalActions_agree _ hag]; exact hlocal⟩
    have hpost : post.Contained db := (runRules_eq_self_iff r.ruleset db).mp
      (hclosed r.ruleset).1 r ((hs.mem_rules_iff r).mpr (Or.inr hr)) rfl post hresult
    have hdpost : d.Contained post := ⟨fun _ h => h⟩
    exact fun t ht => hpost.terms (hdpost.terms (hfs t ht))
  · contradiction

theorem conflicts_sound {d : FnDecl} {body : List Action} {old new : List Term}
    (h : conflicts d body old new = true) : MergeConflict d body old new := by
  unfold conflicts at h
  unfold MergeConflict
  cases hw : d.unchangedWidth body <;> simp_all

theorem mergeFacts_sound {db : Database} (hw : db.WF) (hclosed : MergeSaturated db)
    {f : FnName} {old new : Term} {fs : MergeFacts}
    (ho : old ∈ db.terms) (hn : new ∈ db.terms)
    (hf : mergeFacts db.sig f old new = some fs) :
    ∀ t, t ∈ fs.body ∨ t ∈ fs.result.subtermList → t ∈ db.terms := by
  unfold mergeFacts at hf
  obtain ⟨d, hd, hdecl⟩ := Option.bind_eq_some_iff.mp hf
  cases hm : d.merge with
  | none => simp [hm] at hdecl
  | some ms =>
    cases ms with
    | merge oldVars newVars body res =>
      simp only [hm] at hdecl
      cases old with
      | lit _ => simp at hdecl
      | app ofn oc =>
        cases new with
        | lit _ => simp at hdecl
        | app nfn nc =>
          simp only at hdecl
          split at hdecl
          · rename_i hcols
            simp only [Bool.and_eq_true_iff, beq_iff_eq] at hcols
            obtain ⟨⟨⟨⟨hfo, hfn⟩, hoc⟩, hnc⟩, hkeys⟩ := hcols
            subst ofn
            subst nfn
            split at hdecl
            · rename_i hconf
              obtain ⟨facts, hbody, hafterBody⟩ := Option.bind_eq_some_iff.mp hdecl
              obtain ⟨vs, hres, hafterRes⟩ := Option.bind_eq_some_iff.mp hafterBody
              split at hafterRes
              · cases Option.some.inj hafterRes
                have hc := conflicts_sound hconf
                have hol : (oc.take d.arity).length = d.arity := by
                  simp only [FnDecl.entryWidth, hm, Option.isNone_some, Bool.false_eq_true,
                    if_false] at hoc
                  rw [List.length_take, Nat.min_eq_left (by omega)]
                have hnl : (nc.take d.arity).length = d.arity := by
                  rw [← hkeys]; exact hol
                have hkeymem : ∀ t ∈ oc.take d.arity, t ∈ db.terms := by
                  intro t ht
                  exact hw.subtermClosed _ ho (Term.arg_subterms
                    (List.mem_of_mem_take ht) (Term.self_mem_subterms t))
                have hk : CongList db (oc.take d.arity) (nc.take d.arity) := by
                  rw [← hkeys]; exact CongList.refl hkeymem
                obtain ⟨D, hD, hfs⟩ := actionsFacts_sound
                  (db :=
                    { db with env := mergeEnv oldVars newVars (oc.drop d.arity) (nc.drop d.arity) }) hbody
                have hv : Expr.evalList D.sig res D.env = some vs := by
                  rw [evalActions_sig hD, evalActions_env hD]; exact hres
                let post : Database :=
                  { D.addTerm (.app f (oc.take d.arity ++ vs)) with
                    env := db.env, rules := db.rules }
                have hstep : MergeStep db post := .collide hd hm hc hol hnl
                  (by simpa only [List.take_append_drop] using ho)
                  (by simpa only [List.take_append_drop] using hn) hk hD hv
                have hpost : post = db := hclosed post hstep
                intro t ht
                rw [← hpost]
                rcases ht with ht | ht
                · have hcont : D.Contained post := (Database.Contained.addTerm _ D).trans
                    (show (D.addTerm (.app f (oc.take d.arity ++ vs))).Contained post from
                      ⟨fun _ h => h⟩)
                  exact hcont.terms (hfs t ht)
                · exact Cong.assert (Or.inr ⟨t,
                    (Term.mem_subtermList _).mp ht, rfl⟩)
              · contradiction
            · contradiction
          · contradiction

end Egglog.Provenance
