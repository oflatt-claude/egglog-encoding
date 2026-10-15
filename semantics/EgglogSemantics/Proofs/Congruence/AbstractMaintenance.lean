import EgglogSemantics.Proofs.Congruence.AbstractForward
import EgglogSemantics.Proofs.Congruence.RebuildSubst

/-! The generated rules and merge body establish the abstract rebuilding closure. -/

namespace Egglog.Congruence.Abstract

theorem Matches.bound {d : Database} {p : Pattern} {ρ : Env} (hm : Matches d p ρ)
    {v : Var} (hv : v ∈ p.vars) : (Env.lookup v ρ).isSome := by
  cases hm with
  | @expr e _ _ _ _ he _ =>
      cases e with
      | app f es =>
          obtain ⟨ts, he, _⟩ := Expr.evalAtom_app_inv he
          exact Expr.lookup_isSome_of_mem_varsList he hv
      | lit _ | var _ | min _ _ => exact Expr.lookup_isSome_of_mem_vars he hv
  | eq _ ha hb _ _ =>
      rcases List.mem_union_iff.mp hv with hv | hv
      · exact Expr.lookup_isSome_of_mem_vars ha hv
      · exact Expr.lookup_isSome_of_mem_vars hb hv

/-- A fixed point contains each instantiated head, using an actual valid query
substitution and local action evaluation. -/
theorem atom_rule_closed {d : Database} {R : RulesetName} (hfix : RunRules R d = d)
    {r : Rule} (hr : r ∈ d.rules) (hR : r.ruleset = R) {ρ : Env}
    (hval : ∀ b ∈ ρ, b.2 ∈ d.terms) (hnames : ∀ b ∈ ρ, b.1 ∈ Query.vars r.query)
    (hq : ∀ p ∈ r.query, Matches d p ρ) {f : FnName} {es : List Expr} {ts : List Term}
    (hhead : r.actions = [.expr (.app f es)]) (hf : (d.sig f).isSome = true)
    (he : Expr.evalList d.sig es ρ = some ts) : Term.app f ts ∈ d.terms := by
  have hbound : ∀ v ∈ Query.vars r.query, ∃ t, Env.lookup v ρ = some t ∧ t ∈ d.terms := by
    intro v hv
    obtain ⟨p, hp, hv⟩ := Query.mem_vars.mp hv
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Matches.bound (hq p hp) hv)
    exact ⟨t, ht, hval (v, t) (Env.mem_of_lookup ht)⟩
  obtain ⟨σ, hσ, hag⟩ := validQuerySubst_of_matches hbound hq
  have heσ : Expr.evalList d.sig es σ = some ts := by
    rw [Expr.evalList_agreeOn es (fun v hv => ?_)]
    · exact he
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (Expr.lookup_isSome_of_mem_varsList he hv)
    exact hag v (hnames (v, t) (Env.mem_of_lookup ht))
  let post := d.addTerm (.app f ts)
  have hpost : evalLocalActions d r.actions σ = some post := by
    rw [hhead]
    have hev := Expr.evalList_append_env (τ := d.env) es heσ
    simp only [evalLocalActions, evalActions, evalAction, Expr.evalAtom, hf,
      ite_true, hev, Option.map_some, Option.bind_some]
    rfl
  exact ((runRules_eq_self_iff R d).mp hfix r hr hR post ⟨σ, hσ, hpost⟩).terms
    (Database.mem_addTerm _ _)

/-- Generated table collisions join both outputs in the mathematical merge fixed point. -/
theorem merge_join {d : Database} (hd : d.Diag) (hw : d.WF) (hsat : MergeNormal d)
    (hu : d.sig ufName = some (tableDecl 1)) {f : FnName} {cs : List Term} {a b : Term}
    (hf : d.sig f = some (tableDecl cs.length))
    (ha : d.Out f cs [a]) (hb : d.Out f cs [b]) :
    ∃ e, Parent d a e ∧ Parent d b e := by
  by_cases hab : a = b
  · exact ⟨a, .refl d a, Or.inl hab.symm⟩
  let e := Term.least a b
  let init := { d with env := mergeEnv ["old"] ["new"] [a] [b] }
  let body := (init.addTerm (.app ufName [a, e])).addTerm (.app ufName [b, e])
  let post := { body.addTerm (.app f (cs ++ [e])) with env := d.env, rules := d.rules }
  have heval : evalActions init mergeBody = some body := by
    simp [init, body, e, mergeBody, mergeEnv, evalActions, evalAction, Expr.evalAtom,
      Expr.evalList, Expr.eval, Env.lookup, hu]
  have hres : Expr.evalList body.sig mergeResult body.env = some [e] := by
    simp [body, init, mergeResult, mergeEnv, Expr.evalList, Expr.eval, Env.lookup,
      e]
  have hstep : MergeStep d post := .collide hf rfl
    (by simpa [MergeConflict, FnDecl.unchangedWidth, tableDecl, mergeBody] using hab)
    rfl rfl (ha.term hd) (hb.term hd)
    (CongList.refl fun t ht => ha.columns hw t (List.mem_append_left _ ht)) heval hres
  have heq := hsat post hstep
  have hrowa : Term.app ufName [a, e] ∈ d.terms := by
    rw [← heq]
    rw [show post.terms = (body.addTerm (.app f (cs ++ [e]))).terms from
      Database.terms_setEnvRules]
    apply (Database.Contained.addTerm _ _).terms
    apply (Database.Contained.addTerm _ _).terms
    exact Database.mem_addTerm _ _
  have hrowb : Term.app ufName [b, e] ∈ d.terms := by
    rw [← heq]
    rw [show post.terms = (body.addTerm (.app f (cs ++ [e]))).terms from
      Database.terms_setEnvRules]
    apply (Database.Contained.addTerm _ _).terms
    exact Database.mem_addTerm _ _
  refine ⟨e, Or.inr ⟨[a], .cons ?_ .nil, hrowa⟩,
    Or.inr ⟨[b], .cons ?_ .nil, hrowb⟩⟩
  · exact ha.columns hw a (by simp)
  · exact hb.columns hw b (by simp)

theorem out_of_term {d : Database} (hw : d.WF) {f : FnName} {cs vs : List Term}
    (ht : Term.app f (cs ++ vs) ∈ d.terms) : d.Out f cs vs :=
  ⟨cs, CongList.refl fun _ hm => Database.mem_terms_of_arg hw ht
    (List.mem_append_left _ hm), ht⟩

theorem compress_closed {d : Database} (hd : d.Diag) (hw : d.WF)
    (hfix : RunRules rebuildRuleset d = d) (hr : pathCompressRule ∈ d.rules)
    (hu : d.sig ufName = some (tableDecl 1)) {a b c : Term}
    (hab : d.Out ufName [a] [b]) (hbc : d.Out ufName [b] [c]) :
    d.Out ufName [a] [c] := by
  let ρ : Env := [("@a", a), ("@b", b), ("@c", c)]
  have hval : ∀ v ∈ ρ, v.2 ∈ d.terms := by
    intro v hv
    simp only [ρ, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hab.columns hw a (by simp)
    · exact hab.columns hw b (by simp)
    · exact hbc.columns hw c (by simp)
  have hq : ∀ p ∈ pathCompressRule.query, Matches d p ρ := by
    intro p hp
    simp only [pathCompressRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (FlatRead.entry (by simp [hu])
        (by simp [ρ, Expr.evalList, Expr.eval, Env.lookup]) (hab.term hd)).holds
    · exact (FlatRead.entry (by simp [hu])
        (by simp [ρ, Expr.evalList, Expr.eval, Env.lookup]) (hbc.term hd)).holds
  apply out_of_term hw
  exact atom_rule_closed hfix hr rfl hval
    (by simp [ρ, pathCompressRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList])
    hq rfl (by simp [hu]) (by simp [ρ, Expr.evalList, Expr.eval, Env.lookup])

private theorem varsList_map_var (vs : List Var) (v : Var) :
    v ∈ Expr.varsList (vs.map Expr.var) ↔ v ∈ vs := by
  induction vs with
  | nil => simp
  | cons w ws ih => simp [Expr.vars, ih]

theorem rebuildSubst_names {q : Query} {f : FnName} {arg : Expr}
    (cs : List Term) (e x : Term)
    (hv : Pattern.expr (.app (viewName f) (rebuildVars cs.length ++ [.var "@e"])) ∈ q)
    (hu : Pattern.expr (.app ufName [arg, .var "@x"]) ∈ q) :
    ∀ b ∈ rebuildSubst cs e x, b.1 ∈ Query.vars q := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Query.mem_vars.mpr ⟨_, hv, by simp [Pattern.vars, Expr.vars, Expr.varsList]⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Query.mem_vars.mpr ⟨_, hu, by simp [Pattern.vars, Expr.vars, Expr.varsList]⟩
  apply Query.mem_vars.mpr
  refine ⟨_, hv, ?_⟩
  change b.1 ∈ Expr.varsList (rebuildVars cs.length ++ [.var "@e"])
  apply (Expr.mem_varsList_append _ _).mpr
  apply Or.inl
  rw [rebuildVars_eq_map, varsList_map_var]
  exact (List.of_mem_zip hb).1

theorem rebuildSubst_values {d : Database} {cs : List Term} {e x : Term}
    (hc : ∀ t ∈ cs, t ∈ d.terms) (he : e ∈ d.terms) (hx : x ∈ d.terms) :
    ∀ b ∈ rebuildSubst cs e x, b.2 ∈ d.terms := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact he
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hx
  exact hc b.2 (List.of_mem_zip hb).2

theorem output_closed {d : Database} (hd : d.Diag) (hw : d.WF)
    (hfix : RunRules rebuildRuleset d = d) {f : FnName} {cs : List Term} {e x : Term}
    (hr : eclassRule f cs.length ∈ d.rules)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hv : d.Out (viewName f) cs [e]) (he : d.Out ufName [e] [x]) :
    d.Out (viewName f) cs [x] := by
  have hval := rebuildSubst_values
    (fun t ht => hv.columns hw t (List.mem_append_left _ ht))
    (hv.columns hw e (by simp)) (he.columns hw x (by simp))
  have hq : ∀ p ∈ (eclassRule f cs.length).query, Matches d p (rebuildSubst cs e x) := by
    intro p hp
    simp only [eclassRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · apply FlatRead.holds
      refine .entry (by simp [hf]) ?_ (hv.term hd)
      rw [Expr.evalList_append_map, eval_rebuildVars]
      simp [Expr.evalList, Expr.eval]
    · exact (FlatRead.entry (by simp [hu])
        (by simp [Expr.evalList, Expr.eval]) (he.term hd)).holds
  apply out_of_term hw
  refine atom_rule_closed hfix hr rfl hval
    (rebuildSubst_names cs e x (f := f) (arg := .var "@e") (by simp [eclassRule])
      (by simp [eclassRule])) hq rfl (by simp [hf]) ?_
  rw [Expr.evalList_append_map, eval_rebuildVars]
  simp [Expr.evalList, Expr.eval]

theorem child_closed {d : Database} (hd : d.Diag) (hw : d.WF)
    (hfix : RunRules rebuildRuleset d = d) {f : FnName} {cs : List Term} {e x : Term}
    {i : Nat} (hi : i < cs.length) (hr : childRule f cs.length i ∈ d.rules)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hv : d.Out (viewName f) cs [e]) (he : d.Out ufName [cs[i]] [x]) :
    d.Out (viewName f) (cs.set i x) [e] := by
  have hval := rebuildSubst_values
    (fun t ht => hv.columns hw t (List.mem_append_left _ ht))
    (hv.columns hw e (by simp)) (he.columns hw x (by simp))
  have hq : ∀ p ∈ (childRule f cs.length i).query, Matches d p (rebuildSubst cs e x) := by
    intro p hp
    simp only [childRule, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · apply FlatRead.holds
      refine .entry (by simp [hf]) ?_ (hv.term hd)
      rw [Expr.evalList_append_map, eval_rebuildVars]
      simp [Expr.evalList, Expr.eval]
    · exact (FlatRead.entry (by simp [hu])
        (by simp only [Expr.evalList, Expr.eval, rebuildSubst_key i hi, rebuildSubst_x,
          Option.bind_some, Option.map_some, List.singleton_append]) (he.term hd)).holds
  apply out_of_term hw
  refine atom_rule_closed hfix hr rfl hval
    (rebuildSubst_names cs e x (f := f) (arg := .var ("@c" ++ toString i))
      (by simp [childRule]) (by simp [childRule])) hq rfl (by simp [hf]) ?_
  rw [Expr.evalList_append_map,
    Expr.evalList_set (eval_rebuildVars cs e x) i
      (show Expr.eval d.sig (.var "@x") (rebuildSubst cs e x) = some x from
        rebuildSubst_x cs e x)]
  simp [Expr.evalList, Expr.eval]

/-- Re-keying individual columns composes to an arbitrary tuple of parent steps. -/
theorem keys_closed {d : Database} {f : FnName}
    (hchild : ∀ cs e i (hi : i < cs.length) x,
      d.Out (viewName f) cs [e] → d.Out ufName [cs[i]] [x] →
        d.Out (viewName f) (cs.set i x) [e]) {cs ds : List Term}
    (hcs : List.Forall₂ (Parent d) cs ds) :
    ∀ pre e, d.Out (viewName f) (pre ++ cs) [e] → d.Out (viewName f) (pre ++ ds) [e] := by
  induction hcs with
  | nil => exact fun _ _ h => h
  | @cons a b cs ds hab _ ih =>
      intro pre e ho
      have hn : d.Out (viewName f) (pre ++ b :: cs) [e] := by
        rcases hab with rfl | hab
        · exact ho
        · have hi : pre.length < (pre ++ a :: cs).length := by simp
          have huf : d.Out ufName [(pre ++ a :: cs)[pre.length]] [b] := by simpa using hab
          have hnew := hchild _ e pre.length hi b ho huf
          simpa using hnew
      simpa only [List.append_assoc, List.singleton_append] using
        ih (pre ++ [b]) e (by simpa only [List.append_assoc, List.singleton_append] using hn)

/-- Every retained view supplies its declaration and generated rebuilding rules. -/
def TablesPresent (d : Database) : Prop :=
  ∀ f cs e, d.Out (viewName f) cs [e] →
    d.sig (viewName f) = some (tableDecl cs.length) ∧
    eclassRule f cs.length ∈ d.rules ∧ ∀ i < cs.length, childRule f cs.length i ∈ d.rules

/-- Actual mathematical saturation of the generated rules and merges supplies every
closure property used to normalize recursive view readings. -/
theorem closed_of_saturated {d : Database} (hd : d.Diag) (hw : d.WF)
    (hsat : RunSaturated rebuildRuleset d) (ht : TablesPresent d)
    (hu : d.sig ufName = some (tableDecl 1)) (hr : pathCompressRule ∈ d.rules) : Closed d where
  compress := fun _ _ _ => compress_closed hd hw hsat.1 hr hu
  ufJoin := fun _ _ _ ha hb => merge_join hd hw hsat.2 hu hu ha hb
  viewJoin := fun f cs _ _ ha hb => merge_join hd hw hsat.2 hu (ht f cs _ ha).1 ha hb
  output := fun f cs _ _ hv he =>
    output_closed hd hw hsat.1 (ht f cs _ hv).2.1 (ht f cs _ hv).1 hu hv he
  keys := by
    intro f cs ds e hv hl
    apply keys_closed (d := d) (f := f) (fun cs e i hi x hv he =>
      child_closed hd hw hsat.1 hi ((ht f cs e hv).2.2 i hi) (ht f cs e hv).1 hu hv he)
      hl [] e hv

theorem rebuilt_of_saturated {d : Database} (hd : d.Diag) (hw : d.WF)
    (hfin : d.terms.Finite) (hsat : RunSaturated rebuildRuleset d) (ht : TablesPresent d)
    (hu : d.sig ufName = some (tableDecl 1)) (hr : pathCompressRule ∈ d.rules)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → b = a ∨ Term.blt b a = true) : Rebuilt d :=
  ⟨hw, hfin, closed_of_saturated hd hw hsat ht hu hr, hdesc⟩

end Egglog.Congruence.Abstract
