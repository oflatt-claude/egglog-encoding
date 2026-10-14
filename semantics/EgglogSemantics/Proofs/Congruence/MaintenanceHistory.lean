import EgglogSemantics.Proofs.Congruence.History

/-! Rebuilding heads only rearrange held columns. Their writes preserve the connection
between retained entries and live rows without any source-program assumptions. -/

namespace Egglog.Congruence

theorem evalList_vars_held {d : FDatabase} (hw : d.Inv) :
    ∀ (cols : List Expr) {ts : List Term},
      (∀ c ∈ cols, ∃ v, c = Expr.var v) → Expr.evalList d.sig cols d.env = some ts →
      ∀ t ∈ ts, t ∈ d.terms
  | [], _, _, he => by obtain rfl := Option.some.inj he; simp
  | c :: cs, _, hv, he => by
      obtain ⟨v, rfl⟩ := hv c List.mem_cons_self
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Egglog.FDatabase.mem_toDatabase_terms.mp
          (hw.wf.envInTerms (v, x) (Env.mem_of_lookup ht))
      · exact evalList_vars_held hw cs (fun c hc => hv c (List.mem_cons_of_mem _ hc)) hts x hx

/-- A flat head using bound variables only adds an entry over already held columns. -/
theorem execLocalActions_vars_entryRowsUF {d d' : FDatabase} {q : Query} {σ : Env}
    {f : FnName} {cols : List Expr}
    (hv : ∀ c ∈ cols, ∃ v, c = Expr.var v)
    (hi : d.Inv) (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (hσ : σ ∈ matchQuery d q)
    (run : execLocalActions d [.expr (.app f cols)] σ = some d') : EntryRowsUF d' := by
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp run
  have hm' : execAction { d with env := σ ++ d.env } (.expr (.app f (cols ++ []))) =
      some m := by simpa [execActions] using hm
  obtain ⟨ts, vs, hts, hvs, rfl⟩ := execAction_entry hm'
  obtain rfl : vs = [] := (Option.some.inj hvs).symm
  have hcols := evalList_vars_held (hi.setEnvMatch hσ) cols hv hts
  have hsc := Egglog.FDatabase.SubtermClosed.of_wf hi.wf
  exact h.addAtom hshape fun s hs hn _ =>
    FDatabase.subterms_of_columns hsc (by simpa using hcols) s hs hn

/-- Maintenance either compresses UF paths or writes another table over held variables. -/
def MaintenanceHead (r : Rule) : Prop :=
  ∃ f cols, r.actions = [.expr (.app f cols)] ∧
    (∀ c ∈ cols, ∃ v, c = Expr.var v) ∧
    (f ≠ ufName ∨ r.query = pathCompressRule.query ∧ r.actions = pathCompressRule.actions)

private theorem rebuildVars_areVars (k : Nat) :
    ∀ c ∈ rebuildVars k, ∃ v, c = Expr.var v := by
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨_, rfl⟩

private theorem eclass_headShape (f : FnName) (k : Nat) : MaintenanceHead (eclassRule f k) := by
  refine ⟨viewName f, _, rfl, ?_, Or.inl viewName_ne_ufName⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact rebuildVars_areVars k c hc
  · obtain rfl := List.mem_singleton.mp hc; exact ⟨_, rfl⟩

private theorem child_headShape (f : FnName) (k i : Nat) :
    MaintenanceHead (childRule f k i) := by
  refine ⟨viewName f, _, rfl, ?_, Or.inl viewName_ne_ufName⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases mem_or_eq_of_mem_set hc with hc | rfl
    · exact rebuildVars_areVars k c hc
    · exact ⟨_, rfl⟩
  · obtain rfl := List.mem_singleton.mp hc; exact ⟨_, rfl⟩

private theorem maintenanceRules_headShape (P : Program) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → MaintenanceHead r := by
  intro c hc r hr
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · obtain rfl : pathCompressRule = r := Cmd.rule.inj hr
    refine ⟨ufName, _, rfl, ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩
    · obtain rfl : eclassRule f k = r := Cmd.rule.inj hr
      exact eclass_headShape f k
    · obtain rfl : childRule f k i = r := Cmd.rule.inj hr
      exact child_headShape f k i

theorem maintenance_headShape {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) : MaintenanceHead r := by
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenanceRules_headShape P c hc r hr
  · unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl : { s with ruleset := R } = r := Cmd.rule.inj hr
      exact maintenanceRules_headShape P c hc s hs
    next => exact maintenanceRules_headShape P c hc r hr

/-- Every generated rebuilding rule preserves the bridge, including ruleset copies. -/
theorem maintenance_entryRowsUF {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {d d' : FDatabase} {σ : Env} (hi : d.Inv) (hshape : MergeShape d.sig) (h : EntryRowsUF d)
    (hσ : σ ∈ matchQuery d r.query) (run : execLocalActions d r.actions σ = some d') :
    EntryRowsUF d' := by
  obtain ⟨f, cols, ha, hv, _⟩ := maintenance_headShape hc hr
  rw [ha] at run
  exact execLocalActions_vars_entryRowsUF hv hi hshape h hσ run

end Egglog.Congruence
