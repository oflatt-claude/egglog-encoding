import EgglogSemantics.Proofs.Congruence.Values
import EgglogSemantics.Proofs.Source.RebuildVars

/-! Executable matches and firings of generated rebuilding rules. -/

namespace Egglog.Congruence

theorem rebuildVars_eq_map (k : Nat) : rebuildVars k = (rebuildVarNames k).map Expr.var := by
  rw [rebuildVars, rebuildVarNames, List.map_map]; rfl

/-- A row's key columns and the two ids used by either rebuilding rule. -/
def rebuildSubst (cs : List Term) (e x : Term) : Env :=
  ("@e", e) :: ("@x", x) :: (rebuildVarNames cs.length).zip cs

@[simp] theorem rebuildSubst_e (cs : List Term) (e x : Term) :
    Env.lookup "@e" (rebuildSubst cs e x) = some e := by
  simp [rebuildSubst, Env.lookup_cons]

@[simp] theorem rebuildSubst_x (cs : List Term) (e x : Term) :
    Env.lookup "@x" (rebuildSubst cs e x) = some x := by
  simp [rebuildSubst, Env.lookup_cons]

theorem rebuildSubst_key {cs : List Term} {e x : Term} (i : Nat) (hi : i < cs.length) :
    Env.lookup ("@c" ++ toString i) (rebuildSubst cs e x) = some cs[i] := by
  have hv : "@c" ++ toString i ∈ rebuildVarNames cs.length := by
    rw [← getElem_rebuildVarNames hi]; exact List.getElem_mem _
  have hne : "@c" ++ toString i ≠ "@e" := by
    intro heq; rw [heq] at hv
    exact not_mem_rebuildVarNames (c := 'e') (by decide) (by decide) _ hv
  have hnx : "@c" ++ toString i ≠ "@x" := by
    intro heq; rw [heq] at hv
    exact not_mem_rebuildVarNames (c := 'x') (by decide) (by decide) _ hv
  simp only [rebuildSubst, Env.lookup_cons, if_neg hne, if_neg hnx]
  rw [← getElem_rebuildVarNames hi]
  exact Env.lookup_zip _ _ (length_rebuildVarNames _) (rebuildVarNames_nodup _) i
    (by simpa only [length_rebuildVarNames] using hi) hi

theorem eval_rebuildVars {sig : Signature} (cs : List Term) (e x : Term) :
    Expr.evalList sig (rebuildVars cs.length) (rebuildSubst cs e x) = some cs := by
  rw [rebuildVars_eq_map]
  apply Expr.evalList_map_var _ _ _ (length_rebuildVarNames _)
  intro i hi hi'
  rw [getElem_rebuildVarNames hi']
  exact rebuildSubst_key i hi'

theorem rebuildSubst_valued {d : FDatabase} {cs : List Term} {e x : Term}
    (hc : ∀ t ∈ cs, t ∈ d.valueTerms) (he : e ∈ d.valueTerms) (hx : x ∈ d.valueTerms) :
    ∀ b ∈ rebuildSubst cs e x, b.2 ∈ d.valueTerms := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact he
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hx
  exact hc b.2 ((List.of_mem_zip hb).2)

/-- Both generated queries retain the key columns and the old and replacement ids. -/
theorem rebuildSubst_canon {d : FDatabase} {q : Query} {f : FnName} {a : Expr}
    (cs : List Term) (e x : Term)
    (hv : Pattern.expr (.app (viewName f) (rebuildVars cs.length ++ [.var "@e"])) ∈ q)
    (hu : Pattern.expr (.app ufName [a, .var "@x"]) ∈ q) :
    let σ := Env.canon (Query.freeVars q []) (rebuildSubst cs e x)
    Expr.evalList d.sig (rebuildVars cs.length) σ = some cs ∧
      Env.lookup "@e" σ = some e ∧ Env.lookup "@x" σ = some x := by
  dsimp only
  refine ⟨Expr.evalList_canon_query (eval_rebuildVars cs e x) (fun v hm => ?_), ?_, ?_⟩
  · exact Query.freeVars_of_atom hv ((Expr.mem_varsList_append _ _).mpr (Or.inl hm))
  · rw [Env.lookup_canon (Query.freeVars_nodup q [])
      (Query.freeVars_of_atom hv (by simp [Expr.varsList, Expr.vars]))]
    exact rebuildSubst_e cs e x
  · rw [Env.lookup_canon (Query.freeVars_nodup q [])
      (Query.freeVars_of_atom hu (by simp [Expr.varsList, Expr.vars]))]
    exact rebuildSubst_x cs e x

/-- Exact table declarations determine the entry split without consulting any row. -/
theorem entry_table {sig : Signature} {f : FnName} {k : Nat} {as vs : List Expr}
    (hp : Prim.ofName f = none) (hd : sig f = some (tableDecl k)) (hlen : as.length = k) :
    (Expr.app f (as ++ vs)).entry sig = some (f, as, vs) := by
  simp [Expr.entry, hp, hd, tableDecl, ← hlen]

theorem entryRead_table {d : FDatabase} {τ : Env} {f : FnName} {k : Nat}
    {as vs : List Expr} {ts us : List Term} (hp : Prim.ofName f = none)
    (hd : d.sig f = some (tableDecl k)) (hlen : as.length = k)
    (ha : Expr.evalList d.sig as τ = some ts) (hv : Expr.evalList d.sig vs τ = some us)
    (hr : (⟨f, ts, us⟩ : Row) ∈ d.rows) (hc : ∀ c ∈ ts ++ us, c ∈ d.valueTerms) :
    EntryRead d τ (.expr (.app f (as ++ vs))) :=
  ⟨f, as, vs, ts, us, rfl, entry_table hp hd hlen, ha, hv, hr,
    fun c hm => Egglog.FDatabase.mem_terms_of_mem_valueTerms (hc c hm)⟩

/-- The output-propagation query matches its two actual input rows. -/
theorem eclassRule_match {d : FDatabase} {f : FnName} {cs : List Term} {e x : Term}
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hurow : (⟨ufName, [e], [x]⟩ : Row) ∈ d.rows)
    (hc : ∀ t ∈ cs, t ∈ d.valueTerms) (he : e ∈ d.valueTerms) (hx : x ∈ d.valueTerms) :
    Env.canon (Query.freeVars (eclassRule f cs.length).query []) (rebuildSubst cs e x)
      ∈ matchQuery d (eclassRule f cs.length).query := by
  apply mem_matchQuery_of_entryReads (rebuildSubst_valued hc he hx)
  intro p hp
  simp only [eclassRule, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · apply entryRead_table (prim_viewName f) hf (by simp [rebuildVars])
      (eval_rebuildVars cs e x)
      (by simp [Expr.evalList, Expr.eval]) hr
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hc t ht
    · exact List.mem_singleton.mp ht ▸ he
  · apply entryRead_table (as := [.var "@e"]) (by decide) hu rfl
      (by simp [Expr.evalList, Expr.eval]) (by simp [Expr.evalList, Expr.eval]) hurow
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    intro t ht
    rcases ht with rfl | rfl <;> assumption

/-- Propagating a live output parent is an executable firing, not an assumed rewrite. -/
theorem eclassRule_fires {d : FDatabase} {f : FnName} {cs : List Term} {e x : Term}
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hurow : (⟨ufName, [e], [x]⟩ : Row) ∈ d.rows)
    (hc : ∀ t ∈ cs, t ∈ d.valueTerms) (he : e ∈ d.valueTerms) (hx : x ∈ d.valueTerms) :
    ∃ σ d', σ ∈ matchQuery d (eclassRule f cs.length).query ∧
      Fired d (eclassRule f cs.length) σ d' ∧
      Term.app (viewName f) (cs ++ [x]) ∈ d'.terms := by
  let q := (eclassRule f cs.length).query
  let τ := rebuildSubst cs e x
  let σ := Env.canon (Query.freeVars q []) τ
  obtain ⟨hks, _, hxs⟩ := rebuildSubst_canon (d := d) (q := q) cs e x
    (f := f) (a := .var "@e") (by simp [q, eclassRule]) (by simp [q, eclassRule])
  change Env.lookup "@x" σ = some x at hxs
  have hev : Expr.evalList d.sig (rebuildVars cs.length ++ [.var "@x"]) σ
      = some (cs ++ [x]) := by
    rw [Expr.evalList_append_map, hks]
    simp [Expr.evalList, Expr.eval, hxs]
  obtain ⟨d', hd', ht⟩ := execLocalActions_atom_of_eval (prim_viewName f) (by simp [hf]) hev
  exact ⟨σ, d', eclassRule_match hf hu hr hurow hc he hx, hd', ht⟩

/-- Re-keying a child likewise matches a view row and that child's live parent edge. -/
theorem childRule_match {d : FDatabase} {f : FnName} {cs : List Term} {e x : Term}
    {i : Nat} (hi : i < cs.length)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hurow : (⟨ufName, [cs[i]], [x]⟩ : Row) ∈ d.rows)
    (hc : ∀ t ∈ cs, t ∈ d.valueTerms) (he : e ∈ d.valueTerms) (hx : x ∈ d.valueTerms) :
    Env.canon (Query.freeVars (childRule f cs.length i).query []) (rebuildSubst cs e x)
      ∈ matchQuery d (childRule f cs.length i).query := by
  apply mem_matchQuery_of_entryReads (rebuildSubst_valued hc he hx)
  intro p hp
  simp only [childRule, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · apply entryRead_table (prim_viewName f) hf (by simp [rebuildVars])
      (eval_rebuildVars cs e x) (by simp [Expr.evalList, Expr.eval]) hr
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hc t ht
    · exact List.mem_singleton.mp ht ▸ he
  · apply entryRead_table (as := [.var ("@c" ++ toString i)]) (by decide) hu rfl
      (by simp only [Expr.evalList, Expr.eval, rebuildSubst_key i hi,
        Option.bind_some, Option.map_some])
      (by simp [Expr.evalList, Expr.eval]) hurow
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    intro t ht
    rcases ht with rfl | rfl
    · exact hc cs[i] (List.getElem_mem hi)
    · exact hx

/-- The child rule records the re-keyed entry through an actual local execution. -/
theorem childRule_fires {d : FDatabase} {f : FnName} {cs : List Term} {e x : Term}
    {i : Nat} (hi : i < cs.length)
    (hf : d.sig (viewName f) = some (tableDecl cs.length))
    (hu : d.sig ufName = some (tableDecl 1))
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows)
    (hurow : (⟨ufName, [cs[i]], [x]⟩ : Row) ∈ d.rows)
    (hc : ∀ t ∈ cs, t ∈ d.valueTerms) (he : e ∈ d.valueTerms) (hx : x ∈ d.valueTerms) :
    ∃ σ d', σ ∈ matchQuery d (childRule f cs.length i).query ∧
      Fired d (childRule f cs.length i) σ d' ∧
      Term.app (viewName f) (cs.set i x ++ [e]) ∈ d'.terms := by
  let q := (childRule f cs.length i).query
  let τ := rebuildSubst cs e x
  let σ := Env.canon (Query.freeVars q []) τ
  obtain ⟨hks, hes, hxs⟩ := rebuildSubst_canon (d := d) (q := q) cs e x
    (f := f) (a := .var ("@c" ++ toString i))
    (by simp [q, childRule]) (by simp [q, childRule])
  change Env.lookup "@e" σ = some e at hes
  have hev : Expr.evalList d.sig ((rebuildVars cs.length).set i (.var "@x") ++ [.var "@e"]) σ
      = some (cs.set i x ++ [e]) := by
    rw [Expr.evalList_append_map,
      Expr.evalList_set hks i (show Expr.eval d.sig (.var "@x") σ = some x from hxs)]
    simp [Expr.evalList, Expr.eval, hes]
  obtain ⟨d', hd', ht⟩ := execLocalActions_atom_of_eval (prim_viewName f) (by simp [hf]) hev
  exact ⟨σ, d', childRule_match hi hf hu hr hurow hc he hx, hd', ht⟩

end Egglog.Congruence
