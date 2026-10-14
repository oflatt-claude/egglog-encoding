import EgglogSemantics.Proofs.Bindings
import EgglogSemantics.Proofs.Entries

/-! Constructing executable query matches from valued substitutions. -/

namespace Egglog

/-- **`matchQuery` completeness, in general form.** A substitution the enumerator will offer is
`Env.canon`-shaped at `Query.freeVars`' own order and drawn from `FDatabase.valueTerms`; the
per-atom check then reads it restricted to that atom, and the two restrictions compose. -/
theorem mem_matchQuery_of_lookup {d : FDatabase} {q : Query} {τ : Env}
    (hdef : ∀ v ∈ Query.freeVars q [], (Env.lookup v τ).isSome = true)
    (hval : ∀ v ∈ Query.freeVars q [], ∀ t, Env.lookup v τ = some t → t ∈ d.valueTerms)
    (hp : ∀ p ∈ q, patternHolds d p (Env.canon (p.freeVars []) τ) = true) :
    Env.canon (Query.freeVars q []) τ ∈ matchQuery d q := by
  rw [matchQuery, List.mem_filter]
  refine ⟨mem_assignments.mpr ⟨Env.dom_canon hdef, fun b hb => ?_⟩, List.all_eq_true.mpr ?_⟩
  · obtain ⟨hmem, hlk⟩ := Env.mem_canon hb
    exact hval b.1 hmem b.2 hlk
  · intro p hpq
    rw [Env.canon_canon (Query.freeVars_subset hpq) (Query.freeVars_nodup q [])]
    exact hp p hpq


/-- A table atom answered directly by an indexed row, with existing columns. -/
def EntryRead (d : FDatabase) (τ : Env) (p : Pattern) : Prop :=
  ∃ f as vs ts us, p = .expr (.app f (as ++ vs)) ∧
    (Expr.app f (as ++ vs)).entry d.sig = some (f, as, vs) ∧
    Expr.evalList d.sig as τ = some ts ∧ Expr.evalList d.sig vs τ = some us ∧
    (⟨f, ts, us⟩ : Row) ∈ d.rows ∧ (∀ c ∈ ts ++ us, c ∈ d.terms)

theorem EntryRead.bound {d : FDatabase} {τ : Env} {p : Pattern} (h : EntryRead d τ p)
    {v : Var} (hv : v ∈ p.freeVars []) : (Env.lookup v τ).isSome := by
  obtain ⟨f, as, vs, ts, us, rfl, _, ha, hv', _, _⟩ := h
  have hx := (Pattern.mem_freeVars _).mp hv |>.1
  rw [Pattern.vars, Expr.vars, Expr.mem_varsList_append] at hx
  exact hx.elim (fun h => Expr.lookup_isSome_of_mem_varsList ha h)
    (fun h => Expr.lookup_isSome_of_mem_varsList hv' h)

/-- Restricting a substitution to an atom retains all its column evaluations. -/
theorem EntryRead.holds {d : FDatabase} {τ : Env} {p : Pattern} (h : EntryRead d τ p) :
    patternHolds d p (Env.canon (p.freeVars []) τ) = true := by
  obtain ⟨f, as, vs, ts, us, rfl, he, ha, hv, hr, hc⟩ := h
  have hag : ∀ v ∈ Expr.varsList (as ++ vs),
      Env.lookup v (Env.canon ((Pattern.expr (.app f (as ++ vs))).freeVars []) τ)
        = Env.lookup v τ := by
    intro v hm
    apply Env.lookup_canon (Pattern.freeVars_nodup _ [])
    exact (Pattern.mem_freeVars _).mpr ⟨hm, by simp⟩
  apply patternHolds_entry_of_mem_rows he ?_ ?_ hr hc
  · rw [Expr.evalList_agreeOn as (fun v hv => hag v
      (Expr.mem_varsList_append as vs |>.mpr (Or.inl hv)))]; exact ha
  · rw [Expr.evalList_agreeOn vs (fun v hv => hag v
      (Expr.mem_varsList_append as vs |>.mpr (Or.inr hv)))]; exact hv

/-- Indexed reads and a valued environment give an actual enumerated query match. -/
theorem mem_matchQuery_of_entryReads {d : FDatabase} {τ : Env} {q : Query}
    (hv : ∀ b ∈ τ, b.2 ∈ d.valueTerms) (h : ∀ p ∈ q, EntryRead d τ p) :
    Env.canon (Query.freeVars q []) τ ∈ matchQuery d q := by
  apply mem_matchQuery_of_lookup
  · intro v hm
    obtain ⟨p, hp, hpm⟩ := Query.mem_freeVars.mp hm
    exact (h p hp).bound hpm
  · intro v _ t ht
    exact hv (v, t) (Env.mem_of_lookup ht)
  · exact fun p hp => (h p hp).holds


/-- A column variable of a queried atom is retained by the whole-query substitution. -/
theorem Query.freeVars_of_atom {q : Query} {f : FnName} {cols : List Expr} {v : Var}
    (hp : Pattern.expr (.app f cols) ∈ q) (hv : v ∈ Expr.varsList cols) :
    v ∈ Query.freeVars q [] :=
  Query.freeVars_subset hp ((Pattern.mem_freeVars _).mpr ⟨hv, by simp⟩)

theorem Expr.evalList_canon_query {sig : Signature} {q : Query} {es : List Expr}
    {τ : Env} {ts : List Term} (he : Expr.evalList sig es τ = some ts)
    (hv : ∀ v ∈ Expr.varsList es, v ∈ Query.freeVars q []) :
    Expr.evalList sig es (Env.canon (Query.freeVars q []) τ) = some ts := by
  rw [Expr.evalList_agreeOn es (fun v hm => Env.lookup_canon
    (Query.freeVars_nodup q []) (hv v hm))]
  exact he

/-- A declared, evaluated head atom has a successful local firing that records its term. -/
theorem execLocalActions_atom_of_eval {d : FDatabase} {f : FnName} {cols : List Expr}
    {ts : List Term} {σ : Env} (hd : (d.sig f).isSome)
    (he : Expr.evalList d.sig cols σ = some ts) :
    ∃ d', execLocalActions d [.expr (.app f cols)] σ = some d' ∧
      Term.app f ts ∈ d'.terms := by
  let d' := { ({d with env := σ ++ d.env}.addAtom (.app f ts)) with
    env := d.env, rules := d.rules }
  refine ⟨d', ?_, ?_⟩
  · simp only [execLocalActions, execActions,
      execAction_atom_of_eval (d := { d with env := σ ++ d.env }) hd
        (Expr.evalList_append_env (τ := d.env) cols he), Option.bind_some,
      Option.map_some]
    rfl
  · change Term.app f ts ∈ ({d with env := σ ++ d.env}.addTerm (.app f ts)).terms
    exact FDatabase.self_mem_addTerm _ _

end Egglog
