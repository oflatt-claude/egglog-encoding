import EgglogSemantics.Proofs.Entries

/-! Constructing executable query matches from valued substitutions. -/

namespace Egglog

theorem Env.dom_zip_subset : ∀ (vs : List Var) (as : List Term), Env.dom (vs.zip as) ⊆ vs
  | [], _ => by simp [Env.dom]
  | _ :: _, [] => by simp [Env.dom]
  | v :: vs, a :: as => by
      intro w hw
      rw [List.zip_cons_cons, Env.dom_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Env.dom_zip_subset vs as hw)

theorem Env.lookup_zip : ∀ (vs : List Var) (as : List Term), vs.length = as.length →
    vs.Nodup → ∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length),
      Env.lookup vs[i] (vs.zip as) = some as[i]
  | [], [], _, _, i, hi, _ => by simp at hi
  | v :: vs, a :: as, hlen, hnd, 0, _, _ => by
      rw [List.zip_cons_cons, Env.lookup_cons]
      simp
  | v :: vs, a :: as, hlen, hnd, i + 1, hi, hi' => by
      rw [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hi'
      have hne : vs[i] ≠ v := fun hc => hnd.1 (hc ▸ List.getElem_mem hi)
      rw [List.zip_cons_cons]
      simp only [List.getElem_cons_succ]
      rw [Env.lookup_cons, if_neg hne]
      exact Env.lookup_zip vs as (by simpa using hlen) hnd.2 i hi hi'

/-- **A list of variables evaluates to what the environment binds them to.** -/
theorem Expr.evalList_map_var {sig : Signature} : ∀ (vs : List Var) (as : List Term) (ρ : Env),
    vs.length = as.length →
    (∀ (i : Nat) (hi : i < vs.length) (hi' : i < as.length), Env.lookup vs[i] ρ = some as[i]) →
    Expr.evalList sig (vs.map Expr.var) ρ = some as
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | v :: vs, a :: as, ρ, hlen, h => by
      have h0 : Env.lookup v ρ = some a := h 0 (by simp) (by simp)
      have hrest : Expr.evalList sig (vs.map Expr.var) ρ = some as :=
        Expr.evalList_map_var vs as ρ (by simpa using hlen)
          (fun i hi hi' => h (i + 1) (by simpa using hi) (by simpa using hi'))
      rw [List.map_cons, Expr.evalList, Expr.eval, h0, Option.bind_some, hrest]
      rfl

/-- Every free variable of a list of variable atoms is one of them. -/
theorem Expr.freeVarsList_map_var_subset : ∀ (vs : List Var) (σ : Env),
    Expr.freeVarsList (vs.map Expr.var) σ ⊆ vs
  | [], _ => by simp
  | v :: vs, σ => by
      intro w hw
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff] at hw
      rcases hw with hw | hw
      · rw [Expr.freeVars] at hw
        split at hw
        · exact absurd hw (by simp)
        · rw [List.mem_singleton] at hw; exact hw ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Expr.freeVarsList_map_var_subset vs σ hw)

/-- And one the environment does not bind is free. -/
theorem Expr.mem_freeVarsList_map_var : ∀ (vs : List Var) (σ : Env) {v : Var}, v ∈ vs →
    Env.lookup v σ = none → v ∈ Expr.freeVarsList (vs.map Expr.var) σ
  | [], _, _, hv, _ => by simp at hv
  | w :: vs, σ, v, hv, hn => by
      rw [List.map_cons, Expr.freeVarsList, List.mem_union_iff]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Or.inl (by rw [Expr.freeVars, hn]; simp)
      · exact Or.inr (Expr.mem_freeVarsList_map_var vs σ hv' hn)

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

mutual

/-- **A variable of an expression that evaluates is bound.** `Expr.lookup_isSome_of_mem_evalList`
at every variable rather than only at a top-level one. -/
theorem Expr.lookup_isSome_of_mem_vars {sig : Signature} {ρ : Env} {v : Var} :
    ∀ {e : Expr} {t : Term}, Expr.eval sig e ρ = some t → v ∈ e.vars →
      (Env.lookup v ρ).isSome
  | .lit _, _, _, hv => by simp [Expr.vars] at hv
  | .var w, _, he, hv => by
      obtain rfl : v = w := by simpa [Expr.vars] using hv
      rw [Expr.eval_var] at he; rw [he]; rfl
  | .app f args, t, he, hv => by
      rw [Expr.vars] at hv
      have hl : ∃ ts, Expr.evalList sig args ρ = some ts := by
        rw [Expr.eval] at he
        split at he
        · obtain ⟨ts, hts, -⟩ := Option.map_eq_some_iff.mp he; exact ⟨ts, hts⟩
        · exact absurd he (by simp)
      obtain ⟨ts, hts⟩ := hl
      exact Expr.lookup_isSome_of_mem_varsList hts hv
  | .min a b, t, he, hv => by
      rw [Expr.vars_min, List.mem_union_iff] at hv
      rw [Expr.eval_min] at he
      obtain ⟨x, hx, he'⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp he'
      exact hv.elim (fun h => Expr.lookup_isSome_of_mem_vars hx h)
        (fun h => Expr.lookup_isSome_of_mem_vars hy h)

@[inherit_doc Expr.lookup_isSome_of_mem_vars]
theorem Expr.lookup_isSome_of_mem_varsList {sig : Signature} {ρ : Env} {v : Var} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      v ∈ Expr.varsList es → (Env.lookup v ρ).isSome
  | [], _, _, hv => by simp [Expr.varsList] at hv
  | e :: es, _, he, hv => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨t, ht, he'⟩ := he
      obtain ⟨us, hus, -⟩ := Option.map_eq_some_iff.mp he'
      rw [Expr.varsList, List.mem_union_iff] at hv
      exact hv.elim (fun h => Expr.lookup_isSome_of_mem_vars ht h)
        (fun h => Expr.lookup_isSome_of_mem_varsList hus h)

end


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
