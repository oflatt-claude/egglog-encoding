import EgglogSemantics.Proofs.Congruence.Properties

/-!
# Execution without equality reasoning

This target interpreter never computes congruence closure. Its equality relation is the
diagonal of the stored values: testing a pair requires structural identity and existence.
The same finite relation serves query matching and function-key collision detection.
Generated UF and rebuilding rules run as ordinary table rules.

The equivalence with the specification's execution is proved in
`Proofs/Congruence/Relational.lean`. The compiled matcher `matchQueryFast` and its
`@[csimp]` equivalence stay here, since the replacement applies only to code compiled
with the lemma in scope.
-/

namespace Egglog.Relational

/-- Structural equality on the stored terms; no closure operation. -/
def diagonal (d : FDatabase) : Finset (Term × Term) :=
  d.terms.toFinset.image fun t => (t, t)

@[simp] theorem mem_diagonal {d : FDatabase} {a b : Term} :
    (a, b) ∈ diagonal d ↔ a = b ∧ a ∈ d.terms := by
  simp only [diagonal, Finset.mem_image, List.mem_toFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨rfl, ht⟩
  · rintro ⟨rfl, ht⟩; exact ⟨a, ht, rfl, rfl⟩

/-- All the general interpreter's equality rules collapse to structural identity. -/
theorem diagonal_eq_closure {d : FDatabase} (h : d.EqsRefl) :
    diagonal d = d.closureF := by
  ext ⟨a, b⟩
  rw [mem_diagonal, FDatabase.mem_closureF_iff]
  constructor
  · rintro ⟨rfl, ha⟩
    exact Cong.assert (Or.inl ⟨rfl, ha⟩)
  · intro hab
    exact ⟨Cong.eq_of_eqsRefl h.toDatabase hab, (FDatabase.toDatabase_cong_mem hab).1⟩

/-- Ordinary table matching and structural equality, including existence for `=`. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .expr e =>
    match e.entry d.sig with
    | some (f, keys, vals) =>
      match Expr.evalList d.sig vals σ, Expr.evalList d.sig keys σ with
      | some us, some ts =>
        let ids := diagonal ((d.addTerms ts).addTerms us)
        d.rows.any fun r =>
          decide (r.fn = f) && FDatabase.congrTuple ids ts r.args
            && FDatabase.congrTuple ids us r.out
      | _, _ => false
    | none =>
      match e.evalAtom d.sig σ with
      | none => false
      | some t => decide (t ∈ d.terms)
  | .eq e₁ e₂ =>
    match e₁.eval d.sig σ, e₂.eval d.sig σ with
    | some a, some b => decide (a = b) && decide (a ∈ d.terms)
    | _, _ => false

theorem eqsRefl_of_noUnions {d : FDatabase} (h : d.NoUnions) : d.EqsRefl := by
  intro p hp
  simp [h.eqs] at hp

theorem eqsRefl_addTerms (ts : List Term) {d : FDatabase} (h : d.EqsRefl) :
    (d.addTerms ts).EqsRefl := by
  induction ts generalizing d with
  | nil => exact h
  | cons t ts ih => exact ih h

theorem patternHolds_eq {d : FDatabase} (h : d.EqsRefl) (p : Pattern) (σ : Env) :
    patternHolds d p σ = Egglog.patternHolds d p σ := by
  cases p with
  | expr e =>
    cases he : e.entry d.sig with
    | some entry =>
      obtain ⟨f, keys, vals⟩ := entry
      cases hv : Expr.evalList d.sig vals σ <;>
        cases hk : Expr.evalList d.sig keys σ <;>
        simp only [patternHolds, Egglog.patternHolds, he, hv, hk]
      rw [diagonal_eq_closure (eqsRefl_addTerms _ (eqsRefl_addTerms _ h))]
    | none =>
      cases ht : e.evalAtom d.sig σ with
      | none => simp only [patternHolds, Egglog.patternHolds, he, ht]
      | some t =>
        simp only [patternHolds, Egglog.patternHolds, he, ht]
        rw [← diagonal_eq_closure (d := d.addTerm t) h]
        simp only [mem_diagonal]
        have hm : t ∈ (d.addTerm t).terms := by
          simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
          exact Or.inl ((Term.mem_subtermList _).mpr (Term.self_mem_subterms _))
        simp [hm]
  | eq a b =>
    cases hx : a.eval d.sig σ <;> cases hy : b.eval d.sig σ <;>
      simp only [patternHolds, Egglog.patternHolds, hx, hy]
    rename_i x y
    rw [← diagonal_eq_closure (d := (d.addTerm x).addTerm y) h]
    simp only [mem_diagonal]
    have hm : x ∈ ((d.addTerm x).addTerm y).terms :=
      FDatabase.mem_terms_addTerm (by
        simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
        exact Or.inl ((Term.mem_subtermList _).mpr (Term.self_mem_subterms _)))
    simp [hm]

def matchQuery (d : FDatabase) (q : Query) : List Env :=
  (assignments d.valueTerms (Query.freeVars q [])).filter fun σ =>
    q.all fun p => patternHolds d p (Env.canon (p.freeVars []) σ)

/-- `filter` distributes over `flatMap`. -/
private theorem filter_flatMap {α β : Type} (p : β → Bool) (f : α → List β) (l : List α) :
    (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

/-- `filter` past a `map`, as the composed predicate. -/
private theorem filter_map_comp {α β : Type} (p : β → Bool) (f : α → β) (l : List α) :
    (l.map f).filter p = (l.filter fun a => p (f a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

def matchPrune (d : FDatabase) (q : Query) (ts : List Term)
    (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHolds d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      ts.flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHolds d p (Env.canon (p.freeVars []) pre') then
          (matchPrune d q ts pre' vs).map fun σ => (v, t) :: σ
        else []

/-- **Pruning drops exactly the candidates the final filter would have.** -/
theorem matchPrune_eq (d : FDatabase) (q : Query)
    (ts : List Term) :
    ∀ (vs : List Var) (pre : Env), matchPrune d q ts pre vs
      = (assignments ts vs).filter fun σ =>
          q.all fun p => patternHolds d p (Env.canon (p.freeVars []) (pre ++ σ)) := by
  intro vs
  induction vs with
  | nil =>
    intro pre
    simp [matchPrune, assignments, List.filter_cons, List.append_nil]
  | cons v vs ih =>
    intro pre
    rw [matchPrune, assignments, filter_flatMap]
    refine List.flatMap_congr fun t _ => ?_
    rw [filter_map_comp]
    by_cases hg : (Query.decided d (pre ++ [(v, t)]) q).all fun p =>
        patternHolds d p (Env.canon (p.freeVars []) (pre ++ [(v, t)]))
    · rw [if_pos hg, ih (pre ++ [(v, t)])]
      congr 1
      refine List.filter_congr fun σ _ => ?_
      simp only [List.append_assoc, List.singleton_append]
    · -- the prefix already falsifies a pattern, so no extension of it survives
      have hnil : ((assignments ts vs).filter fun σ =>
          q.all fun p => patternHolds d p
            (Env.canon (p.freeVars []) (pre ++ (v, t) :: σ))) = [] := by
        rw [Bool.not_eq_true, List.all_eq_false] at hg
        obtain ⟨p, hp, hfail⟩ := hg
        obtain ⟨hpq, hdecB⟩ := List.mem_filter.mp hp
        have hdec : ∀ w ∈ p.freeVars [], w ∈ Env.dom (pre ++ [(v, t)]) := fun w hw =>
          of_decide_eq_true (List.all_eq_true.mp hdecB w hw)
        refine List.filter_eq_nil_iff.mpr fun σ _ hall => hfail ?_
        have hp' := List.all_eq_true.mp hall p hpq
        rw [show pre ++ (v, t) :: σ = (pre ++ [(v, t)]) ++ σ by simp,
          Env.canon_append_of_dom hdec] at hp'
        exact hp'
      rw [if_neg hg, hnil, List.map_nil]

/-- Prune assignments as soon as a fully bound atom fails exact matching. -/
def matchQueryPruned (d : FDatabase) (q : Query) : List Env :=
  matchPrune d q d.valueTerms [] (Query.freeVars q [])

theorem matchQueryPruned_eq (d : FDatabase) (q : Query) :
    matchQueryPruned d q = matchQuery d q := by
  rw [matchQueryPruned, matchPrune_eq, matchQuery]
  simp

/-- The row index narrows candidates using only the diagonal relation. -/
def matchJoin (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (ts : List Term)
    (held : Bool) (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHolds d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      (joinCands cl d q held ts pre v).flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHolds d p (Env.canon (p.freeVars []) pre') then
          (matchJoin cl d q ts held pre' vs).map fun σ => (v, t) :: σ
        else []

private theorem flatMap_filter_eq {α β : Type} (P : α → Bool) (F : α → List β) :
    ∀ l : List α, (∀ t ∈ l, P t = false → F t = []) →
      (l.filter P).flatMap F = l.flatMap F := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    by_cases hx : P x
    · simp only [List.filter_cons, if_pos hx, List.flatMap_cons]
      rw [ih fun t ht => h t (List.mem_cons_of_mem _ ht)]
    · simp only [Bool.not_eq_true] at hx
      rw [List.filter_cons, if_neg (by simp [hx]), List.flatMap_cons,
        h x List.mem_cons_self hx, List.nil_append]
      exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

theorem matchJoin_eq (d : FDatabase) (hd : d.EqsRefl) (q : Query)
    (ts : List Term) (held : Bool) (hheld : held = true → ∀ u ∈ ts, d.holdsAll [u] = true) :
    ∀ (vs : List Var) (pre : Env),
      matchJoin (diagonal d) d q ts held pre vs = matchPrune d q ts pre vs := by
  intro vs
  induction vs with
  | nil => intro pre; rfl
  | cons v vs ih =>
    intro pre
    rw [matchJoin, matchPrune]
    simp only [ih]
    simp only [joinCands]
    split
    · rename_i hb
      refine flatMap_filter_eq _ _ ts fun t ht hp => ?_
      split
      · rename_i hg
        refine List.map_eq_nil_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun τ hτ => ?_)
        rw [matchPrune_eq] at hτ
        obtain ⟨hτa, hτp⟩ := List.mem_filter.mp hτ
        have hwith : ∀ p σ, patternHoldsWith (diagonal d) d p σ = patternHolds d p σ :=
          fun p σ => by rw [diagonal_eq_closure hd, patternHoldsWith_eq, patternHolds_eq hd]
        simp only [← hwith] at hτp
        have := joinCands_mem (held := held) hheld ht (mem_assignments.mp hτa).2 hτp
        simp only [joinCands, if_pos hb, List.mem_filter] at this
        rw [this.2] at hp
        exact Bool.noConfusion hp
      · rfl
    · rfl

def matchQueryFast (d : FDatabase) (q : Query) : List Env :=
  if d.eqsReflB then
    matchJoin (diagonal d) d q d.valueTerms (d.holdsAll d.valueTerms) [] (Query.freeVars q [])
  else matchQueryPruned d q

@[csimp] theorem matchQuery_eq_fast : @matchQuery = @matchQueryFast := by
  funext d q
  unfold matchQueryFast
  split
  · rename_i hd
    rw [matchJoin_eq d ((FDatabase.eqsReflB_iff d).mp hd) q d.valueTerms
      (d.holdsAll d.valueTerms) (fun hh u hu => by
        simp only [FDatabase.holdsAll, List.all_eq_true] at hh ⊢
        simpa only [List.mem_singleton, forall_eq] using hh u hu)]
    exact (matchQueryPruned_eq d q).symm
  · exact (matchQueryPruned_eq d q).symm

def fireRule (d acc : FDatabase) (r : Rule) : FDatabase :=
  (matchQuery d r.query).foldl (fireInto d r) acc

def runRules (R : RulesetName) (d : FDatabase) : FDatabase :=
  (d.rules.filter fun r => r.ruleset == R).foldl (fireRule d) d

/-- Function merges use structural keys; there is no implicit congruence rebuild. -/
def mergeRound (d : FDatabase) : FDatabase :=
  if !d.hasMergeRow then d else
    FDatabase.mergeRoundWith (diagonal d) { d with rows := d.rows.dedup }

def mergeSaturate : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (mergeRound d) then some d else none
  | n + 1, d =>
    let e := mergeRound d
    if d.sameData e then some d else mergeSaturate n e

def runRound (R : RulesetName) (d : FDatabase) : Option FDatabase :=
  mergeSaturate mergeFuel (runRules R d)

def runSaturate (R : RulesetName) : Nat → FDatabase → Option FDatabase
  | 0, d => (runRound R d).bind fun e => if d.sameData e then some d else none
  | n + 1, d => (runRound R d).bind fun e =>
    if d.sameData e then some d else runSaturate R n e

def execCmd (d : FDatabase) : Cmd → Option FDatabase
  | .action a => (execAction d a).bind (mergeSaturate mergeFuel)
  | .rule r => some { d with rules := r :: d.rules }
  | .run R => runRound R d
  | .saturate R => runSaturate R runFuel d
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

def execProgram (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | c :: cs => (execCmd d c).bind fun e => execProgram e cs

/-- Execute a union-free program using only structural equality and table operations. -/
def exec (p : Program) (_ : p.UnionFree) : Option FDatabase := execProgram FDatabase.empty p

end Egglog.Relational
