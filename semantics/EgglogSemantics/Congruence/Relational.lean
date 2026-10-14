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

/-- Membership in the diagonal, as a test: identity, then existence. The scan of the term
list happens only for an identical pair; the set would be scanned for every pair. -/
def same (ts : List Term) (a b : Term) : Bool := decide (a = b) && decide (a ∈ ts)

theorem same_eq {d : FDatabase} (a b : Term) :
    same d.terms a b = decide ((a, b) ∈ diagonal d) := by
  simp only [same, mem_diagonal, Bool.decide_and]

/-- `FDatabase.congrTuple` at the diagonal. -/
def sameTuple (ts : List Term) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => same ts q.1 q.2

theorem sameTuple_eq {d : FDatabase} (as bs : List Term) :
    sameTuple d.terms as bs = FDatabase.congrTuple (diagonal d) as bs := by
  simp only [sameTuple, FDatabase.congrTuple, same_eq, Prod.mk.eta]

/-- Congruent key tuples are identical. -/
theorem congrTuple_diagonal_imp {d : FDatabase} {as bs : List Term}
    (h : FDatabase.congrTuple (diagonal d) as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [FDatabase.congrTuple]
  | cons a as ih =>
    cases bs with
    | nil => simp [FDatabase.congrTuple] at h
    | cons b bs =>
      simp only [FDatabase.congrTuple, List.length_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff, decide_eq_true_eq,
        mem_diagonal] at h
      obtain ⟨hlen, ⟨rfl, _⟩, hall⟩ := h
      rw [ih (bs := bs) (by simp only [FDatabase.congrTuple, hlen, beq_self_eq_true,
        Bool.true_and, hall])]

/-- A pair drawn from `as.zip as` is an element of `as`, twice. -/
private theorem mem_zip_self {as : List Term} {q : Term × Term} (h : q ∈ as.zip as) :
    q.1 = q.2 ∧ q.1 ∈ as := by
  induction as with
  | nil => simp at h
  | cons a as ih =>
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, List.mem_cons_self⟩
    · exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

/-- Tuples drawn from the list are congruent exactly when identical. -/
theorem congrTuple_diagonal_eq {d : FDatabase} {as bs : List Term} (h : ∀ a ∈ as, a ∈ d.terms) :
    FDatabase.congrTuple (diagonal d) as bs = decide (as = bs) := by
  by_cases hab : as = bs
  · subst hab
    rw [decide_eq_true rfl]
    simp only [FDatabase.congrTuple, beq_self_eq_true, Bool.true_and, List.all_eq_true,
      decide_eq_true_eq]
    intro q hq
    obtain ⟨x, y⟩ := q
    obtain ⟨hxy, hx⟩ := mem_zip_self hq
    exact mem_diagonal.mpr ⟨hxy, h _ hx⟩
  · rw [decide_eq_false hab]
    cases hc : FDatabase.congrTuple (diagonal d) as bs
    · rfl
    · exact absurd (congrTuple_diagonal_imp hc) hab

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
        d.rows.any fun r =>
          decide (r.fn = f) && decide (ts = r.args) && decide (us = r.out)
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

/-- `addTerms` records each of its terms. -/
private theorem mem_addTerms_of_mem {d : FDatabase} {ts : List Term} {t : Term} (h : t ∈ ts) :
    t ∈ (d.addTerms ts).terms := by
  induction ts generalizing d with
  | nil => simp at h
  | cons u ts ih =>
    have hstep : d.addTerms (u :: ts) = (d.addTerm u).addTerms ts := rfl
    rw [hstep]
    rcases List.mem_cons.mp h with rfl | h
    · exact FDatabase.mem_addTerms_terms (FDatabase.self_mem_addTerm _ _)
    · exact ih h

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
      rename_i us ts
      rw [← diagonal_eq_closure (eqsRefl_addTerms us (eqsRefl_addTerms ts h))]
      have hts : ∀ a ∈ ts, a ∈ ((d.addTerms ts).addTerms us).terms := fun a ha =>
        FDatabase.mem_addTerms_terms (mem_addTerms_of_mem ha)
      have hus : ∀ a ∈ us, a ∈ ((d.addTerms ts).addTerms us).terms := fun a ha =>
        mem_addTerms_of_mem ha
      congr 1
      funext r
      rw [congrTuple_diagonal_eq hts, congrTuple_diagonal_eq hus]
    | none =>
      cases ht : e.evalAtom d.sig σ with
      | none => simp only [patternHolds, Egglog.patternHolds, he, ht]
      | some t =>
        simp only [patternHolds, Egglog.patternHolds, he, ht]
        rw [← diagonal_eq_closure (d := d.addTerm t) h]
        simp only [mem_diagonal]
        have hm : t ∈ (d.addTerm t).terms := FDatabase.self_mem_addTerm d t
        simp [hm]
  | eq a b =>
    cases hx : a.eval d.sig σ <;> cases hy : b.eval d.sig σ <;>
      simp only [patternHolds, Egglog.patternHolds, hx, hy]
    rename_i x y
    rw [← diagonal_eq_closure (d := (d.addTerm x).addTerm y) h]
    simp only [mem_diagonal]
    have hm : x ∈ ((d.addTerm x).addTerm y).terms :=
      FDatabase.mem_terms_addTerm (FDatabase.self_mem_addTerm d x)
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

/-- `Egglog.joinConsistent` at the diagonal. -/
def joinConsistent (ts : List Term) (ks : List (Option Term)) (xs : List Term) : Bool :=
  ks.length == xs.length && (ks.zip xs).all fun p =>
    match p.1 with
    | none => true
    | some t => same ts t p.2

theorem joinConsistent_eq {d : FDatabase} (ks : List (Option Term)) (xs : List Term) :
    joinConsistent d.terms ks xs = Egglog.joinConsistent (diagonal d) ks xs := by
  simp only [joinConsistent, Egglog.joinConsistent, same_eq]
  rfl

/-- `Egglog.joinPlan` at the diagonal. -/
def joinPlan (d : FDatabase) (pre : Env) (v : Var) : Pattern → Option JoinAtom
  | .expr e =>
    match e.entry d.sig with
    | none => none
    | some (f, as, vs) =>
      let vars := (Pattern.expr e).freeVars []
      if (d.sig.mergeOf f).isSome && joinDrivable as && joinDrivable vs
          && decide (v ∈ vars) then
        let ρ := Env.canon vars pre
        let ka := joinKnown ρ as
        let kv := joinKnown ρ vs
        if ((ka ++ kv).filterMap id).all fun u => decide (u ∈ d.terms) then
          some ⟨vars, vs, as,
            d.rows.filter fun r =>
              (r.fn == f) && joinConsistent d.terms ka r.args && joinConsistent d.terms kv r.out⟩
        else none
      else none
  | _ => none

/-- `List.all` under a predicate change on the members. -/
private theorem all_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      all_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- A determined operand is a literal or a binding of `pre`, so with the bindings held its
subterms are recorded exactly when it is. -/
private theorem subtermList_all_eq_mem (d : FDatabase) (pre : Env) (vars : List Var)
    (es : List Expr) (hpre : ∀ b ∈ pre, d.holdsAll [b.2] = true) {u : Term}
    (hu : some u ∈ joinKnown (Env.canon vars pre) es) :
    (u.subtermList.all fun s => decide (s ∈ d.terms)) = decide (u ∈ d.terms) := by
  obtain ⟨e, _, he⟩ := List.mem_map.mp hu
  cases e with
  | lit l =>
    simp only [joinOperand, Option.some.injEq] at he
    subst he
    simp only [Term.subtermList_lit, List.all_cons, List.all_nil, Bool.and_true]
  | var w =>
    simp only [joinOperand] at he
    have hb : Env.lookup w pre = some u := (Env.mem_canon (Env.mem_of_lookup he)).2
    have hw : d.holdsAll [u] = true := hpre (w, u) (Env.mem_of_lookup hb)
    simp only [FDatabase.holdsAll, List.all_cons, List.all_nil, Bool.and_true] at hw
    have hmem : u ∈ d.terms :=
      of_decide_eq_true (List.all_eq_true.mp hw u (Term.self_mem_subtermList u))
    rw [hw, decide_eq_true hmem]
  | app f args => simp [joinOperand] at he
  | min a b => simp [joinOperand] at he

/-- With the bindings held, the general guard asks exactly membership. -/
private theorem holdsAll_joinKnown_eq (d : FDatabase) (pre : Env) (vars : List Var)
    (as vs : List Expr) (hpre : ∀ b ∈ pre, d.holdsAll [b.2] = true) :
    d.holdsAll
        ((joinKnown (Env.canon vars pre) as ++ joinKnown (Env.canon vars pre) vs).filterMap id)
      = ((joinKnown (Env.canon vars pre) as ++ joinKnown (Env.canon vars pre) vs).filterMap id).all
          fun u => decide (u ∈ d.terms) := by
  unfold FDatabase.holdsAll
  refine all_congr_mem fun u hu => ?_
  obtain ⟨o, ho, hou⟩ := List.mem_filterMap.mp hu
  simp only [id_eq] at hou
  subst hou
  rcases List.mem_append.mp ho with ho | ho
  · exact subtermList_all_eq_mem d pre vars as hpre ho
  · exact subtermList_all_eq_mem d pre vars vs hpre ho

/-- A determined operand is a literal or a binding of `pre`; with the bindings held, the
general guard asks exactly membership. -/
theorem joinPlan_eq (d : FDatabase) (pre : Env) (v : Var) (p : Pattern)
    (hpre : ∀ b ∈ pre, d.holdsAll [b.2] = true) :
    joinPlan d pre v p = Egglog.joinPlan (diagonal d) d pre v p := by
  cases p with
  | eq _ _ => rfl
  | expr e =>
    cases he : e.entry d.sig with
    | none => simp only [joinPlan, Egglog.joinPlan, he]
    | some entry =>
      obtain ⟨f, as, vs⟩ := entry
      simp only [joinPlan, Egglog.joinPlan, he, joinConsistent_eq,
        holdsAll_joinKnown_eq d pre _ as vs hpre]

/-- `JoinAtom.keeps` at the diagonal. -/
def keeps (a : JoinAtom) (d : FDatabase) (pre : Env) (v : Var) (t : Term) : Bool :=
  let ρ := Env.canon a.vars (pre ++ [(v, t)])
  a.rows.any fun r =>
    joinConsistent d.terms (joinKnown ρ a.keys) r.args
      && joinConsistent d.terms (joinKnown ρ a.outs) r.out

theorem keeps_eq (a : JoinAtom) (d : FDatabase) (pre : Env) (v : Var) (t : Term) :
    keeps a d pre v t = a.keeps (diagonal d) d pre v t := by
  simp only [keeps, JoinAtom.keeps, joinConsistent_eq]

/-- `Egglog.joinCands` at the diagonal. -/
def joinCands (d : FDatabase) (q : Query) (held : Bool) (ts : List Term) (pre : Env)
    (v : Var) : List Term :=
  if held then
    let plans := (q.filterMap (joinPlan d pre v)).mergeSort fun a b =>
      decide (a.rows.length ≤ b.rows.length)
    ts.filter fun t => plans.all fun a => keeps a d pre v t
  else ts

theorem joinCands_eq (d : FDatabase) (q : Query) (held : Bool) (ts : List Term) (pre : Env)
    (v : Var) (hpre : ∀ b ∈ pre, d.holdsAll [b.2] = true) :
    joinCands d q held ts pre v = Egglog.joinCands (diagonal d) d q held ts pre v := by
  have hplan : joinPlan d pre v = Egglog.joinPlan (diagonal d) d pre v :=
    funext fun p => joinPlan_eq d pre v p hpre
  simp only [joinCands, Egglog.joinCands, hplan, keeps_eq]

/-- The row index narrows candidates using only the diagonal relation. -/
def matchJoin (d : FDatabase) (q : Query) (ts : List Term)
    (held : Bool) (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHolds d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      (joinCands d q held ts pre v).flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHolds d p (Env.canon (p.freeVars []) pre') then
          (matchJoin d q ts held pre' vs).map fun σ => (v, t) :: σ
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
    ∀ (vs : List Var) (pre : Env), (held = true → ∀ b ∈ pre, b.2 ∈ ts) →
      matchJoin d q ts held pre vs = matchPrune d q ts pre vs := by
  intro vs
  induction vs with
  | nil => intro pre _; rfl
  | cons v vs ih =>
    intro pre hpre
    rw [matchJoin, matchPrune]
    cases held with
    | false =>
      have ih' : ∀ pre, matchJoin d q ts false pre vs = matchPrune d q ts pre vs :=
        fun pre => ih pre fun h => absurd h Bool.false_ne_true
      simp only [joinCands, Bool.false_eq_true, ↓reduceIte, ih']
    | true =>
      rw [joinCands_eq d q true ts pre v fun b hb => hheld rfl _ (hpre rfl b hb)]
      simp only [Egglog.joinCands, ↓reduceIte]
      refine (List.flatMap_congr fun t ht => ?_).trans
        (flatMap_filter_eq _ _ ts fun t ht hp => ?_)
      · have hmem : t ∈ ts := List.mem_of_mem_filter ht
        simp only [ih (pre ++ [(v, t)]) fun _ b hb => by
          rcases List.mem_append.mp hb with hb | hb
          · exact hpre rfl b hb
          · rw [List.mem_singleton] at hb; exact hb ▸ hmem]
      · split
        · rename_i hg
          refine List.map_eq_nil_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun τ hτ => ?_)
          rw [matchPrune_eq] at hτ
          obtain ⟨hτa, hτp⟩ := List.mem_filter.mp hτ
          have hwith : ∀ p σ, patternHoldsWith (diagonal d) d p σ = patternHolds d p σ :=
            fun p σ => by rw [diagonal_eq_closure hd, patternHoldsWith_eq, patternHolds_eq hd]
          simp only [← hwith] at hτp
          have := joinCands_mem (held := true) hheld ht (mem_assignments.mp hτa).2 hτp
          simp only [Egglog.joinCands, ↓reduceIte, List.mem_filter] at this
          rw [this.2] at hp
          exact Bool.noConfusion hp
        · rfl

/-- Whether every recorded application's children are recorded, which closes the list
under subterms: the join may then take every candidate as held without enumerating its
subterms. -/
def _root_.Egglog.FDatabase.childrenRecordedB (d : FDatabase) : Bool :=
  d.terms.all fun t => match t with
    | .lit _ => true
    | .app _ args => args.all fun a => decide (a ∈ d.terms)

theorem holdsAll_of_childrenRecorded {d : FDatabase} (h : d.childrenRecordedB = true)
    {u : Term} (hu : u ∈ d.terms) : d.holdsAll [u] = true := by
  have hrec : ∀ t ∈ d.terms, ∀ s ∈ t.subtermList, s ∈ d.terms := by
    intro t
    induction t using Term.recTerm with
    | lit l =>
      intro ht s hs
      rw [Term.subtermList_lit, List.mem_singleton] at hs
      exact hs ▸ ht
    | app f args ih =>
      intro ht s hs
      rw [Term.subtermList_app, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ht
      · obtain ⟨a, ha, hsa⟩ := (Term.mem_subtermListL args).mp hs
        have hargs := List.all_eq_true.mp h (.app f args) ht
        simp only [List.all_eq_true, decide_eq_true_eq] at hargs
        exact ih a ha (hargs a ha) s ((Term.mem_subtermList a).mpr hsa)
  simp only [FDatabase.holdsAll, List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true,
    decide_eq_true_eq]
  exact hrec u hu

/-- `matchQuery` with the join switched on by `held`. -/
def matchQueryHeld (d : FDatabase) (held : Bool) (q : Query) : List Env :=
  if d.eqsReflB then matchJoin d q d.valueTerms held [] (Query.freeVars q [])
  else matchQueryPruned d q

theorem matchQueryHeld_eq (d : FDatabase) (held : Bool)
    (hheld : held = true → ∀ u ∈ d.valueTerms, d.holdsAll [u] = true) (q : Query) :
    matchQueryHeld d held q = matchQuery d q := by
  unfold matchQueryHeld
  split
  · rename_i hd
    rw [matchJoin_eq d ((FDatabase.eqsReflB_iff d).mp hd) q d.valueTerms held hheld
      _ [] (fun _ _ h => by simp at h)]
    exact matchQueryPruned_eq d q
  · exact matchQueryPruned_eq d q

def matchQueryFast (d : FDatabase) (q : Query) : List Env :=
  matchQueryHeld d d.childrenRecordedB q

@[csimp] theorem matchQuery_eq_fast : @matchQuery = @matchQueryFast := by
  funext d q
  exact (matchQueryHeld_eq d _ (fun h u hu =>
    holdsAll_of_childrenRecorded h (FDatabase.mem_terms_of_mem_valueTerms hu)) q).symm

def fireRule (d acc : FDatabase) (r : Rule) : FDatabase :=
  (matchQuery d r.query).foldl (fireInto d r) acc

def runRules (R : RulesetName) (d : FDatabase) : FDatabase :=
  (d.rules.filter fun r => r.ruleset == R).foldl (fireRule d) d

/-- `runRules` with the children check made once per round rather than once per rule. -/
def runRulesFast (R : RulesetName) (d : FDatabase) : FDatabase :=
  let held := d.childrenRecordedB
  (d.rules.filter fun r => r.ruleset == R).foldl
    (fun acc r => (matchQueryHeld d held r.query).foldl (fireInto d r) acc) d

@[csimp] theorem runRules_eq_fast : @runRules = @runRulesFast := by
  funext R d
  simp only [runRules, runRulesFast, matchQueryHeld_eq d _ fun h u hu =>
    holdsAll_of_childrenRecorded h (FDatabase.mem_terms_of_mem_valueTerms hu)]
  rfl

/-- `FDatabase.mergeOneOriented` at the diagonal: colliding keys are identical keys. -/
def mergeOneOriented (ts : List Term) (d : FDatabase) (r₁ r₂ : Row) : Option FDatabase :=
  match d.sig.mergeOf r₁.fn with
  | some (.merge body res) =>
    if r₁.fn = r₂.fn && sameTuple ts r₁.args r₂.args
        && d.rows.contains r₁ && d.rows.contains r₂ then
      if FDatabase.noConflict ((d.sig r₁.fn).bind (·.unchangedWidth body)) r₁ r₂ then
        some { d with rows := d.rows.filter fun r => r ≠ r₁ }
      else
        (execActions { d with env := mergeEnv r₂.out r₁.out } body).bind
          fun e => (Expr.evalList e.sig res e.env).map fun vs =>
            let e' := e.addTerm (.app r₂.fn (r₂.args ++ vs))
            { e' with
              rows := (e'.rows.filter fun r => r ≠ r₁).map fun r =>
                if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r,
              env := d.env, rules := d.rules }
    else none
  | _ => none

theorem mergeOneOriented_eq (d e : FDatabase) (r₁ r₂ : Row) :
    mergeOneOriented d.terms e r₁ r₂ = FDatabase.mergeOneOriented (diagonal d) e r₁ r₂ := by
  simp only [mergeOneOriented, FDatabase.mergeOneOriented, FDatabase.congrKeys, sameTuple_eq]
  rfl

/-- Every key is canonical under the diagonal, so no pair is reoriented. -/
theorem swapForCanon_diagonal (d e : FDatabase) (r₁ r₂ : Row) :
    FDatabase.swapForCanon (diagonal d) e r₁ r₂ = false := by
  unfold FDatabase.swapForCanon
  split
  · by_cases hc : FDatabase.congrTuple (diagonal d) r₁.args r₂.args = true
    · rw [congrTuple_diagonal_imp hc]
      simp
    · simp only [Bool.not_eq_true] at hc
      simp [FDatabase.congrKeys, hc]
  · rfl

/-- `FDatabase.mergeRoundWith` at the diagonal, with no rebuild: nothing is re-keyed. -/
def mergeRoundWith (ts : List Term) (e : FDatabase) : FDatabase :=
  e.rows.foldl (fun acc r₁ =>
    e.rows.foldl (fun acc' r₂ =>
      if r₁ == r₂ then acc'
      else match mergeOneOriented ts acc' r₁ r₂ with
        | some acc'' => acc''
        | none => acc') acc) e

theorem mergeRoundWith_eq (d e : FDatabase) :
    mergeRoundWith d.terms e = FDatabase.mergeRoundWith (diagonal d) e := by
  simp only [mergeRoundWith, FDatabase.mergeRoundWith, FDatabase.mergeOneWith,
    swapForCanon_diagonal, Bool.false_eq_true, if_false, mergeOneOriented_eq]
  rfl

/-- Function merges use structural keys; there is no implicit congruence rebuild. -/
def mergeRound (d : FDatabase) : FDatabase :=
  if !d.hasMergeRow then d else mergeRoundWith d.terms { d with rows := d.rows.dedup }

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
