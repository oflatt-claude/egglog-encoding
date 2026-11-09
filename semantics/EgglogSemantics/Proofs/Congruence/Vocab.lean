import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Proofs.OrderFinite
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Representatives
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Diagonal

/-! The vocabulary of a source program, and the size of the terms its rounds build: every
reachable term uses the program's names and literals, and from a meaning-stable state the
rounds build terms of bounded size, since every representative is bounded by the
representatives of the stable state. -/

namespace Egglog

/-! ### Literals of a program -/

mutual

/-- The literals occurring in an expression. -/
def Expr.lits : Expr → List Lit
  | .lit l => [l]
  | .var _ => []
  | .app _ args => Expr.litsList args
  | .min a b => a.lits ++ b.lits

def Expr.litsList : List Expr → List Lit
  | [] => []
  | e :: es => e.lits ++ Expr.litsList es

end

def Pattern.lits : Pattern → List Lit
  | .expr e => e.lits
  | .eq a b => a.lits ++ b.lits
  | .ne a b => a.lits ++ b.lits

def Action.lits : Action → List Lit
  | .expr e => e.lits
  | .union a b => a.lits ++ b.lits
  | .subsume f es => (Expr.app f es).lits

def Rule.lits (r : Rule) : List Lit :=
  r.query.flatMap Pattern.lits ++ r.actions.flatMap Action.lits

def Schedule.lits (S : Schedule) : List Lit := S.rules.flatMap Rule.lits

/-- Every literal the program mentions. -/
def Program.lits (P : Program) : List Lit := P.schedule.lits ++ P.check.flatMap Pattern.lits

/-- The constructor names of a program, as a set. -/
def Program.ctorSet (P : Program) : Set FnName := {g | ∃ k, (g, k) ∈ P.ctors}

/-- The literals of a program, as a set. -/
def Program.litSet (P : Program) : Set Lit := {l | l ∈ P.lits}

theorem Program.ctorSet_finite (P : Program) : P.ctorSet.Finite := by
  apply ((List.finite_toSet P.ctors).image Prod.fst).subset
  rintro g ⟨k, hk⟩
  exact ⟨(g, k), hk, rfl⟩

theorem Program.litSet_finite (P : Program) : P.litSet.Finite := List.finite_toSet _

/-- A term over the program's names and literals. -/
abbrev Term.VocabIn (P : Program) (t : Term) : Prop := Term.UsesVocabulary P.ctorSet P.litSet t

theorem Term.VocabIn.subterm {P : Program} {s t : Term} (ht : t.VocabIn P) (hs : s ∈ t.subterms) :
    s.VocabIn P := Term.UsesVocabulary.subterm ht hs

theorem Term.vocabIn_app_iff {P : Program} {f : FnName} {args : List Term} :
    Term.VocabIn P (.app f args) ↔ f ∈ P.ctorSet ∧ ∀ a ∈ args, Term.VocabIn P a := by
  constructor
  · intro h; cases h with | app hf hargs => exact ⟨hf, hargs⟩
  · rintro ⟨hf, hargs⟩; exact .app hf hargs

mutual

/-- Evaluation stays inside the program's vocabulary. -/
theorem Expr.eval_vocab {P : Program} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.VocabIn P t) :
    ∀ (e : Expr) {t : Term}, (∀ fk ∈ e.ctors, fk ∈ P.ctors) → (∀ l ∈ e.lits, l ∈ P.lits) →
      e.eval σ = some t → Term.VocabIn P t
  | .lit l, _, _, hl, he => by
      obtain rfl : _ = _ := Option.some.inj he
      exact .lit (hl l (by simp [Expr.lits]))
  | .var v, t, _, _, he => hσ v t he
  | .app f args, t, hc, hl, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      refine .app ⟨args.length, hc _ (by rw [Expr.ctors]; exact List.mem_cons_self)⟩ ?_
      exact Expr.evalList_vocab hσ args
        (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk))
        (fun l hl' => hl l (by rw [Expr.lits]; exact hl')) hts
  | .min a b, t, hc, hl, he => by
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact Expr.eval_vocab hσ a
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_left _ hk))
          (fun l hl' => hl l (by rw [Expr.lits]; exact List.mem_append_left _ hl')) hx
      · exact Expr.eval_vocab hσ b
          (fun fk hk => hc fk (by rw [Expr.ctors]; exact List.mem_append_right _ hk))
          (fun l hl' => hl l (by rw [Expr.lits]; exact List.mem_append_right _ hl')) hy

theorem Expr.evalList_vocab {P : Program} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.VocabIn P t) :
    ∀ (es : List Expr) {ts : List Term}, (∀ fk ∈ Expr.ctorsList es, fk ∈ P.ctors) →
      (∀ l ∈ Expr.litsList es, l ∈ P.lits) → Expr.evalList es σ = some ts →
      ∀ t ∈ ts, Term.VocabIn P t
  | [], _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hc, hl, he => by
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_vocab hσ e
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_left _ hk))
          (fun l hl' => hl l (by rw [Expr.litsList]; exact List.mem_append_left _ hl')) hu
      · exact Expr.evalList_vocab hσ es
          (fun fk hk => hc fk (by rw [Expr.ctorsList]; exact List.mem_append_right _ hk))
          (fun l hl' => hl l (by rw [Expr.litsList]; exact List.mem_append_right _ hl'))
          hus t ht'

end

/-- The literals of a rule of the program are among the program's. -/
theorem Rule.lits_subset {P : Program} {r : Rule} (hr : r ∈ P.rules) :
    ∀ l ∈ r.lits, l ∈ P.lits := by
  intro l hl
  unfold Program.lits Schedule.lits
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, hl⟩)

theorem Action.lits_subset {P : Program} {r : Rule} (hr : r ∈ P.rules) {a : Action}
    (ha : a ∈ r.actions) : ∀ l ∈ a.lits, l ∈ P.lits := by
  intro l hl
  apply Rule.lits_subset hr
  unfold Rule.lits
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hl⟩)

theorem Action.ctors_subset {P : Program} {r : Rule} (hr : r ∈ P.rules) {a : Action}
    (ha : a ∈ r.actions) : ∀ fk ∈ a.ctors, fk ∈ P.ctors := by
  intro fk hk
  apply mem_program_ctors (S := P.schedule) (fun r hr => hr)
  unfold Schedule.ctors
  exact List.mem_flatMap.mpr ⟨r, hr, List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hk⟩)⟩

theorem Action.evalTerms_vocab {P : Program} {σ : Env} {a : Action}
    (hc : ∀ fk ∈ a.ctors, fk ∈ P.ctors) (hl : ∀ l ∈ a.lits, l ∈ P.lits)
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.VocabIn P t) :
    a.EvalTerms σ (Term.VocabIn P) := by
  cases a with
  | expr e => exact fun t ht => Expr.eval_vocab hσ e hc hl ht
  | subsume f es => exact fun t ht => Expr.eval_vocab hσ (.app f es) hc hl ht
  | union a b =>
    refine ⟨fun t ht => Expr.eval_vocab hσ a ?_ ?_ ht, fun t ht => Expr.eval_vocab hσ b ?_ ?_ ht⟩
    · exact fun fk hk => hc fk (by rw [Action.ctors]; exact List.mem_append_left _ hk)
    · exact fun l hl' => hl l (by rw [Action.lits]; exact List.mem_append_left _ hl')
    · exact fun fk hk => hc fk (by rw [Action.ctors]; exact List.mem_append_right _ hk)
    · exact fun l hl' => hl l (by rw [Action.lits]; exact List.mem_append_right _ hl')

/-- A round of the program's rules keeps every held term in the vocabulary. -/
theorem RunRules.vocab {P : Program} {R : List Rule} {db : Database} (hw : db.WF)
    (hR : ∀ r ∈ R, r ∈ P.rules) (hd : ∀ t ∈ db.terms, Term.VocabIn P t) :
    ∀ t ∈ (RunRules R db).terms, Term.VocabIn P t := by
  apply RunRules.preserves_evalTerms (fun _ ht _ hs => ht.subterm hs) hd
  intro r hr σ hσ a ha
  exact Action.evalTerms_vocab (Action.ctors_subset (hR r hr) ha) (Action.lits_subset (hR r hr) ha)
    fun v t hv => hd t (hw.subtermClosed _ (hσ.1.mem_terms (v, t) (Env.mem_of_lookup hv))
      (Term.self_mem_subterms _))

/-! ### The size of built terms -/

mutual

/-- The node count of an expression. -/
def Expr.size : Expr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .app _ args => 1 + Expr.sizeList args
  | .min a b => 1 + a.size + b.size

def Expr.sizeList : List Expr → Nat
  | [] => 0
  | e :: es => e.size + Expr.sizeList es

end

mutual

/-- A built term is at most the expression's size times the largest binding. -/
theorem Expr.eval_nodeSize_le {σ : Env} {N : Nat}
    (hσ : ∀ v t, Env.lookup v σ = some t → t.nodeSize ≤ N) :
    ∀ (e : Expr) {t : Term}, e.OrderingFree → e.eval σ = some t →
      t.nodeSize ≤ e.size * (N + 1)
  | .lit _, _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp [Expr.size]
  | .var v, t, _, he => by
      have := hσ v t he
      simp only [Expr.size, Nat.one_mul]
      omega
  | .min _ _, _, ho, _ => (Expr.not_orderingFree_min ho).elim
  | .app f args, t, ho, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      have := Expr.evalList_nodeSize_le hσ args (Expr.orderingFree_app ho) hts
      simp only [Expr.size, Term.nodeSize_app]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem Expr.evalList_nodeSize_le {σ : Env} {N : Nat}
    (hσ : ∀ v t, Env.lookup v σ = some t → t.nodeSize ≤ N) :
    ∀ (es : List Expr) {ts : List Term}, Expr.OrderingFreeList es →
      Expr.evalList es σ = some ts → Term.nodeSizeList ts ≤ Expr.sizeList es * (N + 1)
  | [], _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp [Expr.sizeList]
  | e :: es, ts, ho, he => by
      obtain ⟨hoe, hoes⟩ := Expr.orderingFreeList_cons ho
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      have h₁ := Expr.eval_nodeSize_le hσ e hoe hu
      have h₂ := Expr.evalList_nodeSize_le hσ es hoes hus
      simp only [Expr.sizeList, Term.nodeSizeList_cons]
      rw [Nat.add_mul]
      omega

end

/-- The expressions an action evaluates. -/
def Action.exprs : Action → List Expr
  | .expr e => [e]
  | .union a b => [a, b]
  | .subsume f es => [.app f es]

/-- The largest head expression of the program. -/
def Program.headSize (P : Program) : Nat :=
  (P.rules.flatMap fun r => r.actions.flatMap Action.exprs).foldr (fun e acc => max e.size acc) 0

theorem le_foldr_max {α : Type*} (f : α → Nat) : ∀ {l : List α} {x : α}, x ∈ l →
    f x ≤ l.foldr (fun y acc => max (f y) acc) 0
  | [], _, h => by simp at h
  | y :: l, x, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max f h) (Nat.le_max_right _ _)

theorem Expr.size_le_headSize {P : Program} {r : Rule} (hr : r ∈ P.rules) {a : Action}
    (ha : a ∈ r.actions) {e : Expr} (he : e ∈ a.exprs) : e.size ≤ P.headSize :=
  le_foldr_max Expr.size (List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨a, ha, he⟩⟩)

theorem Action.evalTerms_nodeSize {P : Program} {r : Rule} (hr : r ∈ P.rules) {a : Action}
    (ha : a ∈ r.actions) (ho : a.OrderingFree) {σ : Env} {N : Nat}
    (hσ : ∀ v t, Env.lookup v σ = some t → t.nodeSize ≤ N) :
    a.EvalTerms σ fun t => t.nodeSize ≤ P.headSize * (N + 1) := by
  have bound : ∀ e ∈ a.exprs, e.OrderingFree → ∀ t, e.eval σ = some t →
      t.nodeSize ≤ P.headSize * (N + 1) := by
    intro e he hoe t ht
    exact Nat.le_trans (Expr.eval_nodeSize_le hσ e hoe ht)
      (Nat.mul_le_mul_right _ (Expr.size_le_headSize hr ha he))
  cases a with
  | expr e => exact bound e (by simp [Action.exprs]) ho
  | subsume f es => exact bound _ (by simp [Action.exprs]) ho
  | union a b =>
    exact ⟨bound a (by simp [Action.exprs]) ho.1, bound b (by simp [Action.exprs]) ho.2⟩

/-- Representatives of a state with the meaning of `x₀` and all its terms are bounded by
the terms of `x₀`. -/
theorem reps_nodeSize_le {x₀ z : Database} (hr₀ : x₀.HasReps) (hm : z.SameMeaning x₀)
    (hsub : x₀.terms ⊆ z.terms) {N : Nat} (hN : ∀ t ∈ x₀.terms, t.nodeSize ≤ N) :
    ∀ t ∈ z.reps, t.nodeSize ≤ N := by
  intro t ht
  have hc : Cong x₀ t t := (hm.congr t t).mp (Database.toCong ht.1)
  obtain ⟨r, hr, htr⟩ := hr₀ t hc
  have hrz : Cong z r t := (hm.congr r t).mpr htr.symm
  have hnot : ¬ Term.blt r t = true := ht.2 r (hsub hr.1) hrz
  rcases eq_or_ne t r with rfl | hne
  · exact hN t hr.1
  · rcases Term.blt_total t r hne with h | h
    · exact Nat.le_trans (Term.nodeSize_le_of_blt h) (hN r hr.1)
    · exact (hnot h).elim

theorem Actions.orderingFree_of_mem : ∀ {as : List Action}, Actions.OrderingFree as →
    ∀ {a : Action}, a ∈ as → a.OrderingFree
  | [], _, _, h => by simp at h
  | b :: bs, ho, a, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ho.1
      · exact Actions.orderingFree_of_mem ho.2 h

/-- A round from a bounded state with bounded representatives stays bounded. -/
theorem RunRules.nodeSize_le {P : Program} {R : List Rule} {db : Database}
    (hR : ∀ r ∈ R, r ∈ P.rules) (ho : ∀ r ∈ R, Actions.OrderingFree r.actions) {N M : Nat}
    (hreps : ∀ t ∈ db.reps, t.nodeSize ≤ N) (hM : P.headSize * (N + 1) ≤ M)
    (hd : ∀ t ∈ db.terms, t.nodeSize ≤ M) :
    ∀ t ∈ (RunRules R db).terms, t.nodeSize ≤ M := by
  apply RunRules.preserves_evalTerms
    (fun _ ht _ hs => Nat.le_trans (Term.IsSubterm.nodeSize_le hs) ht) hd
  intro r hr σ hσ a ha
  have hoa : a.OrderingFree := Actions.orderingFree_of_mem (ho r hr) ha
  have := Action.evalTerms_nodeSize (hR r hr) ha hoa
    (fun v t hv => hreps t (hσ.1.mem_reps (v, t) (Env.mem_of_lookup hv)))
  cases a with
  | expr e => exact fun t ht => Nat.le_trans (this t ht) hM
  | subsume f es => exact fun t ht => Nat.le_trans (this t ht) hM
  | union a b =>
    exact ⟨fun t ht => Nat.le_trans (this.1 t ht) hM, fun t ht => Nat.le_trans (this.2 t ht) hM⟩

end Egglog
