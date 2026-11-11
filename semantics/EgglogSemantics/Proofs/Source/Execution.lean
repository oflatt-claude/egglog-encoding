import EgglogSemantics.Proofs.Source.Domain
import EgglogSemantics.Source.Names
import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Proofs.StatePreservation

/-! Execution properties of the constructor source fragment. Scoped rule heads use
arbitrary constructor names; the domain's union condition prevents literal unions. These
facts are independent of either compiler or proof annotations. -/

namespace Egglog

mutual
/-- **A head an expression applies is one of its `Expr.ctors`.** `Expr.fns` deduplicates and
`Expr.ctors` carries arities; the two name the same heads. -/
theorem Expr.exists_ctor_of_mem_fns : ∀ {e : Expr} {g : FnName}, g ∈ e.fns →
    ∃ k, (g, k) ∈ e.ctors
  | .lit _, _, hg => absurd hg (by simp [Expr.fns])
  | .var _, _, hg => absurd hg (by simp [Expr.fns])
  | .app f args, g, hg => by
      rw [Expr.fns, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨args.length, by rw [Expr.ctors]; exact List.mem_cons_self⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_cons_of_mem _ hk⟩
  | .min a b, g, hg => by
      rw [Expr.fns] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctors]; exact List.mem_append_right _ hk⟩
@[inherit_doc Expr.exists_ctor_of_mem_fns]
theorem Expr.exists_ctorList_of_mem_fnsList : ∀ {es : List Expr} {g : FnName},
    g ∈ Expr.fnsList es → ∃ k, (g, k) ∈ Expr.ctorsList es
  | [], _, hg => absurd hg (by simp [Expr.fnsList])
  | e :: es, g, hg => by
      rw [Expr.fnsList] at hg
      rcases List.mem_union_iff.mp hg with hg' | hg'
      · obtain ⟨k, hk⟩ := Expr.exists_ctor_of_mem_fns hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_left _ hk⟩
      · obtain ⟨k, hk⟩ := Expr.exists_ctorList_of_mem_fnsList hg'
        exact ⟨k, by rw [Expr.ctorsList]; exact List.mem_append_right _ hk⟩
end

/-- Constructor uses of a schedule whose rules occur in the program occur in the program. -/
theorem mem_program_ctors {Q : Program} {S : Schedule} (hs : S.rules ⊆ Q.rules)
    {p : FnName × Nat} (hp : p ∈ S.ctors) : p ∈ Q.ctors := by
  rw [Program.ctors, List.mem_dedup]
  obtain ⟨r, hr, hp⟩ := List.mem_flatMap.mp hp
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hs hr, hp⟩)

/-- No literal occurs in `t`. -/
def Term.LitFree (t : Term) : Prop := ∀ s ∈ t.subterms, ¬ s.isLit

theorem Term.litFree_app {f : FnName} {args : List Term} :
    Term.LitFree (.app f args) ↔ ∀ a ∈ args, Term.LitFree a := by
  simp only [Term.LitFree, Term.subterms_app, Set.mem_insert_iff, Set.mem_iUnion,
    exists_prop, forall_eq_or_imp]
  constructor
  · rintro ⟨-, h⟩ a ha s hs
    exact h s ⟨a, ha, hs⟩
  · rintro h
    refine ⟨by simp [Term.isLit], ?_⟩
    rintro s ⟨a, ha, hs⟩
    exact h a ha s hs

/-- No term the state holds is a literal. -/
def Database.LitFree (db : Database) : Prop := ∀ t ∈ db.terms, ¬ t.isLit

theorem Database.LitFree.term {db : Database} (hw : db.WF) (h : db.LitFree) {t : Term}
    (ht : t ∈ db.terms) : Term.LitFree t :=
  fun s hs => h s (hw.subtermClosed t ht hs)

theorem Database.empty_litFree : Database.empty.LitFree := by
  intro t ht; exact absurd ht (by simp)

/-! ##### Evaluation of a literal-free expression builds a literal-free term -/

mutual

/-- **A literal-free expression evaluates to a literal-free term**, in an environment whose
bindings are literal-free. Building wraps literal-free arguments, and `min` returns one of
its operands, so nothing an expression computes can introduce a literal. -/
theorem Expr.eval_litFree {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (e : Expr) {t : Term}, e.litFreeB = true → e.eval σ = some t → Term.LitFree t
  | .lit _, _, hl, _ => by simp [Expr.litFreeB] at hl
  | .var v, t, _, he => hσ v t he
  | .app f args, t, hl, he => by
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      exact Term.litFree_app.mpr (Expr.evalList_litFree hσ args hl hts)
  | .min a b, t, hl, he => by
      rw [Expr.litFreeB, Bool.and_eq_true] at hl
      rw [Expr.eval_min, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, hmap⟩ := he
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rcases Term.least_eq_or x y with h | h <;> rw [h]
      · exact Expr.eval_litFree hσ a hl.1 hx
      · exact Expr.eval_litFree hσ b hl.2 hy
@[inherit_doc Expr.eval_litFree]
theorem Expr.evalList_litFree {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Term.LitFree t) :
    ∀ (es : List Expr) {ts : List Term}, Expr.litFreeListB es = true →
      Expr.evalList es σ = some ts → ∀ t ∈ ts, Term.LitFree t
  | [], _, _, he => by
      obtain rfl : _ = _ := Option.some.inj he
      simp
  | e :: es, ts, hl, he => by
      rw [Expr.litFreeListB, Bool.and_eq_true] at hl
      rw [Expr.evalList_cons, Option.bind_eq_some_iff] at he
      obtain ⟨u, hu, hrest⟩ := he
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Expr.eval_litFree hσ e hl.1 hu
      · exact Expr.evalList_litFree hσ es hl.2 hus t ht'

end

theorem Term.LitFree.subterm {t s : Term} (h : t.LitFree) (hs : s ∈ t.subterms) : s.LitFree :=
  fun u hu => h u (hu.trans hs)

theorem Database.LitFree.lookup {db : Database} (hw : db.WF) (h : db.LitFree)
    {σ : Env} (hs : ∀ b ∈ σ, b.2 ∈ db.terms) :
    ∀ v t, Env.lookup v σ = some t → Term.LitFree t := fun v t hv =>
  h.term hw (hs (v, t) (Env.mem_of_lookup hv))

def Action.NoLits (a : Action) : Prop := a.litFreeB = true

def Schedule.NoLits (c : Schedule) : Prop := ∀ r ∈ c.rules, ∀ a ∈ r.actions, a.NoLits

theorem Action.evalTerms_litFree {σ : Env} {a : Action} (hl : a.NoLits)
    (hs : ∀ v t, Env.lookup v σ = some t → t.LitFree) : a.EvalTerms σ Term.LitFree := by
  cases a with
  | expr e => exact fun t ht => Expr.eval_litFree hs e hl ht
  | subsume f es => exact fun t ht => Expr.eval_litFree hs (.app f es) hl ht
  | union a b =>
    have hl' := Bool.and_eq_true_iff.mp hl
    exact ⟨fun t ht => Expr.eval_litFree hs a hl'.1 ht,
      fun t ht => Expr.eval_litFree hs b hl'.2 ht⟩

structure Database.NoLits (db : Database) : Prop where
  terms : db.LitFree

theorem Database.NoLits.runRules {R : List Rule} {db : Database} (hw : db.WF)
    (h : db.NoLits) (hn : ∀ r ∈ R, ∀ a ∈ r.actions, a.NoLits) : (RunRules R db).NoLits := by
  refine ⟨?_⟩
  have hh := RunRules.preserves_evalTerms (R := R) (P := Term.LitFree)
    (fun _ ht _ hsub => ht.subterm hsub) (fun _ ht => h.terms.term hw ht)
    (fun r hr σ hσ a ha => Action.evalTerms_litFree (hn r hr a ha)
      (h.terms.lookup hw hσ.1.mem_terms))
  exact fun t ht => hh t ht t (.refl _)

theorem Schedule.NoLits.of_domain {P : Program} (_hdom : P.Fragment)
    (hlit : P.schedule.litFreeB = true) {S : Schedule} (hs : S.rules ⊆ P.rules) :
    S.NoLits := by
  intro r hr a ha
  exact List.all_eq_true.mp (List.all_eq_true.mp hlit r (hs hr)) a ha

end Egglog
