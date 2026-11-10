import EgglogSemantics.Proofs.Congruence.Writes
import EgglogSemantics.Proofs.Congruence.QueryCorr
import EgglogSemantics.Proofs.Congruence.Invariant

/-! A source run and its compiled run preserve the simulation relation: the firings
correspond through the query correspondence, and the compiled rows of each firing stand to
its source writes as the relation requires. -/

namespace Egglog.Congruence

/-! ### Compiled heads -/

theorem encodeAction_expr (e : Expr) : encodeActionWith {} (.expr e) = encodeBuildWith {} e := rfl

theorem encodeAction_union (a b : Expr) : encodeActionWith {} (.union a b) =
    encodeBuildWith {} a ++ encodeBuildWith {} b ++
      [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))] := rfl

theorem encodeActions_nil : encodeActionsWith {} [] = [] := rfl

theorem encodeActions_cons (a : Action) (as : List Action) :
    encodeActionsWith {} (a :: as) = encodeActionWith {} a ++ encodeActionsWith {} as := by
  simp [encodeActionsWith]

/-- Compiled heads only write rows. -/
theorem encodeBuild_subsumeFree : ∀ e : Expr, Actions.SubsumeFree (encodeBuildWith {} e)
  | .lit _ => by
      rw [build_lit]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; trivial
  | .var _ => by
      rw [build_var]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; trivial
  | .min a b => by
      intro x hx
      simp only [encodeBuildWith, List.mem_append] at hx
      rcases hx with hx | hx
      · exact encodeBuild_subsumeFree a x hx
      · exact encodeBuild_subsumeFree b x hx
  | .app f args => by
      rw [build_app]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact encodeBuildArgs_subsumeFree args x hx
      · simp only [List.mem_singleton] at hx; subst hx; trivial
where
  encodeBuildArgs_subsumeFree : ∀ es : List Expr, Actions.SubsumeFree (encodeBuildArgsWith {} es)
    | [] => by intro a ha; simp [buildArgs_nil] at ha
    | e :: es => by
        rw [buildArgs_cons]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact encodeBuild_subsumeFree e x hx
        · exact encodeBuildArgs_subsumeFree es x hx

theorem encodeAction_subsumeFree (a : Action) : Actions.SubsumeFree (encodeActionWith {} a) := by
  cases a with
  | expr e => exact encodeBuild_subsumeFree e
  | union a b =>
    rw [encodeAction_union]
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | rfl | rfl
    · exact encodeBuild_subsumeFree a x hx
    · exact encodeBuild_subsumeFree b x hx
    · trivial
    · trivial
  | subsume _ _ => intro x hx; simp [encodeActionWith] at hx

theorem encodeActions_subsumeFree (as : List Action) :
    Actions.SubsumeFree (encodeActionsWith {} as) := by
  induction as with
  | nil => intro a ha; simp [encodeActions_nil] at ha
  | cons a as ih =>
    rw [encodeActions_cons]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact encodeAction_subsumeFree a x hx
    · exact ih x hx

theorem encodeRule_subsumeFree (r : Rule) : (encodeRuleWith {} r).SubsumeFree :=
  encodeActions_subsumeFree r.actions

/-! ### Writes depend only on the head's variables -/

mutual

theorem build_writes_agreeOn {σ τ : Env} : ∀ (e : Expr),
    (∀ v ∈ e.vars, Env.lookup v σ = Env.lookup v τ) →
    Action.writes σ (encodeBuildWith {} e) = Action.writes τ (encodeBuildWith {} e)
  | .lit _, _ => rfl
  | .var v, h => by
      rw [build_var, Action.writes_singleton, Action.writes_singleton]
      simp [Action.write, ufRow, Expr.evalList, h v (by simp)]
  | .min a b, h => by
      simp only [encodeBuildWith]
      rw [Action.writes_append, Action.writes_append,
        build_writes_agreeOn a (fun v hv => h v (by simp [hv])),
        build_writes_agreeOn b (fun v hv => h v (by simp [hv]))]
  | .app f args, h => by
      rw [build_app, Action.writes_append, Action.writes_append,
        buildArgs_writes_agreeOn args (by simpa using h), Action.writes_singleton,
        Action.writes_singleton]
      simp only [Action.write, ufRow, Expr.eval_app_ctor, Expr.evalList_cons, Expr.evalList_nil,
        Expr.evalList_agreeOn args (by simpa using h)]

theorem buildArgs_writes_agreeOn {σ τ : Env} : ∀ (es : List Expr),
    (∀ v ∈ Expr.varsList es, Env.lookup v σ = Env.lookup v τ) →
    Action.writes σ (encodeBuildArgsWith {} es) = Action.writes τ (encodeBuildArgsWith {} es)
  | [], _ => rfl
  | e :: es, h => by
      rw [buildArgs_cons, Action.writes_append, Action.writes_append,
        build_writes_agreeOn e (fun v hv => h v (by simp [hv])),
        buildArgs_writes_agreeOn es (fun v hv => h v (by simp [hv]))]

end

theorem action_writes_agreeOn {σ τ : Env} (a : Action)
    (h : ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.writes σ (encodeActionWith {} a) = Action.writes τ (encodeActionWith {} a) := by
  cases a with
  | expr e => exact build_writes_agreeOn e h
  | union a b =>
    have ha : ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ := fun v hv =>
      h v (by simp [Action.vars, hv])
    have hb : ∀ v ∈ b.vars, Env.lookup v σ = Env.lookup v τ := fun v hv =>
      h v (by simp [Action.vars, hv])
    simp only [encodeAction_union, Action.writes_append, Action.writes, Action.write, ufRow,
      Expr.eval_app_ctor, Expr.evalList_cons, Expr.evalList_nil, Expr.eval_min,
      Expr.eval_agreeOn a ha, Expr.eval_agreeOn b hb, build_writes_agreeOn a ha,
      build_writes_agreeOn b hb]
  | subsume _ _ => rfl

theorem actions_writes_agreeOn {σ τ : Env} (as : List Action)
    (h : ∀ a ∈ as, ∀ v ∈ a.vars, Env.lookup v σ = Env.lookup v τ) :
    Action.writes σ (encodeActionsWith {} as) = Action.writes τ (encodeActionsWith {} as) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [encodeActions_cons, Action.writes_append, Action.writes_append,
      action_writes_agreeOn a (h a (by simp)), ih (fun a ha => h a (by simp [ha]))]

/-- A scoped action mentions only variables of the scope. -/
theorem Action.vars_subset_of_scoped {a : Action} {Γ : Scope} (h : a.Scoped Γ) :
    ∀ v ∈ a.vars, v ∈ Γ := by
  cases a with
  | expr e => exact h.2
  | union a b =>
    intro v hv
    rw [Action.vars, List.mem_union_iff] at hv
    exact hv.elim (h.1 v) (h.2 v)
  | subsume f es => exact h

theorem Actions.vars_subset_of_scoped : ∀ {as : List Action} {Γ : Scope},
    Actions.Scoped as Γ → ∀ a ∈ as, ∀ v ∈ a.vars, v ∈ Γ
  | [], _, _ => by simp
  | a :: as, Γ, h => by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Action.vars_subset_of_scoped h.1
      · exact Actions.vars_subset_of_scoped h.2 b hb

/-! ### The compiled rows of a head against its source writes -/

/-- How the compiled rows `V'` of a head stand to its source writes `V`: rows between
terms congruent and held once `V` is asserted and the bindings are held, going down the
term order, with their endpoints' self-loops; every source write derivable from the rows;
and every subterm of a source write a self-loop or inside a binding. The bindings matter
for a `min`: the compiled head writes the self-loop of the operand it does not choose,
which is a bound representative. -/
structure HeadWrites (σ : Env) (V V' : Set (Term × Term)) : Prop where
  uf : ∀ q ∈ V', ∃ k p, q = (ufRowT k p, ufRowT k p)
  down : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → p = k ∨ Term.blt p k = true
  selfLoop : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → selfRow k ∈ V' ∧ selfRow p ∈ V'
  cong : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → ∀ D : Database, V ⊆ D.eqs →
    (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → Cong D k p
  ends : ∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → ∀ D : Database, V ⊆ D.eqs →
    (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → k ∈ D.terms ∧ p ∈ D.terms
  derivable : ∀ q ∈ V, ∀ E : Database,
    (∀ k p, (ufRowT k p, ufRowT k p) ∈ V' → (k, p) ∈ E.eqs) → Cong E q.1 q.2
  covers : ∀ q ∈ V, ∀ u, Term.IsSubterm u q.1 ∨ Term.IsSubterm u q.2 →
    selfRow u ∈ V' ∨ ∃ v w, Env.lookup v σ = some w ∧ Term.IsSubterm u w

theorem HeadWrites.empty (σ : Env) : HeadWrites σ ∅ ∅ where
  uf := by simp
  down := by simp
  selfLoop := by simp
  cong := by simp
  ends := by simp
  derivable := by simp
  covers := by simp

theorem HeadWrites.union {σ : Env} {V₁ V₁' V₂ V₂' : Set (Term × Term)}
    (h₁ : HeadWrites σ V₁ V₁') (h₂ : HeadWrites σ V₂ V₂') :
    HeadWrites σ (V₁ ∪ V₂) (V₁' ∪ V₂') where
  uf := fun q hq => hq.elim (h₁.uf q) (h₂.uf q)
  down := fun k p hq => hq.elim (h₁.down k p) (h₂.down k p)
  selfLoop := fun k p hq => hq.elim
    (fun hq => ⟨Or.inl (h₁.selfLoop k p hq).1, Or.inl (h₁.selfLoop k p hq).2⟩)
    (fun hq => ⟨Or.inr (h₂.selfLoop k p hq).1, Or.inr (h₂.selfLoop k p hq).2⟩)
  cong := fun k p hq D hD hσ => hq.elim
    (fun hq => h₁.cong k p hq D (Set.subset_union_left.trans hD) hσ)
    (fun hq => h₂.cong k p hq D (Set.subset_union_right.trans hD) hσ)
  ends := fun k p hq D hD hσ => hq.elim
    (fun hq => h₁.ends k p hq D (Set.subset_union_left.trans hD) hσ)
    (fun hq => h₂.ends k p hq D (Set.subset_union_right.trans hD) hσ)
  derivable := fun q hq E hE => hq.elim
    (fun hq => h₁.derivable q hq E fun k p hkp => hE k p (Or.inl hkp))
    (fun hq => h₂.derivable q hq E fun k p hkp => hE k p (Or.inr hkp))
  covers := fun q hq u hu => hq.elim
    (fun hq => (h₁.covers q hq u hu).imp_left Or.inl)
    (fun hq => (h₂.covers q hq u hu).imp_left Or.inr)

/-- A source write's endpoints are held once it is asserted. -/
theorem mem_terms_of_mem_eqs {D : Database} {q : Term × Term} (hq : q ∈ D.eqs) :
    q.1 ∈ D.terms ∧ q.2 ∈ D.terms :=
  ⟨⟨q, hq, Or.inl (Term.self_mem_subterms _)⟩, ⟨q, hq, Or.inr (Term.self_mem_subterms _)⟩⟩

theorem subterm_mem_terms {D : Database} {t u : Term} (ht : t ∈ D.terms) (hu : Term.IsSubterm u t) :
    u ∈ D.terms := D.subtermClosed t ht hu

/-- The rows a build writes, relative to its value: self-loops of subterms of the value or
of bindings, including the value's own, covering every subterm not inside a binding. -/
theorem build_rows {σ : Env} {e : Expr} (ho : e.MinOverVars)
    (hb : ∀ v ∈ e.vars, (Env.lookup v σ).isSome) {t : Term} (ht : e.eval σ = some t)
    {V' : Set (Term × Term)} (hV' : Action.writes σ (encodeBuildWith {} e) = some V') :
    (∀ q ∈ V', ∃ u, q = selfRow u ∧ (Term.IsSubterm u t ∨ ∃ v, Env.lookup v σ = some u)) ∧
      selfRow t ∈ V' ∧
      ∀ u, Term.IsSubterm u t →
        selfRow u ∈ V' ∨ ∃ v w, Env.lookup v σ = some w ∧ Term.IsSubterm u w := by
  obtain ⟨W, hW, hmem⟩ := build_writes e ho hb
  rw [hW] at hV'
  obtain rfl := Option.some.inj hV'
  refine ⟨fun q hq => ?_, (hmem _).mpr ⟨t, BuildTerm.self ho ht, rfl⟩, fun u hu => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (hmem q).mp hq
    exact ⟨u, rfl, hu.subterm_or_bound ho ht⟩
  · rcases subterm_build e ho ht hu with hbt | ⟨v, _, w, hw, huw⟩
    · exact Or.inl ((hmem _).mpr ⟨u, hbt, rfl⟩)
    · exact Or.inr ⟨v, w, hw, huw⟩

theorem mem_terms_of_subterm_eq {D : Database} {t u : Term} {q : Term × Term} (hq : q ∈ D.eqs)
    (ht : t = q.1 ∨ t = q.2) (hu : Term.IsSubterm u t) : u ∈ D.terms := by
  rcases ht with rfl | rfl
  · exact subterm_mem_terms (mem_terms_of_mem_eqs hq).1 hu
  · exact subterm_mem_terms (mem_terms_of_mem_eqs hq).2 hu

/-- The compiled rows of a source action. -/
theorem action_headWrites {σ : Env} {a : Action} (ho : a.MinOverVars) (hsf : a.SubsumeFree)
    (hb : ∀ v ∈ a.vars, (Env.lookup v σ).isSome) {V : Set (Term × Term)}
    (hV : a.write σ = some V) :
    ∃ V', Action.writes σ (encodeActionWith {} a) = some V' ∧ HeadWrites σ V V' := by
  cases a with
  | expr e =>
    rw [Action.write] at hV
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hV
    rw [encodeAction_expr]
    obtain ⟨W, hW, _⟩ := build_writes e ho hb
    obtain ⟨hrows, hself, hcov⟩ := build_rows ho hb ht hW
    refine ⟨W, hW, ?_⟩
    have hpair : ∀ k p, (ufRowT k p, ufRowT k p) ∈ W →
        k = p ∧ (Term.IsSubterm k t ∨ ∃ v, Env.lookup v σ = some k) := by
      intro k p hkp
      obtain ⟨u, heq, hu⟩ := hrows _ hkp
      obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
      exact ⟨rfl, hu⟩
    -- A build term is held once the value is asserted and the bindings are held.
    have hheld : ∀ k, (Term.IsSubterm k t ∨ ∃ v, Env.lookup v σ = some k) → ∀ D : Database,
        {(t, t)} ⊆ D.eqs → (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → k ∈ D.terms := by
      intro k hk D hD hσ
      rcases hk with hk | ⟨v, hv⟩
      · exact mem_terms_of_subterm_eq (hD rfl) (Or.inl rfl) hk
      · exact hσ v k hv
    refine ⟨fun q hq => ?_, fun k p hkp => ?_, fun k p hkp => ?_, fun k p hkp D hD hσ => ?_,
      fun k p hkp D hD hσ => ?_, fun q hq E hE => ?_, fun q hq u hu => ?_⟩
    · obtain ⟨u, rfl, _⟩ := hrows q hq
      exact ⟨u, u, rfl⟩
    · exact Or.inl (hpair k p hkp).1.symm
    · obtain ⟨rfl, _⟩ := hpair k p hkp
      exact ⟨hkp, hkp⟩
    · obtain ⟨rfl, hk⟩ := hpair k p hkp
      exact Database.toCong (hheld k hk D hD hσ)
    · obtain ⟨rfl, hk⟩ := hpair k p hkp
      exact ⟨hheld k hk D hD hσ, hheld k hk D hD hσ⟩
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact .direct (hE t t hself)
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hcov u (hu.elim id id)
  | union a b =>
    obtain ⟨hoa, hob⟩ := Action.minOverVars_union ho
    rw [Action.write] at hV
    obtain ⟨t₁, ht₁, hV⟩ := Option.bind_eq_some_iff.mp hV
    obtain ⟨t₂, ht₂, hV⟩ := Option.bind_eq_some_iff.mp hV
    split at hV
    · cases hV
    · obtain rfl := Option.some.inj hV
      have hba : ∀ v ∈ a.vars, (Env.lookup v σ).isSome := fun v hv =>
        hb v (by simp [Action.vars, hv])
      have hbb : ∀ v ∈ b.vars, (Env.lookup v σ).isSome := fun v hv =>
        hb v (by simp [Action.vars, hv])
      obtain ⟨W₁, hW₁, _⟩ := build_writes a hoa hba
      obtain ⟨W₂, hW₂, _⟩ := build_writes b hob hbb
      obtain ⟨hrows₁, hself₁, hcov₁⟩ := build_rows hoa hba ht₁ hW₁
      obtain ⟨hrows₂, hself₂, hcov₂⟩ := build_rows hob hbb ht₂ hW₂
      set m := Term.least t₁ t₂ with hm
      have hmin : (Expr.min a b).eval σ = some m := by
        rw [Expr.eval_min, ht₁, Option.bind_some, ht₂, Option.map_some]
      have hpair : Action.writes σ [.expr (ufRow a (.min a b)), .expr (ufRow b (.min a b))] =
          some ({(ufRowT t₁ m, ufRowT t₁ m)} ∪ ({(ufRowT t₂ m, ufRowT t₂ m)} ∪ ∅)) := by
        simp [Action.writes, Action.write, ufRow, Expr.evalList, ht₁, ht₂, hmin]
      set P : Set (Term × Term) :=
        {(ufRowT t₁ m, ufRowT t₁ m)} ∪ ({(ufRowT t₂ m, ufRowT t₂ m)} ∪ ∅) with hP
      have hPmem : ∀ q, q ∈ P ↔
          q = (ufRowT t₁ m, ufRowT t₁ m) ∨ q = (ufRowT t₂ m, ufRowT t₂ m) := by
        intro q
        rw [hP]
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
      refine ⟨W₁ ∪ W₂ ∪ P, ?_, ?_⟩
      · rw [encodeAction_union, Action.writes_append, Action.writes_append, hW₁, Option.bind_some,
          hW₂, Option.map_some, Option.bind_some, hpair, Option.map_some]
      have hm_or : m = t₁ ∨ m = t₂ := Term.least_eq_or t₁ t₂
      have hselfm : selfRow m ∈ W₁ ∪ W₂ := by
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact Or.inl hself₁
        · exact Or.inr hself₂
      have hdown₁ : m = t₁ ∨ Term.blt m t₁ = true := by
        rw [Term.least_eq_ite] at hm
        by_cases h12 : Term.blt t₁ t₂ = true
        · rw [if_pos h12] at hm; exact Or.inl hm
        · rw [if_neg h12] at hm
          rcases eq_or_ne t₁ t₂ with heq | hne
          · exact Or.inl (hm.trans heq.symm)
          · rcases Term.blt_total t₁ t₂ hne with h | h
            · exact (h12 h).elim
            · exact Or.inr (hm ▸ h)
      have hdown₂ : m = t₂ ∨ Term.blt m t₂ = true := by
        rw [Term.least_eq_ite] at hm
        by_cases h12 : Term.blt t₁ t₂ = true
        · rw [if_pos h12] at hm; exact Or.inr (hm ▸ h12)
        · rw [if_neg h12] at hm; exact Or.inl hm
      -- Rows of the builds: self-loops of subterms of an endpoint, or of a binding.
      have hW : ∀ k p, (ufRowT k p, ufRowT k p) ∈ W₁ ∪ W₂ →
          k = p ∧ (Term.IsSubterm k t₁ ∨ Term.IsSubterm k t₂ ∨
            ∃ v, Env.lookup v σ = some k) := by
        intro k p hkp
        rcases hkp with hkp | hkp
        · obtain ⟨u, heq, hu⟩ := hrows₁ _ hkp
          obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          exact ⟨rfl, hu.imp_right Or.inr⟩
        · obtain ⟨u, heq, hu⟩ := hrows₂ _ hkp
          obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          exact ⟨rfl, Or.inr hu⟩
      have hendD : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs →
          (∀ v w, Env.lookup v σ = some w → w ∈ D.terms) → ∀ u,
          Term.IsSubterm u t₁ ∨ Term.IsSubterm u t₂ ∨ (∃ v, Env.lookup v σ = some u) →
          u ∈ D.terms := by
        intro D hD hσ u hu
        rcases hu with hu | hu | ⟨v, hv⟩
        · exact mem_terms_of_subterm_eq (hD rfl) (Or.inl rfl) hu
        · exact mem_terms_of_subterm_eq (hD rfl) (Or.inr rfl) hu
        · exact hσ v u hv
      have hmD : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs → m ∈ D.terms := by
        intro D hD
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact (mem_terms_of_mem_eqs (hD rfl)).1
        · exact (mem_terms_of_mem_eqs (hD rfl)).2
      have hcongm : ∀ D : Database, {(t₁, t₂)} ⊆ D.eqs → Cong D t₁ m ∧ Cong D t₂ m := by
        intro D hD
        have h12 : Cong D t₁ t₂ := .direct (hD rfl)
        rcases hm_or with hm' | hm' <;> rw [hm']
        · exact ⟨h12.trans h12.symm, h12.symm⟩
        · exact ⟨h12, h12.symm.trans h12⟩
      refine ⟨fun q hq => ?_, fun k p hkp => ?_, fun k p hkp => ?_, fun k p hkp D hD hσ => ?_,
        fun k p hkp D hD hσ => ?_, fun q hq E hE => ?_, fun q hq u hu => ?_⟩
      · rcases hq with hq | hq
        · rcases hq with hq | hq
          · obtain ⟨u, rfl, _⟩ := hrows₁ q hq; exact ⟨u, u, rfl⟩
          · obtain ⟨u, rfl, _⟩ := hrows₂ q hq; exact ⟨u, u, rfl⟩
        · rcases (hPmem q).mp hq with rfl | rfl
          · exact ⟨t₁, m, rfl⟩
          · exact ⟨t₂, m, rfl⟩
      · rcases hkp with hkp | hkp
        · exact Or.inl (hW k p hkp).1.symm
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact hdown₁
          · exact hdown₂
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, _⟩ := hW k p hkp
          exact ⟨Or.inl hkp, Or.inl hkp⟩
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact ⟨Or.inl (Or.inl hself₁), Or.inl hselfm⟩
          · exact ⟨Or.inl (Or.inr hself₂), Or.inl hselfm⟩
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, hk⟩ := hW k p hkp
          exact Database.toCong (hendD D hD hσ k hk)
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact (hcongm D hD).1
          · exact (hcongm D hD).2
      · rcases hkp with hkp | hkp
        · obtain ⟨rfl, hk⟩ := hW k p hkp
          exact ⟨hendD D hD hσ k hk, hendD D hD hσ k hk⟩
        · rcases (hPmem _).mp hkp with heq | heq <;>
            obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
          · exact ⟨(mem_terms_of_mem_eqs (hD rfl)).1, hmD D hD⟩
          · exact ⟨(mem_terms_of_mem_eqs (hD rfl)).2, hmD D hD⟩
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        have h₁ : (t₁, m) ∈ E.eqs := hE t₁ m (Or.inr ((hPmem _).mpr (Or.inl rfl)))
        have h₂ : (t₂, m) ∈ E.eqs := hE t₂ m (Or.inr ((hPmem _).mpr (Or.inr rfl)))
        exact (Cong.direct h₁).trans (Cong.direct h₂).symm
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        rcases hu with hu | hu
        · exact (hcov₁ u hu).imp_left fun h => Or.inl (Or.inl h)
        · exact (hcov₂ u hu).imp_left fun h => Or.inl (Or.inr h)
  | subsume _ _ => simp [Action.SubsumeFree, Action.monotoneB] at hsf

/-- The compiled rows of a head. -/
theorem actions_headWrites {σ : Env} : ∀ {as : List Action}, Actions.MinOverVars as →
    Actions.SubsumeFree as → (∀ a ∈ as, ∀ v ∈ a.vars, (Env.lookup v σ).isSome) →
    ∀ {V : Set (Term × Term)}, Action.writes σ as = some V →
    ∃ V', Action.writes σ (encodeActionsWith {} as) = some V' ∧ HeadWrites σ V V'
  | [], _, _, _, V, hV => by
      rw [Action.writes] at hV
      obtain rfl := Option.some.inj hV
      exact ⟨∅, rfl, HeadWrites.empty σ⟩
  | a :: as, ho, hsf, hb, V, hV => by
      rw [Action.writes] at hV
      obtain ⟨V₁, hV₁, hV⟩ := Option.bind_eq_some_iff.mp hV
      obtain ⟨V₂, hV₂, rfl⟩ := Option.map_eq_some_iff.mp hV
      obtain ⟨W₁, hW₁, hh₁⟩ := action_headWrites (ho a (by simp)) (hsf a (by simp))
        (hb a (by simp)) hV₁
      obtain ⟨W₂, hW₂, hh₂⟩ := actions_headWrites (fun x hx => ho x (by simp [hx]))
        (fun x hx => hsf x (by simp [hx])) (fun x hx => hb x (by simp [hx])) hV₂
      refine ⟨W₁ ∪ W₂, ?_, hh₁.union hh₂⟩
      rw [encodeActions_cons, Action.writes_append, hW₁, Option.bind_some, hW₂, Option.map_some]

/-! ### The firings of a run -/

theorem mem_runWrites_iff {R : List Rule} {db : Database} {q : Term × Term} :
    q ∈ RunWrites R db ↔ ∃ r ∈ R, ∃ σ W, QueryMatches db r.query σ ∧
      Action.writes σ r.actions = some W ∧ q ∈ W := by
  unfold RunWrites
  rw [Set.mem_sUnion]
  constructor
  · rintro ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩; exact ⟨r, hr, σ, W, hσ, hW, hq⟩
  · rintro ⟨r, hr, σ, W, hσ, hW, hq⟩; exact ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩

theorem writes_subset_runWrites' {R : List Rule} {db : Database} {r : Rule} (hr : r ∈ R)
    {σ : Env} (hσ : QueryMatches db r.query σ) {W : Set (Term × Term)}
    (hW : Action.writes σ r.actions = some W) : W ⊆ RunWrites R db :=
  fun _ hq => mem_runWrites_iff.mpr ⟨r, hr, σ, W, hσ, hW, hq⟩

/-- The conditions on a source rule the round correspondence uses. -/
structure RuleOk (r : Rule) : Prop where
  query : QueryOk r.query
  keyed : Query.VarsKeyed r.query
  heads : r.HeadScoped
  minOverVars : Actions.MinOverVars r.actions
  subsumeFree : r.SubsumeFree

theorem encodeRule_query (r : Rule) :
    (encodeRuleWith {} r).query = (encodeQueryWith {} r.query 0).1 := rfl

theorem encodeRule_actions (r : Rule) :
    (encodeRuleWith {} r).actions = encodeActionsWith {} r.actions := rfl

/-- A firing of a source rule, with its source writes and compiled rows. -/
structure Firing (src d : Database) (R : List Rule) (r : Rule) (σ : Env)
    (V V' : Set (Term × Term)) : Prop where
  mem : r ∈ R
  qmatch : QueryMatches src r.query σ
  writes : Action.writes σ r.actions = some V
  compiled : Action.writes σ (encodeActionsWith {} r.actions) = some V'
  head : HeadWrites σ V V'
  src_sub : V ⊆ RunWrites R src
  tgt_sub : V' ⊆ RunWrites (R.map (encodeRuleWith {})) d

variable {src d : Database}

/-- Every source firing at a canonical state has a compiled firing with the same source
bindings. -/
theorem firing_data (h : Rel src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {r : Rule} (hr : r ∈ R) {σ : Env} (hσ : QueryMatches src r.query σ) :
    ∃ V V', Firing src d R r σ V V' := by
  have hok := hR r hr
  obtain ⟨V, hV⟩ := hfire r hr σ hσ
  have hbound : ∀ a ∈ r.actions, ∀ v ∈ a.vars, (Env.lookup v σ).isSome := by
    intro a ha v hv
    apply Env.lookup_isSome_iff_mem_dom.mpr
    exact hσ.1.1.mem_iff.mpr (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  obtain ⟨V', hV', hhead⟩ := actions_headWrites hok.minOverVars hok.subsumeFree hbound hV
  obtain ⟨σ', hσ', hag⟩ := fire_complete h hc hw hok.query hσ
  have hag' : ∀ a ∈ r.actions, ∀ v ∈ a.vars, Env.lookup v σ' = Env.lookup v σ :=
    fun a ha v hv => hag v (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  refine ⟨V, V', hr, hσ, hV, hV', hhead, writes_subset_runWrites' hr hσ hV, ?_⟩
  have hmem : encodeRuleWith {} r ∈ R.map (encodeRuleWith {}) := List.mem_map_of_mem hr
  have hW' : Action.writes σ' (encodeRuleWith {} r).actions = some V' := by
    rw [encodeRule_actions, actions_writes_agreeOn r.actions hag']
    exact hV'
  exact writes_subset_runWrites' hmem hσ' hW'

/-- Every compiled write comes from a source firing. -/
theorem firing_of_compiled (h : Rel src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {q : Term × Term} (hq : q ∈ RunWrites (R.map (encodeRuleWith {})) d) :
    ∃ r σ V V', Firing src d R r σ V V' ∧ q ∈ V' := by
  obtain ⟨r', hr', σ', W', hσ', hW', hqW⟩ := mem_runWrites_iff.mp hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hok := hR r hr
  rw [encodeRule_query] at hσ'
  obtain ⟨hσ, hag⟩ := fire_sound h hc hw hok.query hok.keyed hσ'
  obtain ⟨V, V', hf⟩ := firing_data h hc hw hR hfire hr hσ
  have hag' : ∀ a ∈ r.actions, ∀ v ∈ a.vars,
      Env.lookup v (restrict (Query.vars r.query) σ') = Env.lookup v σ' :=
    fun a ha v hv => hag v (Actions.vars_subset_of_scoped hok.heads a ha v hv)
  have hV' : Action.writes σ' (encodeActionsWith {} r.actions) = some V' := by
    rw [← actions_writes_agreeOn r.actions hag']
    exact hf.compiled
  rw [encodeRule_actions, hV'] at hW'
  obtain rfl := Option.some.inj hW'
  exact ⟨r, _, V, V', hf, hqW⟩

/-- Every source write comes from a firing with compiled rows. -/
theorem firing_of_source (h : Rel src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    {q : Term × Term} (hq : q ∈ RunWrites R src) :
    ∃ r σ V V', Firing src d R r σ V V' ∧ q ∈ V := by
  obtain ⟨r, hr, σ, W, hσ, hW, hqW⟩ := mem_runWrites_iff.mp hq
  obtain ⟨V, V', hf⟩ := firing_data h hc hw hR hfire hr hσ
  rw [hf.writes] at hW
  obtain rfl := Option.some.inj hW
  exact ⟨r, σ, V, V', hf, hqW⟩

theorem compiled_rules_subsumeFree (R : List Rule) :
    ∀ r ∈ R.map (encodeRuleWith {}), r.SubsumeFree := by
  intro r hr
  obtain ⟨r₀, _, rfl⟩ := List.mem_map.mp hr
  exact encodeRule_subsumeFree r₀

/-- A source run and its compiled run preserve the relation. -/
theorem run_rel (h : Rel src d) (hc : Canon d) (hw : src.WF) {R : List Rule}
    (hR : ∀ r ∈ R, RuleOk r)
    (hfire : ∀ r ∈ R, ∀ σ, QueryMatches src r.query σ → ∃ W, Action.writes σ r.actions = some W)
    (havoid : ∀ t ∈ (RunRules R src).terms, ¬ Term.Mentions ufName t) :
    Rel (RunRules R src) (RunRules (R.map (encodeRuleWith {})) d) := by
  have hsf : ∀ r ∈ R, r.SubsumeFree := fun r hr => (hR r hr).subsumeFree
  set src' := RunRules R src with hsrc'
  set d' := RunRules (R.map (encodeRuleWith {})) d with hd'
  have hseqs : src'.eqs = src.eqs ∪ RunWrites R src := by rw [hsrc', RunRules.eq_addEqs hsf]; rfl
  have hssub : src'.subsumed = src.subsumed := by rw [hsrc', RunRules.eq_addEqs hsf]; rfl
  have hdeqs : d'.eqs = d.eqs ∪ RunWrites (R.map (encodeRuleWith {})) d := by
    rw [hd', RunRules.eq_addEqs (compiled_rules_subsumeFree R)]; rfl
  have hdsub : d'.subsumed = d.subsumed := by
    rw [hd', RunRules.eq_addEqs (compiled_rules_subsumeFree R)]; rfl
  have hdmono : d.eqs ⊆ d'.eqs := hdeqs ▸ Set.subset_union_left
  have hsmono : src.eqs ⊆ src'.eqs := hseqs ▸ Set.subset_union_left
  have hsrcW : RunWrites R src ⊆ src'.eqs := hseqs ▸ Set.subset_union_right
  have hdW : RunWrites (R.map (encodeRuleWith {})) d ⊆ d'.eqs := hdeqs ▸ Set.subset_union_right
  -- A new row of the compiled state comes from a firing.
  have hrow : ∀ k p, Row d' k p → Row d k p ∨
      ∃ r σ V V', Firing src d R r σ V V' ∧ (ufRowT k p, ufRowT k p) ∈ V' := by
    intro k p hr
    have : (ufRowT k p, ufRowT k p) ∈ d.eqs ∪ RunWrites (R.map (encodeRuleWith {})) d :=
      hdeqs ▸ hr
    rcases this with hr | hr
    · exact Or.inl hr
    · exact Or.inr (firing_of_compiled h hc hw hR hfire hr)
  have hufOnly : UfOnly d' := by
    intro q hq
    have : q ∈ d.eqs ∪ RunWrites (R.map (encodeRuleWith {})) d := hdeqs ▸ hq
    rcases this with hq | hq
    · exact h.ufOnly q hq
    · obtain ⟨r, σ, V, V', hf, hqV⟩ := firing_of_compiled h hc hw hR hfire hq
      exact hf.head.uf q hqV
  have hdiag : d'.Diag := by
    intro q hq
    obtain ⟨k, p, rfl⟩ := hufOnly q hq
    rfl
  -- The bindings of a firing are source representatives, held before and after the round.
  have hbind : ∀ {r : Rule} {σ : Env} {V V' : Set (Term × Term)}, Firing src d R r σ V V' →
      ∀ v w, Env.lookup v σ = some w → w ∈ src'.terms := fun hf v w hvw =>
    Database.mem_terms_of_eqs hsmono (hf.qmatch.1.2 (v, w) (Env.mem_of_lookup hvw)).1
  have hkeys_sub : ∀ k p, Row d' k p → k ∈ src'.terms := by
    intro k p hr
    rcases hrow k p hr with hr | ⟨r, σ, V, V', hf, hkp⟩
    · exact Database.mem_terms_of_eqs hsmono (h.key_mem_src hr.mem_keys)
    · exact (hf.head.ends k p hkp src' (hf.src_sub.trans hsrcW) (hbind hf)).1
  have hself : ∀ k p, Row d' k p → Row d' k k ∧ Row d' p p := by
    intro k p hr
    rcases hrow k p hr with hr | ⟨r, σ, V, V', hf, hkp⟩
    · exact ⟨(h.selfLoop k p hr).1.mono hdmono, (h.selfLoop k p hr).2.mono hdmono⟩
    · obtain ⟨h₁, h₂⟩ := hf.head.selfLoop k p hkp
      exact ⟨hdW (hf.tgt_sub h₁), hdW (hf.tgt_sub h₂)⟩
  have hkeys : Keys d' = src'.terms := by
    apply Set.Subset.antisymm
    · rintro k ⟨p, hr⟩
      exact hkeys_sub k p hr
    · intro t ht
      obtain ⟨q, hq, hsub⟩ := ht
      have : q ∈ src.eqs ∪ RunWrites R src := hseqs ▸ hq
      rcases this with hq | hq
      · exact Keys.mono hdmono (h.mem_keys_of_src ⟨q, hq, hsub⟩)
      · obtain ⟨r, σ, V, V', hf, hqV⟩ := firing_of_source h hc hw hR hfire hq
        rcases hf.head.covers q hqV t hsub with hself' | ⟨v, w, hw', htw⟩
        · exact ⟨t, hdW (hf.tgt_sub hself')⟩
        · have hwsrc : w ∈ src.terms := (hf.qmatch.1.2 (v, w) (Env.mem_of_lookup hw')).1
          exact Keys.mono hdmono (h.mem_keys_of_src (src.subtermClosed w hwsrc htw))
  have hends : EndsFree d' := fun k p hr =>
    ⟨havoid k (hkeys ▸ hr.mem_keys), havoid p (hkeys ▸ (hself k p hr).2.mem_keys)⟩
  have hcong : ∀ a b, Cong src' a b ↔ Cong (view d') a b := by
    intro a b
    constructor
    · intro hab
      refine Cong.replay (D := src') (E := view d') (fun q hq => ?_) hab
      have : q ∈ src.eqs ∪ RunWrites R src := hseqs ▸ hq
      rcases this with hq | hq
      · exact Cong.mono_eqs (view_mono hdmono) ((h.cong q.1 q.2).mp (.direct hq))
      · obtain ⟨r, σ, V, V', hf, hqV⟩ := firing_of_source h hc hw hR hfire hq
        exact hf.head.derivable q hqV (view d') fun k p hkp => hdW (hf.tgt_sub hkp)
    · intro hab
      refine Cong.replay (D := view d') (E := src') (fun q hq => ?_) hab
      rcases hrow q.1 q.2 hq with hr | ⟨r, σ, V, V', hf, hkp⟩
      · exact Cong.mono_eqs hsmono ((h.cong q.1 q.2).mpr hr.cong_view)
      · exact hf.head.cong q.1 q.2 hkp src' (hf.src_sub.trans hsrcW) (hbind hf)
  exact {
    diag := hdiag
    ufOnly := hufOnly
    finite := RunRules.finite_eqs h.finite _
    marks := by
      intro t ht
      rw [hdsub] at ht
      obtain ⟨k, p, q, heq, hkp, hkq, hpq, hlt⟩ := h.marks t ht
      exact ⟨k, p, q, heq, hkp.mono hdmono, hkq.mono hdmono, hpq.mono hdmono, hlt⟩
    down := by
      intro k p hr
      rcases hrow k p hr with hr | ⟨r, σ, V, V', hf, hkp⟩
      · exact h.down k p hr
      · exact hf.head.down k p hkp
    selfLoop := hself
    keys := hkeys
    avoids := havoid
    cong := hcong
    liveCong := by
      intro k p hr
      by_cases hs : ufRowT k p ∈ d'.subsumed
      · rw [hdsub] at hs
        obtain ⟨k', p', q, heq, hkp, _⟩ := h.marks _ hs
        obtain ⟨rfl, rfl⟩ := ufRowT_inj heq
        have := h.liveCong k p hkp
        exact Cong.mono_eqs (d := liveView d) (e := liveView d')
          (fun q hq => Edge.mono h.diag h.ufOnly h.endsFree hdiag hufOnly hends
            hdmono (hdsub ▸ subset_rfl) hq) this
      · exact (Edge.of_row hdiag hufOnly hends hr hs).cong_liveView
    srcSubsumed := hssub.trans h.srcSubsumed }

end Egglog.Congruence
