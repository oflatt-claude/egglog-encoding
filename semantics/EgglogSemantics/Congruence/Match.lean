import EgglogSemantics.Congruence.Correspond

/-!
# Source matches from flattened table queries

The recursion follows the original query and the compiler's left-to-right postorder.
Sound view rows supply both equality and existence of source premises. No annotation,
proof column, or saved flattening tree is used.
-/

namespace Egglog.Congruence

mutual

inductive QueryRead (d : Database) (ρ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : QueryRead d ρ (.lit l) (.lit l)
  | var {v : Var} {i : Term} : Env.lookup v ρ = some i → QueryRead d ρ (.var v) i
  | app {f : FnName} {args : List Expr} {es : List Term} {i : Term} :
      QueryReadList d ρ args es → d.Out (viewName f) es [i] →
      QueryRead d ρ (.app f args) i

inductive QueryReadList (d : Database) (ρ : Env) : List Expr → List Term → Prop where
  | nil : QueryReadList d ρ [] []
  | cons {a : Expr} {i : Term} {as : List Expr} {is : List Term} :
      QueryRead d ρ a i → QueryReadList d ρ as is → QueryReadList d ρ (a :: as) (i :: is)

end

inductive PatternRead (d : Database) (ρ : Env) : Pattern → Prop where
  | expr {e : Expr} {i : Term} : QueryRead d ρ e i → PatternRead d ρ (.expr e)
  | eq {e₁ e₂ : Expr} {i : Term} :
      QueryRead d ρ e₁ i → QueryRead d ρ e₂ i → PatternRead d ρ (.eq e₁ e₂)

def Env.ReadsAs (src : Database) (ρs ρt : Env) (vs : List Var) : Prop :=
  ∀ v ∈ vs, ∀ i, Env.lookup v ρt = some i → ∃ t, Env.lookup v ρs = some t ∧ Cong src t i

theorem Env.ReadsAs.mono {src : Database} {ρs ρt : Env} {vs ws : List Var}
    (h : Env.ReadsAs src ρs ρt vs) (hsub : ws ⊆ vs) : Env.ReadsAs src ρs ρt ws :=
  fun v hv => h v (hsub hv)

def CongUp (src : Database) (t i : Term) : Prop :=
  ∀ D : Database, src.Contained D → (∀ s ∈ t.subterms, s ∈ D.terms) → Cong D t i

theorem CongUp.lit {src : Database} {l : Lit} : CongUp src (.lit l) (.lit l) :=
  fun _ _ hsub => hsub _ (Term.self_mem_subterms _)

theorem CongUp.of_cong {src : Database} {t i : Term} (h : Cong src t i) : CongUp src t i :=
  fun _ hc _ => Cong.mono hc h

theorem CongUp.congList {src D : Database} (hcon : src.Contained D) {ts es : List Term}
    (h : List.Forall₂ (CongUp src) ts es)
    (hsub : ∀ t ∈ ts, ∀ s ∈ t.subterms, s ∈ D.terms) : CongList D ts es := by
  rw [CongList.forall₂]
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hl ih =>
    exact .cons (hab D hcon (hsub a (by simp))) (ih fun t ht => hsub t (by simp [ht]))

theorem CongUp.congOn {src : Database} {t i : Term} (h : CongUp src t i) :
    CongOn src [t] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

theorem CongUp.congOn_pair_left {src : Database} {t u i : Term} (h : CongUp src t i) :
    CongOn src [t, u] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

theorem CongUp.congOn_pair_right {src : Database} {t u i : Term} (h : CongUp src u i) :
    CongOn src [t, u] u i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨u, by simp, hs⟩

mutual

theorem congUp_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {ρs ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src ρs ρt e.vars) :
    ∃ t, e.eval src.sig ρs = some t ∧ CongUp src t i := by
  revert hlink
  induction h using QueryRead.rec
    (motive_2 := fun es is _ => Env.ReadsAs src ρs ρt (Expr.varsList es) →
      ∃ ts, Expr.evalList src.sig es ρs = some ts ∧ List.Forall₂ (CongUp src) ts is) with
  | lit => exact fun _ => ⟨_, rfl, CongUp.lit⟩
  | @var v i hlk =>
    intro hlink
    obtain ⟨t, ht, hc⟩ := hlink v (by simp [Expr.vars]) i hlk
    exact ⟨t, ht, .of_cong hc⟩
  | @app f args es i _ ho ih =>
    intro hlink
    obtain ⟨as, ham, hal, hae⟩ := hs f _ _ ho
    obtain ⟨hnp, hctor⟩ := hb f as ham
    obtain ⟨ts, hts, hup⟩ := ih (by simpa [Expr.vars] using hlink)
    refine ⟨.app f ts, by simp [Expr.eval, hnp, hctor, hts], fun D hcon hsub => ?_⟩
    have hlD : CongList D ts es :=
      CongUp.congList hcon hup fun t ht s hs' => hsub s (Term.arg_subterms ht hs')
    exact (Cong.congr (hsub _ (Term.self_mem_subterms _)) (hcon.terms ham)
      (hlD.trans (CongList.mono hcon hal).symm)).trans (Cong.mono hcon hae)
  | nil _ => exact ⟨[], rfl, .nil⟩
  | @cons a i as is _ _ ih ihl hlink =>
    obtain ⟨t, ht, hc⟩ := ih (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inl hv))
    obtain ⟨ts, hts, hcs⟩ := ihl (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inr hv))
    exact ⟨t :: ts, by simp [Expr.evalList, ht, hts], .cons hc hcs⟩

end

theorem mem_terms_of_queryRead {src d : Database} (hs : ViewsSound d src) {ρs ρt : Env}
    {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hlink : Env.ReadsAs src ρs ρt e.vars)
    (hnl : ∀ l, e = .lit l → Term.lit l ∈ src.terms) : i ∈ src.terms := by
  cases h with
  | lit => exact hnl _ rfl
  | var hlk =>
    obtain ⟨_, _, hc⟩ := hlink _ (by simp [Expr.vars]) _ hlk
    exact hc.mem_right
  | app _ ho =>
    obtain ⟨_, _, _, hae⟩ := hs _ _ _ ho
    exact hae.mem_right

theorem matches_expr_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src τ ρt e.vars)
    (hnl : ∀ l, e = .lit l → Term.lit l ∈ src.terms) :
    Matches src (.expr e) τ := by
  obtain ⟨t, ht, hup⟩ := congUp_of_queryRead hb hs h hlink
  exact .expr (mem_terms_of_queryRead hs h hlink hnl) (Expr.evalAtom_of_eval ht) hup.congOn.symm

theorem matches_eq_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {e₁ e₂ : Expr} {i : Term}
    (h₁ : QueryRead d ρt e₁ i) (h₂ : QueryRead d ρt e₂ i)
    (hlink : Env.ReadsAs src τ ρt (e₁.vars ∪ e₂.vars))
    (hnl : (∀ l, e₁ = .lit l → Term.lit l ∈ src.terms) ∨
      (∀ l, e₂ = .lit l → Term.lit l ∈ src.terms)) : Matches src (.eq e₁ e₂) τ := by
  have hl₁ : Env.ReadsAs src τ ρt e₁.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inl hv)
  have hl₂ : Env.ReadsAs src τ ρt e₂.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inr hv)
  obtain ⟨t₁, ht₁, hu₁⟩ := congUp_of_queryRead hb hs h₁ hl₁
  obtain ⟨t₂, ht₂, hu₂⟩ := congUp_of_queryRead hb hs h₂ hl₂
  have hi : i ∈ src.terms :=
    hnl.elim (fun hn => mem_terms_of_queryRead hs h₁ hl₁ hn)
      (fun hn => mem_terms_of_queryRead hs h₂ hl₂ hn)
  exact .eq hi ht₁ ht₂ hu₁.congOn_pair_left.symm
    (hu₁.congOn_pair_left.trans hu₂.congOn_pair_right.symm)

theorem matches_of_patternRead {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {τ ρt : Env} {p : Pattern} (hg : p.GroundedAt src)
    (h : PatternRead d ρt p) (hlink : Env.ReadsAs src τ ρt p.vars) :
    Matches src p τ := by
  cases h with
  | expr hr => exact matches_expr_of_queryRead hb hs hr hlink hg
  | eq h₁ h₂ => exact matches_eq_of_queryRead hb hs h₁ h₂ hlink hg

def sourceSubst (env : Env) (g : Var → Term) (p : Pattern) : Env :=
  (p.freeVars env).map fun v => (v, g v)

theorem dom_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} :
    Env.dom (sourceSubst env g p) = p.freeVars env := by
  simp [sourceSubst, Env.dom, List.map_map, Function.comp_def]

theorem lookup_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} {v : Var}
    (hv : v ∈ p.freeVars env) : Env.lookup v (sourceSubst env g p) = some (g v) :=
  (Env.lookup_eq_some_iff_mem (by rw [dom_sourceSubst]; exact p.freeVars_nodup env)).mpr
    (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem lookup_nil_sourceSubst {g : Var → Term} {p : Pattern} {v : Var} (hv : v ∈ p.vars) :
    Env.lookup v (sourceSubst [] g p) = some (g v) :=
  lookup_sourceSubst (p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩)

theorem Query.vars_nodup (q : Query) : (Query.vars q).Nodup := by
  induction q with
  | nil => simp [Query.vars]
  | cons p ps ih => exact List.Nodup.union _ ih

theorem validQuerySubst_of_patternReads {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {q : Query} {g : Var → Term} {ρt : Env}
    (hgt : ∀ v ∈ Query.vars q, g v ∈ src.terms)
    (hlink : ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i → Cong src (g v) i)
    (hgr : ∀ p ∈ q, p.GroundedAt src) (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, Env.lookup v τ = some (g v) := by
  have hmem : ∀ p ∈ q, ∀ v ∈ p.vars, v ∈ Query.vars q := fun p hp v hv =>
    Query.mem_vars.mpr ⟨p, hp, hv⟩
  have hvalid : ∀ p ∈ q, ValidSubst src p (sourceSubst [] g p) := by
    intro p hp
    refine ⟨⟨by rw [dom_sourceSubst], ?_⟩, ?_⟩
    · rintro b hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      exact hgt v (hmem p hp v (p.mem_freeVars.mp hv).1)
    · refine matches_of_patternRead hb hs (hgr p hp) (hread p hp) fun v hv i hi => ?_
      exact ⟨g v, lookup_nil_sourceSubst hv, hlink v (hmem p hp v hv) i hi⟩
  have hnd : (Env.dom (Query.vars q |>.map fun v => (v, g v))).Nodup := by
    simpa [Env.dom, List.map_map, Function.comp_def] using Query.vars_nodup q
  have hrefines : ∀ ρ ∈ q.map (sourceSubst [] g),
      Env.Refines ρ (Query.vars q |>.map fun v => (v, g v)) := by
    rintro ρ hρ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hρ
    rintro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    exact (Env.lookup_eq_some_iff_mem hnd).mpr
      (List.mem_map.mpr ⟨v, hmem p hp v (p.mem_freeVars.mp hv).1, rfl⟩)
  obtain ⟨τ, hu, hrτ⟩ := Env.exists_unionAll _ hrefines
  have hself : ∀ ρ ∈ q.map (sourceSubst [] g), Env.Refines ρ ρ := by
    rintro ρ hρ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
    exact Env.Refines.self_of_nodup (by rw [dom_sourceSubst]; exact p.freeVars_nodup _)
  obtain ⟨hall, -⟩ := hu.refines_of_mem hself
  refine ⟨τ, ⟨_, List.forall₂_map_self hvalid, hu⟩, ?_, fun v hv => ?_⟩
  · intro b hb
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp (Env.mem_of_lookup (hrτ b hb))
    obtain rfl : v = b.1 := congrArg Prod.fst heq
    exact hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hv
  exact hall _ (List.mem_map.mpr ⟨p, hp, rfl⟩) (v, g v)
    (List.mem_map.mpr ⟨v, p.mem_freeVars.mpr ⟨hvp, by simp [Env.dom]⟩, rfl⟩)

mutual

theorem exists_source_of_argVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hv : Expr.ArgVar v e) :
    ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j := by
  cases h with
  | lit => exact absurd hv (by simp [Expr.ArgVar])
  | var => exact absurd hv (by simp [Expr.ArgVar])
  | @app f args es i hl ho =>
    obtain ⟨as, -, hal, -⟩ := hs f _ _ ho
    rcases hv with hv | hv
    · exact exists_source_of_memVar hl hal hv
    · exact exists_source_of_argVarList hs hl hv

theorem exists_source_of_memVar {src d : Database} {ρt : Env} {v : Var} :
    ∀ {args : List Expr} {es as : List Term}, QueryReadList d ρt args es →
      CongList src as es → Expr.var v ∈ args →
      ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j
  | _, _, _, .nil, _, hv => absurd hv (by simp)
  | _, _, _, .cons hr hl, hc, hv => by
    cases hc with
    | cons hc hcl =>
      rcases List.mem_cons.mp hv with rfl | hv
      · cases hr with
        | var hlk => exact ⟨_, _, hlk, hc⟩
      · exact exists_source_of_memVar hl hcl hv

theorem exists_source_of_argVarList {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} : ∀ {args : List Expr} {es : List Term}, QueryReadList d ρt args es →
      Expr.ArgVarList v args → ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j
  | _, _, .nil, hv => absurd hv (by simp [Expr.ArgVarList])
  | _, _, .cons hr hl, hv => by
    rcases hv with hv | hv
    · exact exists_source_of_argVar hs hr hv
    · exact exists_source_of_argVarList hs hl hv

end

theorem exists_source_of_patternArgVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j := by
  cases h with
  | expr hr => exact exists_source_of_argVar hs hr hv
  | eq h₁ h₂ => exact hv.elim (exists_source_of_argVar hs h₁) (exists_source_of_argVar hs h₂)

theorem out_of_matches_entry {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {vs as : List Expr} {f : FnName} {σ : Env}
    (hp : Prim.ofName f = none) (h : Matches d (.expr (.app f (as ++ vs))) σ) :
    ∃ ts us, Expr.evalList d.sig as (σ) = some ts ∧
      Expr.evalList d.sig vs (σ) = some us ∧
      Term.app f (ts ++ us) ∈ d.terms ∧ d.Out f ts us := by
  cases h with
  | expr hw hev hc =>
    obtain ⟨cols, hcols, rfl⟩ := Expr.evalAtom_app_inv hp hev
    obtain ⟨ts, us, hts, hus, rfl⟩ := Expr.evalList_append hcols
    have heq := congOn_eq_of_diag hd hc
    subst heq
    refine ⟨ts, us, hts, hus, hw, ts, CongList.refl fun a ha => ?_, hw⟩
    exact hsc _ hw (Term.arg_subterms (List.mem_append_left _ ha) (Term.self_mem_subterms a))

theorem encodeQueryExpr_var {v : Var} {n : Nat} :
    encodeQueryExpr (.var v) n = (.var v, [], n) := rfl

theorem encodeQueryExpr_app_expr {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).1 = .var (freshVar (encodeQueryArgs args n).2.2) := rfl

theorem encodeQueryExpr_app_atoms {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).2.1 =
      (encodeQueryArgs args n).2.1 ++
        [.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))] := rfl

theorem encodeQueryArgs_cons_exprs {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).1 =
      (encodeQueryExpr e n).1 :: (encodeQueryArgs es (encodeQueryExpr e n).2.2).1 := rfl

theorem encodeQueryArgs_cons_atoms {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).2.1 =
      (encodeQueryExpr e n).2.1 ++ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.1 := rfl

theorem encodePattern_expr_atoms {e : Expr} {n : Nat} :
    (encodePattern (.expr e) n).1 = (encodeQueryExpr e n).2.1 := rfl

theorem encodePattern_eq_atoms {e₁ e₂ : Expr} {n : Nat} :
    (encodePattern (.eq e₁ e₂) n).1 =
      (encodeQueryExpr e₁ n).2.1 ++
        (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).2.1 ++
        [.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1] := rfl

theorem encodeQuery_cons_atoms {p : Pattern} {ps : Query} {n : Nat} :
    (encodeQuery (p :: ps) n).1 =
      (encodePattern p n).1 ++ (encodeQuery ps (encodePattern p n).2).1 := rfl

theorem encodePattern_subset_encodeQuery {p : Pattern} : ∀ {q : Query}, p ∈ q → ∀ n : Nat,
    ∃ m, (encodePattern p m).1 ⊆ (encodeQuery q n).1
  | [], hp, _ => absurd hp (by simp)
  | p' :: ps, hp, n => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨n, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inl ha)⟩
    · obtain ⟨m, hm⟩ := encodePattern_subset_encodeQuery hp' (encodePattern p' n).2
      exact ⟨m, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inr (hm ha))⟩

theorem mem_encodeQueryArgs_of_mem {v : Var} : ∀ {args : List Expr} {n : Nat},
    Expr.var v ∈ args → Expr.var v ∈ (encodeQueryArgs args n).1
  | [], _, h => absurd h (by simp)
  | a :: as, n, h => by
    rw [encodeQueryArgs_cons_exprs]
    rcases List.mem_cons.mp h with rfl | h'
    · rw [encodeQueryExpr_var]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_encodeQueryArgs_of_mem h')

mutual

theorem lookup_isSome_of_argVar {d : Database} {σ : Env} {v : Var} :
    ∀ (e : Expr) (n : Nat), (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.ArgVar v e → (Env.lookup v (σ)).isSome
  | .lit _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .var _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .app f args, n, hm, hv => by
    rw [encodeQueryExpr_app_atoms] at hm
    rcases hv with hv | hv
    · cases hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp) with
      | expr _ hev _ =>
        obtain ⟨cols, hcols, -⟩ := Expr.evalAtom_app_inv (prim_viewName f) hev
        obtain ⟨ts, us, hts, -, -⟩ := Expr.evalList_append hcols
        exact Expr.lookup_isSome_of_mem_evalList hts (mem_encodeQueryArgs_of_mem hv)
    · exact lookup_isSome_of_argVarList args n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv

theorem lookup_isSome_of_argVarList {d : Database} {σ : Env} {v : Var} :
    ∀ (es : List Expr) (n : Nat), (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.ArgVarList v es → (Env.lookup v (σ)).isSome
  | [], _, _, hv => absurd hv (by simp [Expr.ArgVarList])
  | e :: es, n, hm, hv => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv
    · exact lookup_isSome_of_argVarList es (encodeQueryExpr e n).2.2
        (fun a ha => hm a (List.mem_append.mpr (Or.inr ha))) hv

end

theorem lookup_isSome_of_patternArgVar {d : Database} {σ : Env} {v : Var} :
    ∀ (p : Pattern) (n : Nat),
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → Pattern.ArgVar v p →
      (Env.lookup v (σ)).isSome
  | .expr e, n, hm, hv => lookup_isSome_of_argVar e n hm hv
  | .eq e₁ e₂, n, hm, hv => by
    rw [encodePattern_eq_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e₁ n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha))))) hv
    · exact lookup_isSome_of_argVar e₂ (encodeQueryExpr e₁ n).2.2
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha))))) hv

theorem exists_eval_encodeQueryExpr {d : Database} {σ : Env} :
    ∀ (e : Expr) (n : Nat), (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      (∀ v ∈ e.vars, (Env.lookup v (σ)).isSome) →
      ∃ i, Expr.eval d.sig (encodeQueryExpr e n).1 (σ) = some i
  | .lit l, _, _, _ => ⟨.lit l, rfl⟩
  | .var v, _, _, hb => Option.isSome_iff_exists.mp (hb v (by simp))
  | .app f args, n, hm, _ => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var]
    cases hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp) with
    | expr _ hev _ =>
      obtain ⟨cols, hcols, -⟩ := Expr.evalAtom_app_inv (prim_viewName f) hev
      obtain ⟨ts, us, -, hus, -⟩ := Expr.evalList_append hcols
      exact Option.isSome_iff_exists.mp (Expr.lookup_isSome_of_mem_evalList hus (by simp))
private theorem evalList_one_var {sig : Signature} {x : Var} {ρ : Env} {us : List Term}
    (h : Expr.evalList sig [.var x] ρ = some us) :
    ∃ a, Env.lookup x ρ = some a ∧ us = [a] := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain rfl : rest = [] := (Option.some.inj hrest).symm
  exact ⟨a, ha, rfl⟩

mutual

theorem queryRead_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (e : Expr) (n : Nat) {i : Term}, (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.eval d.sig (encodeQueryExpr e n).1 (σ) = some i →
      QueryRead d (σ) e i
  | .lit l, _, _, _, hi => by
    obtain rfl : Term.lit l = _ := Option.some.inj hi
    exact .lit
  | .var _, _, _, _, hi => .var hi
  | .app f args, n, i, hm, hi => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var] at hi
    obtain ⟨ts, us, hts, hus, -, ho⟩ :=
      out_of_matches_entry hd hsc (prim_viewName f)
        (as := (encodeQueryArgs args n).1)
        (vs := [.var (freshVar (encodeQueryArgs args n).2.2)])
        (hm (.expr (.app (viewName f) ((encodeQueryArgs args n).1 ++
          [.var (freshVar (encodeQueryArgs args n).2.2)]))) (by simp))
    obtain ⟨a, ha, rfl⟩ := evalList_one_var hus
    obtain rfl : a = i := Option.some.inj (ha.symm.trans hi)
    exact .app (queryReadList_of_matches hd hsc args n
      (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) hts) ho

theorem queryReadList_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (es : List Expr) (n : Nat) {ts : List Term},
      (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.evalList d.sig (encodeQueryArgs es n).1 (σ) = some ts →
      QueryReadList d (σ) es ts
  | [], _, _, _, h => by
    obtain rfl : ([] : List Term) = _ := Option.some.inj h
    exact .nil
  | e :: es, n, ts, hm, h => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rw [encodeQueryArgs_cons_exprs, Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h'⟩ := h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact .cons (queryRead_of_matches hd hsc e n
        (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) ht)
      (queryReadList_of_matches hd hsc es (encodeQueryExpr e n).2.2
        (fun x hx => hm x (List.mem_append.mpr (Or.inr hx))) hus)

end

theorem patternRead_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (p : Pattern) (n : Nat),
      (∀ v ∈ p.vars, (Env.lookup v (σ)).isSome) →
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → PatternRead d (σ) p
  | .expr e, n, hb, hm => by
    rw [encodePattern_expr_atoms] at hm
    obtain ⟨i, hi⟩ := exists_eval_encodeQueryExpr e n hm hb
    exact .expr (queryRead_of_matches hd hsc e n hm hi)
  | .eq e₁ e₂, n, _, hm => by
    rw [encodePattern_eq_atoms] at hm
    cases hm (.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1)
        (by simp) with
    | @eq _ _ _ w t₁ t₂ hw he₁ he₂ hc₁ hc₂ =>
      obtain rfl : t₁ = t₂ := congOn_eq_of_diag hd hc₂
      exact .eq
        (queryRead_of_matches hd hsc e₁ n
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha)))))
          he₁)
        (queryRead_of_matches hd hsc e₂ (encodeQueryExpr e₁ n).2.2
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha)))))
          he₂)

theorem patternReads_of_encodeQuery {tgt : Database} (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∀ p ∈ q, PatternRead tgt σ p := by
  have hblock : ∀ p ∈ q, ∃ m, ∀ a ∈ (encodePattern p m).1, Matches tgt a σ := by
    intro p hp
    obtain ⟨m, hsub⟩ := encodePattern_subset_encodeQuery hp n
    exact ⟨m, fun a ha => h.matches_of_mem (hsub ha)⟩
  have hbound : ∀ v ∈ Query.vars q, (Env.lookup v σ).isSome := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    obtain ⟨m, hm⟩ := hblock p hp
    exact lookup_isSome_of_patternArgVar p m hm ha
  intro p hp
  obtain ⟨m, hm⟩ := hblock p hp
  exact patternRead_of_matches hd hsc p m
    (fun v hv => hbound v (Query.mem_vars.mpr ⟨p, hp, hv⟩)) hm

theorem mem_terms_of_patternArgVar {src d : Database} (hs : ViewsSound d src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
  obtain ⟨j, t, hj, hc⟩ := exists_source_of_patternArgVar hs h hv
  exact ⟨j, hj, hc.mem_right⟩

def idReading (ρt : Env) : Var → Term := fun v => (Env.lookup v ρt).getD (.lit (.int 0))

theorem idReading_eq {ρt : Env} {v : Var} {i : Term} (h : Env.lookup v ρt = some i) :
    idReading ρt v = i := by simp [idReading, h]

theorem exists_validQuerySubst_at_ids {src d : Database} (hb : src.TermsBuild)
    (hs : ViewsSound d src) {q : Query} {ρt : Env}
    (hgr : ∀ p ∈ q, p.GroundedAt src) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i →
        Env.lookup v (τ ++ src.env) = some i := by
  have hbound : ∀ v ∈ Query.vars q, ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    exact mem_terms_of_patternArgVar hs (hread p hp) ha
  have hgt : ∀ v ∈ Query.vars q, idReading ρt v ∈ src.terms := by
    intro v hv
    obtain ⟨i, hi, hm⟩ := hbound v hv
    rw [idReading_eq hi]; exact hm
  obtain ⟨τ, hv, hdom, hτ⟩ := validQuerySubst_of_patternReads hb hs
    (g := idReading ρt) hgt
    (fun v hv i hi => idReading_eq hi ▸ hgt v hv) hgr hread
  exact ⟨τ, hv, hdom, fun v hvq i hi => by
    rw [Env.lookup_append_of_some (hτ v hvq), idReading_eq hi]⟩

/-- A match of the flattened query supplies an existing source match at the same values.
This is the query obligation used when transporting a compiled rule head to the source. -/
theorem sourceMatch_of_encodedQuery {src tgt : Database} (hb : src.TermsBuild)
    (hs : ViewsSound tgt src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hg : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v σ = some i →
        Env.lookup v (τ ++ src.env) = some i :=
  exists_validQuerySubst_at_ids hb hs (fun p hp => (hg p hp).groundedAt) hk
    (patternReads_of_encodeQuery hd hsc hk h)

end Egglog.Congruence
