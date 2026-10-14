import EgglogSemantics.Proofs.NoUnions

/-! Complete entry atoms: evaluation, indexed matching, and single-atom rule heads. -/

namespace Egglog

/-- Replacing one operand replaces one value: what a column rule's key expression is. -/
theorem Expr.evalList_set {sig : Signature} {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ (i : Nat) {e : Expr} {t : Term}, e.eval sig ρ = some t →
        Expr.evalList sig (es.set i e) ρ = some (ts.set i t)
  | [], _, h, _, _, _, _ => by
      rw [Expr.evalList, Option.some.injEq] at h
      cases h
      simp
  | a :: as, _, h, 0, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_zero, List.set_cons_zero, Expr.evalList, he, Option.bind_some, hus]
      rfl
  | a :: as, _, h, i + 1, e, t, he => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      rw [List.set_cons_succ, List.set_cons_succ, Expr.evalList, hu, Option.bind_some,
        Expr.evalList_set hus i he]
      rfl

/-- The value at one position is that operand's. -/
theorem Expr.getElem?_of_evalList {sig : Signature} {ρ : Env} :
    ∀ {es : List Expr} {ts : List Term}, Expr.evalList sig es ρ = some ts →
      ∀ (i : Nat) {e : Expr}, es[i]? = some e →
        ∃ t, ts[i]? = some t ∧ e.eval sig ρ = some t
  | [], _, _, i, _, hi => by simp at hi
  | e :: es, _, h, 0, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain rfl : e = e' := by simpa using hi
      exact ⟨u, by simp, hu⟩
  | e :: es, _, h, i + 1, e', hi => by
      rw [Expr.evalList] at h
      obtain ⟨u, hu, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hrest
      obtain ⟨t, ht, hev⟩ := Expr.getElem?_of_evalList hus i (by simpa using hi)
      exact ⟨t, by simpa using ht, hev⟩

/-- A one-element operand list. -/
theorem Expr.evalList_singleton {sig : Signature} {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList sig [e] σ = some ts) : ∃ t, e.eval sig σ = some t ∧ ts = [t] := by
  rw [Expr.evalList] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.evalList, Option.map_some, Option.some.injEq] at h
  exact ⟨t, ht, h.symm⟩

/-- Evaluate a pair of operands. -/
theorem Expr.evalList_pair {sig : Signature} {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList sig [e₁, e₂] σ = some ts) :
    ∃ t₁ t₂, e₁.eval sig σ = some t₁ ∧ e₂.eval sig σ = some t₂ ∧ ts = [t₁, t₂] := by
  rw [Expr.evalList] at h
  obtain ⟨t₁, ht₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨t₂, ht₂, rfl⟩ := Expr.evalList_singleton hus
  exact ⟨t₁, t₂, ht₁, ht₂, rfl⟩

/-- **What one entry atom records**: its evaluated key and output columns
the operands evaluated to in the state the action ran in. `addRow` is `addTerm` on the entry
term, so this is also the read-back of the *entry term* and of all of its subterms. -/
theorem execAction_entry {d e : FDatabase} {f : FnName} {args out : List Expr}
    (h : execAction d (.expr (.app f (args ++ out))) = some e) :
    ∃ as vs, Expr.evalList d.sig args d.env = some as ∧
      Expr.evalList d.sig out d.env = some vs ∧ e = d.addAtom (.app f (as ++ vs)) := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Expr.evalAtom] at ht
  split at ht
  · obtain ⟨cols, hc, rfl⟩ := Option.map_eq_some_iff.mp ht
    rw [Expr.evalList_append_map] at hc
    obtain ⟨as, ha, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨vs, hv, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact ⟨as, vs, ha, hv, rfl⟩
  · simp at ht

/-- At a diagonal database, every successful atom instance is a recorded term. -/
theorem mem_terms_of_patternHolds_expr {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {e : Expr} {σ : Env} (h : patternHolds d (.expr e) σ = true) :
    ∃ t, e.evalAtom d.sig σ = some t ∧ t ∈ d.terms := by
  cases he : e.entry d.sig with
  | none =>
    cases hv : e.evalAtom d.sig σ with
    | none => simp [patternHolds, he, hv] at h
    | some t =>
      simp only [patternHolds, he, hv, decide_eq_true_eq] at h
      obtain ⟨w, hw, hc⟩ := h
      have ht : w = t := diag_closureF
        (fun q hq => hr q (by simpa only [FDatabase.addTerm_eqs] using hq)) hc
      exact ⟨t, rfl, ht ▸ hw⟩
  | some entry =>
    obtain ⟨f, keys, vals⟩ := entry
    cases hv : Expr.evalList d.sig vals σ with
    | none => simp [patternHolds, he, hv] at h
    | some us =>
      cases hk : Expr.evalList d.sig keys σ with
      | none => simp [patternHolds, he, hv, hk] at h
      | some ts =>
        simp only [patternHolds, he, hv, hk, List.any_eq_true,
          Bool.and_eq_true_iff, decide_eq_true_eq] at h
        obtain ⟨r, hm, ⟨⟨hfn, ha⟩, ho⟩⟩ := h
        have hcl : ∀ p ∈ ((d.addTerms ts).addTerms us).closureF, p.1 = p.2 :=
          fun p hp => diag_closureF (fun q hq => hr q (by simpa using hq)) hp
        obtain rfl : ts = r.args := eq_of_congrKeys hcl ha
        obtain rfl : us = r.out := eq_of_congrKeys hcl ho
        obtain ⟨dc, hd, hmg, -⟩ := Expr.entry_some he
        refine ⟨.app f (r.args ++ r.out), Expr.evalAtom_entry he hk hv, ?_⟩
        have hm' := mem_terms_of_indexOk hr hidx hm (by
          rw [hfn, Signature.mergeOf, hd, Option.bind_some]
          exact Option.isSome_iff_ne_none.mp hmg)
        simpa only [hfn] using hm'

/-- Read an atom's columns at any chosen syntactic split. The split need not be its index key. -/
theorem mem_terms_of_patternHolds_entry {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {vs as : List Expr} {f : FnName} {σ : Env}
    (h : patternHolds d (.expr (.app f (as ++ vs))) σ = true) :
    ∃ ts us, Expr.evalList d.sig as σ = some ts ∧
      Expr.evalList d.sig vs σ = some us ∧
      Term.app f (ts ++ us) ∈ d.terms := by
  obtain ⟨t, hev, hm⟩ := mem_terms_of_patternHolds_expr hr hidx h
  obtain ⟨cols, hcols, rfl⟩ := Expr.evalAtom_app_inv hev
  obtain ⟨ts, us, hts, hus, rfl⟩ := Expr.evalList_append hcols
  exact ⟨ts, us, hts, hus, hm⟩

/-! ##### The substitution a pattern was checked at, and the one the head runs under -/

/-- A binding a restricted substitution answers with is one the full substitution answers
with, the globals shadowing both alike. -/
theorem lookup_append_of_refines {env ρ σ : Env} (hr : Env.Refines ρ σ) {v : Var} {t : Term}
    (h : Env.lookup v (env ++ ρ) = some t) : Env.lookup v (env ++ σ) = some t := by
  by_cases hv : v ∈ Env.dom env
  · rw [Env.lookup_append_of_mem hv]
    rw [Env.lookup_append_of_mem hv] at h
    exact h
  · rw [Env.lookup_append_of_not_mem hv]
    rw [Env.lookup_append_of_not_mem hv] at h
    exact hr (v, t) (Env.mem_of_lookup h)

mutual

/-- **An evaluation survives un-restricting the substitution.** `Expr.eval` reads the
environment only through `Env.lookup`, so what the pattern's own restriction pinned down the
whole match pins down too — which is what lets a query atom's reading be used at the
environment the *head* runs in. -/
theorem Expr.eval_of_refines {sig : Signature} {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (e : Expr) {t : Term}, e.eval sig (env ++ ρ) = some t → e.eval sig (env ++ σ) = some t
  | .lit _, _, h => h
  | .var _, _, h => by
      rw [Expr.eval] at h ⊢
      exact lookup_append_of_refines hr h
  | .app f args, _, h => by
      simp only [Expr.eval] at h ⊢
      by_cases hct : sig.IsCtor f
      · rw [if_pos hct] at h ⊢
        obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
        rw [Expr.evalList_of_refines hr args hts]
        exact congrArg some hap
      · rw [if_neg hct] at h
        exact absurd h (by simp)
  | .min a b, _, h => by
      rw [Expr.eval_min] at h ⊢
      obtain ⟨x, hx, hmap⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hmap
      rw [Expr.eval_of_refines hr a hx, Option.bind_some, Expr.eval_of_refines hr b hy,
        Option.map_some]

@[inherit_doc Expr.eval_of_refines]
theorem Expr.evalList_of_refines {sig : Signature} {env ρ σ : Env} (hr : Env.Refines ρ σ) :
    ∀ (es : List Expr) {ts : List Term},
      Expr.evalList sig es (env ++ ρ) = some ts → Expr.evalList sig es (env ++ σ) = some ts
  | [], _, h => h
  | e :: es, _, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_of_refines hr e ht, Expr.evalList_of_refines hr es hts]
      exact congrArg some hcons

end

/-- Every pattern of a matched query holds, at its own restriction of the substitution. -/
theorem patternHolds_of_mem_matchQuery {d : FDatabase} {q : Query} {σ : Env}
    (h : σ ∈ matchQuery d q) {p : Pattern} (hp : p ∈ q) :
    patternHolds d p (Env.canon (p.freeVars []) σ) = true := by
  rw [matchQuery, List.mem_filter] at h
  exact List.all_eq_true.mp h.2 p hp

/-- **A matched query's row atom, read at the substitution its head runs under.** -/
theorem mem_terms_of_mem_matchQuery_entry {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {q : Query} {σ : Env} (hσ : σ ∈ matchQuery d q) {vs as : List Expr} {f : FnName}
    (hp : Pattern.expr (.app f (as ++ vs)) ∈ q) :
    ∃ ts us, Expr.evalList d.sig as σ = some ts ∧
      Expr.evalList d.sig vs σ = some us ∧
      Term.app f (ts ++ us) ∈ d.terms := by
  obtain ⟨ts, us, ha, hv, hmem⟩ :=
    mem_terms_of_patternHolds_entry hr hidx (patternHolds_of_mem_matchQuery hσ hp)
  exact ⟨ts, us, Expr.evalList_of_refines (env := []) Env.refines_canon as ha,
    Expr.evalList_of_refines (env := []) Env.refines_canon vs hv, hmem⟩

/-! ##### The one `set` a maintenance head is -/

/-- **A block that is one `set`, read back.** The environment and rule list come back from the
pre-state, so what the firing contributes to `terms` is exactly the entry the `set` recorded.

The reading is at `σ ++ d.env`, which is where `execLocalActions` runs a head: the match's own
bindings win, and `Expr.eval_append_env` is what carries a matched atom's value into it. -/
theorem execLocalActions_entry {d d' : FDatabase} {g : FnName} {args out : List Expr} {σ : Env}
    (h : execLocalActions d [.expr (.app g (args ++ out))] σ = some d') :
    ∃ es vs, Expr.evalList d.sig args (σ ++ d.env) = some es ∧
      Expr.evalList d.sig out (σ ++ d.env) = some vs ∧
      ∀ t ∈ d'.terms, t ∈ (FDatabase.addRow g es vs d).terms := by
  rw [execLocalActions] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [execActions] at he
  obtain ⟨e₁, he₁, he₂⟩ := Option.bind_eq_some_iff.mp he
  rw [execActions, Option.some.injEq] at he₂
  subst he₂
  obtain ⟨es, vs, hes, hvs, rfl⟩ := execAction_entry he₁
  exact ⟨es, vs, hes, hvs, fun t ht => ht⟩

/-- One column of the right-hand list moved along a congruence. What the rebuild's column
rules do to a key, pointwise. -/
theorem CongList.setAt {db : Database} {as cs : List Term} {c x : Term} (i : Nat)
    (h : CongList db as cs) (hget : cs[i]? = some c) (hcx : Cong db c x) :
    CongList db as (cs.set i x) := by
  rw [CongList.forall₂] at h ⊢
  induction i generalizing as cs with
  | zero =>
    cases h with
    | nil => simp at hget
    | cons hab hl =>
      obtain rfl : _ = c := by simpa using hget
      simpa using List.Forall₂.cons (hab.trans hcx) hl
  | succ n ih =>
    cases h with
    | nil => simp at hget
    | cons hab hl => simpa using List.Forall₂.cons hab (ih hl (by simpa using hget))

/-- A member of a list one position was replaced in is a member or the replacement. -/
theorem mem_or_eq_of_mem_set {α : Type _} {l : List α} {i : Nat} {b a : α}
    (h : a ∈ l.set i b) : a ∈ l ∨ a = b := by
  induction l generalizing i with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero =>
      rw [List.set_cons_zero, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ h)
    | succ j =>
      rw [List.set_cons_succ, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact (ih h).imp (List.mem_cons_of_mem _) id

/-! ## The match, read back at a diagonal target

`validQuerySubst_of_mem_matchQuery` needs `Signature.AllConstructors`, which is exactly what
an encoded target does not have: `@UF` and every `@fView` carry a `:merge`. The clause that
needs it is `patternHolds`' **read** branch, and at a target whose `Cong` is the identity
that branch is `mem_terms_of_patternHolds_entry` — a matched row is an entry term. So the
same repackaging goes through with `FDatabase.EqsRefl` and `FDatabase.IndexOk` in place of
the signature condition, which is what the encoded target has. -/

/-- `withOperands` records the operand, so it is congruent to itself there whether or not
the state held it. -/
theorem congOn_self {db : Database} (t : Term) : CongOn db [t] t t :=
  Cong.assert (by
    simp only [Database.withOperands, Database.addTerms, List.foldl_cons,
      List.foldl_nil, Database.addTerm, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inr ⟨t, Term.self_mem_subterms t, rfl⟩)

/-- **`patternHolds` is `Matches`, at a diagonal state whose index is faithful.**
`patternHolds_iff` with `Signature.AllConstructors` traded for the two invariants an encoded
target has; only the read branch differs, and there it is `mem_terms_of_patternHolds_entry`. -/
theorem matches_of_patternHolds {d : FDatabase} (he : d.EqsInTerms) (hr : d.EqsRefl)
    (hidx : d.IndexOk) {p : Pattern} {σ : Env} (h : patternHolds d p σ = true) :
    Matches d.toDatabase p σ := by
  cases p with
  | expr e =>
    obtain ⟨t, hev, hm⟩ := mem_terms_of_patternHolds_expr hr hidx h
    exact .expr (FDatabase.mem_toDatabase_terms.mpr hm) hev (congOn_self t)
  | eq e₁ e₂ =>
    cases hev₁ : e₁.eval d.sig σ with
    | none => rw [patternHolds, hev₁] at h; simp at h
    | some t₁ =>
      cases hev₂ : e₂.eval d.sig σ with
      | none => rw [patternHolds, hev₁, hev₂] at h; simp at h
      | some t₂ =>
        simp only [patternHolds, hev₁, hev₂, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨heq, w, hwm, hcl⟩ := h
        exact .eq (FDatabase.mem_toDatabase_terms.mpr hwm)
          (by rw [FDatabase.toDatabase_sig]; exact hev₁)
          (by rw [FDatabase.toDatabase_sig]; exact hev₂)
          (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp hcl))
          (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp heq))

/-- **A substitution the enumerator produced is one the specification admits**, at a
diagonal target with a faithful index. `validQuerySubst_of_mem_matchQuery` with its
signature hypothesis replaced; the repackaging from one restricted substitution to the
specification's `Env.UnionAll` of per-pattern ones is the same. -/
theorem validQuerySubst_of_mem_matchQuery_diag {d : FDatabase} (he : d.EqsInTerms)
    (hr : d.EqsRefl) (hidx : d.IndexOk) {q : Query} {σ : Env} (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at h
  obtain ⟨⟨hdom, hval⟩, hall⟩ := h
  obtain ⟨τ, hu, hrf⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars []) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self (fun p hp =>
    ⟨validEnv_canon hp hdom hval, matches_of_patternHolds he hr hidx (hall p hp)⟩), hu⟩,
    Env.agree_of_refines hrf ?_⟩
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp


/-- Split execution of consecutive action blocks at their intermediate state. -/
theorem execActions_append {as bs : List Action} : ∀ {d e : FDatabase},
    execActions d (as ++ bs) = some e →
      ∃ m, execActions d as = some m ∧ execActions m bs = some e := by
  induction as with
  | nil => intro d e h; exact ⟨d, rfl, h⟩
  | cons a as ih =>
    intro d e h
    cases hv : execAction d a with
    | none => rw [List.cons_append, execActions, hv] at h; simp at h
    | some d' =>
      rw [List.cons_append, execActions, hv, Option.bind_some] at h
      obtain ⟨m, hm, hme⟩ := ih h
      exact ⟨m, by rw [execActions, hv, Option.bind_some]; exact hm, hme⟩


/-- Evaluating a concatenation, in the direction that *builds* one. `Expr.evalList_append` is
the elimination. -/
theorem Expr.evalList_append_eq {sig : Signature} {σ : Env} :
    ∀ {es fs : List Expr} {as bs : List Term},
      Expr.evalList sig es σ = some as → Expr.evalList sig fs σ = some bs →
        Expr.evalList sig (es ++ fs) σ = some (as ++ bs) := by
  intro es
  induction es with
  | nil =>
      intro fs as bs h₁ h₂
      obtain rfl : as = [] := (Option.some.inj h₁).symm
      simpa using h₂
  | cons e es ih =>
      intro fs as bs h₁ h₂
      rw [Expr.evalList] at h₁
      obtain ⟨t, ht, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h₁
      simp only [List.cons_append, Expr.evalList, ht, Option.bind_some, ih hus h₂,
        Option.map_some]

/-- Running a concatenation of action blocks, in the direction that *builds* one.
`execActions_append` is the elimination. -/
theorem execActions_append_eq {as bs : List Action} : ∀ {d m e : FDatabase},
    execActions d as = some m → execActions m bs = some e →
      execActions d (as ++ bs) = some e := by
  induction as with
  | nil =>
      intro d m e h₁ h₂
      obtain rfl : d = m := Option.some.inj h₁
      simpa using h₂
  | cons a as ih =>
      intro d m e h₁ h₂
      rw [execActions] at h₁
      obtain ⟨d₁, hd₁, h₁⟩ := Option.bind_eq_some_iff.mp h₁
      rw [List.cons_append, execActions, hd₁, Option.bind_some]
      exact ih h₁ h₂

/-- Indexing a complete entry agrees with inserting its declared key and output tuple. -/
theorem FDatabase.addAtom_eq_addRow {d : FDatabase} {f : FnName} {dc : FnDecl}
    {as vs : List Term} (hd : d.sig f = some dc) (hm : dc.merge.isSome = true)
    (ha : as.length = dc.arity) (hv : vs.length = dc.outArity) :
    d.addAtom (.app f (as ++ vs)) = d.addRow f as vs := by
  have hw : (as ++ vs).length = dc.entryWidth := by
    have hn : dc.merge ≠ none := by intro hn; simp [hn] at hm
    simp [FnDecl.entryWidth, hn, List.length_append, ha, hv]
  simp [FDatabase.addAtom, FDatabase.entryRowList, hd, hm, hw,
    FDatabase.addRow, ← ha]

/-- Atom insertion preserves existing rows. -/
theorem mem_addAtom_rows {d : FDatabase} {t : Term} {r : Row}
    (h : r ∈ d.rows) : r ∈ (d.addAtom t).rows := by
  simp [FDatabase.addAtom, FDatabase.addTerm, h]

/-- **A row a firing neither displaced nor rewrote is a row of its result.** The skip branch
filters `r₁` out and moves nothing else; the body branch filters `r₁` and rewrites `r₂`. -/
theorem mem_rows_of_mergeOneOriented {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ r : Row} (hfire : d.mergeOneOriented cl r₁ r₂ = some e) (hm : r ∈ d.rows)
    (h₁ : r ≠ r₁) (h₂ : r ≠ r₂) : r ∈ e.rows := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    split at hfire
    next hg =>
      split at hfire
      next =>
        rw [Option.some.injEq] at hfire
        subst hfire
        exact List.mem_filter.mpr ⟨hm, by simpa using h₁⟩
      next =>
        obtain ⟨m, hmb, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, he⟩ := Option.map_eq_some_iff.mp hfire
        subst he
        refine List.mem_map.mpr ⟨r, List.mem_filter.mpr
          ⟨FDatabase.mem_addTerm_rows.mpr (Or.inr ?_), by simpa using h₁⟩, by simp [h₂]⟩
        exact FDatabase.execActions_rows hmb r hm
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)


namespace FDatabase

/-- Whether `t` applies a head to a first argument at or below `a`. The entry-side counterpart
of `FDatabase.rowKeyLe`, and it needs no name test: what the measure counts is bounded above by
the `@UF` entry at the key, and every other term it counts it counts on both sides. -/
def firstArgLe (a : Term) (t : Term) : Bool :=
  match t with
  | .app _ (k :: _) => Term.blt k a || k == a
  | _ => false

/-- The filter only grows as its bound does. -/
theorem firstArgLe_mono {a b : Term} (hba : Term.blt b a = true) {t : Term}
    (h : firstArgLe b t = true) : firstArgLe a t = true := by
  cases t with
  | lit l => exact absurd h (by simp [firstArgLe])
  | app f args =>
      cases args with
      | nil => exact absurd h (by simp [firstArgLe])
      | cons k ks =>
          simp only [firstArgLe, Bool.or_eq_true, beq_iff_eq] at h ⊢
          rcases h with hkb | rfl
          · exact Or.inl (Term.blt_trans k b a hkb hba)
          · exact Or.inl hba

@[inherit_doc firstArgLe_mono]
theorem filter_firstArgLe_le {d : FDatabase} {a b : Term}
    (h : b = a ∨ Term.blt b a = true) :
    (d.terms.filter (firstArgLe b)).length ≤ (d.terms.filter (firstArgLe a)).length := by
  rcases h with rfl | hlt
  · exact le_refl _
  · exact (List.monotone_filter_right _ fun t ht => firstArgLe_mono hlt ht).length_le

end FDatabase

/-- A pair of a list zipped with itself is diagonal. -/
theorem mem_zip_self {α : Type _} : ∀ {xs : List α} {q : α × α},
    q ∈ xs.zip xs → q.1 = q.2 ∧ q.1 ∈ xs
  | [], _, h => by simp at h
  | x :: xs, q, h => by
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨rfl, List.mem_cons_self⟩
      · exact ⟨(mem_zip_self h).1, List.mem_cons_of_mem _ (mem_zip_self h).2⟩

/-- A key tuple is congruent to itself as soon as the closure records its columns. -/
theorem congrKeys_self {cl : Finset (Term × Term)} {as : List Term}
    (h : ∀ a ∈ as, (a, a) ∈ cl) : FDatabase.congrKeys cl as as = true := by
  simp only [FDatabase.congrKeys, FDatabase.congrTuple, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, decide_eq_true_eq]
  intro q hq
  obtain ⟨heq, hmem⟩ := mem_zip_self hq
  rw [show q = (q.1, q.1) from Prod.ext rfl heq.symm]
  exact h q.1 hmem

/-- Evaluated columns record a complete atom at a declared head. -/
theorem execAction_atom_of_eval {d : FDatabase} {f : FnName} {cols : List Expr}
    {ts : List Term} (hd : (d.sig f).isSome = true)
    (hev : Expr.evalList d.sig cols d.env = some ts) :
    execAction d (.expr (.app f cols)) = some (d.addAtom (.app f ts)) := by
  simp only [execAction, Expr.evalAtom, hd, if_true, hev, Option.map_some]

/-- **A row of a `:merge` function makes its own atom hold**, at the values its columns are.
The converse of `mem_terms_of_patternHolds_entry`, and what says that lemma — and the three
families over it — is not vacuous. The only closure facts it needs are reflexive, so nothing
here asks the kernel for a congruence closure. -/
theorem patternHolds_entry_of_mem_rows {d : FDatabase} {vs as : List Expr} {f : FnName}
    {σ : Env} {ts us : List Term} (he : (Expr.app f (as ++ vs)).entry d.sig = some (f, as, vs))
    (hats : Expr.evalList d.sig as σ = some ts)
    (hvus : Expr.evalList d.sig vs σ = some us)
    (hrow : (⟨f, ts, us⟩ : Row) ∈ d.rows) (hcol : ∀ c ∈ ts ++ us, c ∈ d.terms) :
    patternHolds d (.expr (.app f (as ++ vs))) σ = true := by
  have hrefl : ∀ c ∈ ts ++ us, (c, c) ∈ ((d.addTerms ts).addTerms us).closureF := by
    intro c hc
    exact FDatabase.mem_closureF_iff.mpr (Cong.assert (Or.inl ⟨rfl,
      FDatabase.mem_addTerms_terms (FDatabase.mem_addTerms_terms (hcol c hc))⟩))
  have hct : ∀ (xs : List Term),
      (∀ c ∈ xs, (c, c) ∈ ((d.addTerms ts).addTerms us).closureF) →
      FDatabase.congrTuple ((d.addTerms ts).addTerms us).closureF xs xs = true := by
    intro xs hxs
    refine Bool.and_eq_true_iff.mpr ⟨by simp, List.all_eq_true.mpr (fun q hq => ?_)⟩
    obtain ⟨a, b⟩ := q
    obtain ⟨heq, hmem⟩ := mem_zip_self hq
    simp only at heq hmem
    subst heq
    simpa using hxs a hmem
  simp only [patternHolds, he, hvus, hats, List.any_eq_true]
  refine ⟨⟨f, ts, us⟩, hrow, Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨by simp, ?_⟩, ?_⟩⟩
  · exact hct ts (fun c hc => hrefl c (List.mem_append_left _ hc))
  · exact hct us (fun c hc => hrefl c (List.mem_append_right _ hc))

end Egglog
