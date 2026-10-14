import EgglogSemantics.Proofs.Congruence.Build

/-! Forward execution of compiled source heads, preserving existence and recorded unions. -/

namespace Egglog.Congruence

mutual

/-- Historical readings survive every operation that retains the recorded equations. -/
theorem ViewRepr.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) :
    ∀ {a i : Term}, ViewRepr d₁ a i → ViewRepr d₂ a i
  | _, _, .lit => .lit
  | _, _, .app hs ho => .app (ViewReprList.mono h hs) (ho.mono h)

@[inherit_doc ViewRepr.mono]
theorem ViewReprList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) :
    ∀ {as is : List Term}, ViewReprList d₁ as is → ViewReprList d₂ as is
  | _, _, .nil => .nil
  | _, _, .cons ha hs => .cons (ViewRepr.mono h ha) (ViewReprList.mono h hs)

end

/-- Head variables need a reading, which need not already be a canonical UF root. -/
def Env.Reads (d : Database) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t →
    ∃ i, Env.lookup v ρ = some i ∧ ViewRepr d t i

theorem Env.Reads.mono {d d' : Database} {σ ρ : Env} (h : Env.Reads d σ ρ)
    (hc : d.Contained d') : Env.Reads d' σ ρ := by
  intro v t ht
  obtain ⟨i, hi, hr⟩ := h v t ht
  exact ⟨i, hi, hr.mono hc⟩

private theorem out_addAtom (d : FDatabase) (f : FnName) (cs : List Term) (i : Term) :
    (d.addAtom (.app f (cs ++ [i]))).toDatabase.Out f cs [i] := by
  apply Database.out_self
  · change Term.app f (cs ++ [i]) ∈ (d.addTerm (.app f (cs ++ [i]))).toDatabase.terms
    rw [Egglog.FDatabase.toDatabase_terms]
    exact Egglog.FDatabase.mem_addTerm_terms.mpr (Or.inl ((Term.mem_subtermList _).mpr (.refl _)))
  · intro t ht
    change t ∈ (d.addTerm (.app f (cs ++ [i]))).toDatabase.terms
    rw [Egglog.FDatabase.toDatabase_terms]
    apply Egglog.FDatabase.mem_addTerm_terms.mpr
    exact Or.inl ((Term.mem_subtermList _).mpr
      (Term.IsSubterm.arg (List.mem_append_left _ ht) (.refl t)))

mutual

/-- A source build executes at a reading substitution and represents its source result.
The target id is the head expression evaluated at target ids, not the source term itself. -/
theorem encodeBuild_reads {sig : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term} {d : FDatabase},
      e.OrderingFree →
      (∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d.toDatabase σ d.env → e.eval sig σ = some t →
      ∃ i d', e.eval d.sig d.env = some i ∧
        execActions d (encodeBuild e) = some d' ∧ ViewRepr d'.toDatabase t i
  | .lit l, _, d, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨.lit l, d, rfl, rfl, .lit⟩
  | .var v, t, d, _, _, _, hρ, he => by
      obtain ⟨i, hi, hr⟩ := hρ v t he
      exact ⟨i, d, hi, rfl, hr⟩
  | .min _ _, _, _, hp, _, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .app f args, t, d, hp, hc, hd, hρ, he => by
      have hctor : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨is, m, his, hm, hviews⟩ := encodeBuildArgs_reads args
        (Expr.orderingFree_app hp)
        (fun g hg => hc g (by simp [Expr.fns, hg]))
        (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) hρ hts
      have htarget : (Expr.app f args).eval d.sig d.env = some (.app f is) := by
        rw [Expr.eval_app_ctor (hc f (by simp [Expr.fns]) hctor), his]; rfl
      have hsig := Egglog.FDatabase.execActions_sig hm
      have henv := Egglog.FDatabase.execActions_env hm
      have hcols : Expr.evalList m.sig (args ++ [.app f args]) m.env =
          some (is ++ [.app f is]) := by
        rw [hsig, henv]
        exact Expr.evalList_append_eq his (by
          simp only [Expr.evalList, htarget, Option.bind_some, Option.map_some])
      have hwrite := execAction_atom_of_eval
        (by rw [hsig]; exact hd (f, args.length) List.mem_cons_self) hcols
      refine ⟨.app f is, m.addAtom (.app (viewName f) (is ++ [.app f is])),
        htarget, execActions_append_eq hm ?_, ?_⟩
      · simp only [execActions, hwrite, Option.bind_some]
      · exact .app (hviews.mono (Egglog.FDatabase.execAction_contained hwrite))
          (out_addAtom m (viewName f) is (.app f is))

@[inherit_doc encodeBuild_reads]
theorem encodeBuildArgs_reads {sig : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term} {d : FDatabase},
      Expr.OrderingFreeList es →
      (∀ f ∈ Expr.fnsList es, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ Expr.ctorsList es, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d.toDatabase σ d.env → Expr.evalList sig es σ = some ts →
      ∃ is d', Expr.evalList d.sig es d.env = some is ∧
        execActions d (encodeBuildArgs es) = some d' ∧ ViewReprList d'.toDatabase ts is
  | [], _, d, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], d, rfl, rfl, .nil⟩
  | e :: es, _, d, hp, hc, hd, hρ, he => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨i, m, hi, hm, hv⟩ := encodeBuild_reads e (Expr.orderingFreeList_cons hp).1
        (fun f hf => hc f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) hρ ht
      have hsig := Egglog.FDatabase.execActions_sig hm
      have henv := Egglog.FDatabase.execActions_env hm
      obtain ⟨is, d', his, hr, hvs⟩ := encodeBuildArgs_reads (d := m) es
        (Expr.orderingFreeList_cons hp).2
        (fun f hf hctor => by rw [hsig]; exact hc f (by simp [Expr.fnsList, hf]) hctor)
        (fun fk hk => by rw [hsig]; exact hd fk (by simp [Expr.ctorsList, hk]))
        (by rw [henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hm)) hts
      rw [hsig, henv] at his
      refine ⟨i :: is, d', ?_, execActions_append_eq hm hr,
        .cons (hv.mono (Egglog.FDatabase.execActions_contained hr)) hvs⟩
      simp only [Expr.evalList, hi, Option.bind_some, his, Option.map_some]

end

/-- The endpoint readings of an encoded union are joined by an explicit UF entry: the link
from the larger id, the other link being a self-loop. -/
theorem encodeUnion_reads {sig : Signature} {σ : Env} {a b : Expr} {ta tb : Term}
    {d : FDatabase}
    (hp : ∀ e ∈ [a, b], e.OrderingFree)
    (hc : ∀ e ∈ [a, b], ∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase σ d.env)
    (ha : a.eval sig σ = some ta) (hb : b.eval sig σ = some tb) :
    ∃ i j d', execActions d (encodeAction (.union a b)) = some d' ∧
      ViewRepr d'.toDatabase ta i ∧ ViewRepr d'.toDatabase tb j ∧
      (d'.toDatabase.Out ufName [i] [j] ∨ d'.toDatabase.Out ufName [j] [i]) := by
  obtain ⟨i, m, hi, hm, hia⟩ := encodeBuild_reads a
    (hp a (by simp)) (hc a (by simp)) (hd a (by simp)) hρ ha
  have hsig := Egglog.FDatabase.execActions_sig hm
  have henv := Egglog.FDatabase.execActions_env hm
  obtain ⟨j, n, hj, hn, hjb⟩ := encodeBuild_reads (d := m) b
    (hp b (by simp))
    (fun f hf hctor => by rw [hsig]; exact hc b (by simp) f hf hctor)
    (fun fk hk => by rw [hsig]; exact hd b (by simp) fk hk)
    (by rw [henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hm)) hb
  have hbuild := execActions_append_eq hm hn
  rw [hsig, henv] at hj
  have hsig' := Egglog.FDatabase.execActions_sig hbuild
  have henv' := Egglog.FDatabase.execActions_env hbuild
  have hi' : a.eval n.sig n.env = some i := by rw [hsig', henv']; exact hi
  have hj' : b.eval n.sig n.env = some j := by rw [hsig', henv']; exact hj
  have hmin := eval_min_ids hi' hj'
  have hcols₁ : Expr.evalList n.sig [a, .min a b] n.env = some [i, lowerId i j] := by
    simp only [Expr.evalList, hi', hmin, Option.bind_some, Option.map_some]
  have huf' : (n.sig ufName).isSome = true := by rw [hsig']; exact huf
  have hwrite₁ := execAction_atom_of_eval huf' hcols₁
  have hcols₂ : Expr.evalList (n.addAtom (.app ufName [i, lowerId i j])).sig [b, .min a b]
      (n.addAtom (.app ufName [i, lowerId i j])).env = some [j, lowerId i j] := by
    change Expr.evalList n.sig [b, .min a b] n.env = _
    simp only [Expr.evalList, hj', hmin, Option.bind_some, Option.map_some]
  have hwrite₂ := execAction_atom_of_eval (d := n.addAtom (.app ufName [i, lowerId i j]))
    huf' hcols₂
  refine ⟨i, j, (n.addAtom (.app ufName [i, lowerId i j])).addAtom (.app ufName [j, lowerId i j]),
    execActions_append_eq hbuild ?_, ?_, ?_, ?_⟩
  · simp only [execActions, hwrite₁, Option.bind_some, hwrite₂]
  · exact ((hia.mono (Egglog.FDatabase.execActions_contained hn)).mono
      (Egglog.FDatabase.execAction_contained hwrite₁)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
  · exact (hjb.mono (Egglog.FDatabase.execAction_contained hwrite₁)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
  · have ho₁ := (out_addAtom n ufName [i] (lowerId i j)).mono
      (Egglog.FDatabase.execAction_contained hwrite₂)
    have ho₂ := out_addAtom (n.addAtom (.app ufName [i, lowerId i j])) ufName [j] (lowerId i j)
    rcases ids_paired i j with ⟨-, hl⟩ | ⟨-, hl⟩
    · exact Or.inl (by simpa only [List.cons_append, List.nil_append, hl] using ho₁)
    · exact Or.inr (by simpa only [List.cons_append, List.nil_append, hl] using ho₂)

theorem ViewReprList.mem_read {d : Database} : ∀ {as is : List Term},
    ViewReprList d as is → ∀ t ∈ as, ∃ i, ViewRepr d t i
  | _, _, .nil, _, ht => absurd ht (by simp)
  | _, _, .cons ha hs, _, ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨_, ha⟩
      · exact ViewReprList.mem_read hs _ ht

/-- Reading a parent already contains readings of every one of its source subterms. -/
theorem ViewRepr.subterms {d : Database} {t i : Term} (h : ViewRepr d t i) :
    ∀ s ∈ t.subterms, ∃ j, ViewRepr d s j := by
  intro s hs
  induction hs generalizing i with
  | refl => exact ⟨i, h⟩
  | arg hm _ ih =>
      cases h with
      | app hl _ =>
          obtain ⟨j, hj⟩ := hl.mem_read _ hm
          exact ih hj

/-- Monotone source facts carried between rebuilding fixed points. Every source union
retains the entry that recorded it, even after the live rows have changed. -/
structure SourceReads (d src : Database) : Prop where
  terms : ∀ t ∈ src.terms, ∃ i, ViewRepr d t i
  unions : UnionsJoined d src

theorem SourceReads.mono {d d' src : Database} (h : SourceReads d src)
    (hc : d.Contained d') : SourceReads d' src := by
  refine ⟨fun t ht => (h.terms t ht).imp fun _ hr => hr.mono hc, ?_⟩
  intro a b hab hne
  obtain ⟨i, j, hi, hj, ho⟩ := h.unions a b hab hne
  exact ⟨i, j, hi.mono hc, hj.mono hc, ho.imp (Database.Out.mono hc) (Database.Out.mono hc)⟩

/-- A smaller source state only asks for a subset of the already represented facts. -/
theorem SourceReads.restrict {d src src' : Database} (h : SourceReads d src)
    (hc : src'.Contained src) : SourceReads d src' :=
  ⟨fun t ht => h.terms t (hc.terms ht), fun a b hab => h.unions a b (hc.eqs hab)⟩

theorem SourceReads.addTerm {d src : Database} (h : SourceReads d src) {t i : Term}
    (ht : ViewRepr d t i) : SourceReads d (src.addTerm t) := by
  refine ⟨?_, fun a b hab hne => ?_⟩
  · intro s hs
    rcases Database.addTerm_terms ▸ hs with hs | hs
    · exact h.terms s hs
    · exact ht.subterms s hs
  · rcases Database.addTerm_eqs ▸ hab with hab | ⟨s, _, heq⟩
    · exact h.unions a b hab hne
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact (hne rfl).elim

theorem SourceReads.addEq {d src : Database} (h : SourceReads d src) {a b i j : Term}
    (ha : ViewRepr d a i) (hb : ViewRepr d b j)
    (ho : d.Out ufName [i] [j] ∨ d.Out ufName [j] [i]) : SourceReads d (src.addEq a b) := by
  have hterms := (h.addTerm ha).addTerm hb
  refine ⟨?_, fun x y hxy hne => ?_⟩
  · intro t ht
    apply hterms.terms t
    simpa only [Database.addTerm_terms] using Database.addEq_terms ▸ ht
  · rcases Database.addEq_eqs ▸ hxy with heq | hxy
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨i, j, ha, hb, ho⟩
    · exact hterms.unions x y hxy hne

/-- Every successful source action has a successful compiled execution carrying its
new existence and union facts. This does not require rebuilding until the block ends. -/
theorem encodeAction_reads {src post : Database} {d : FDatabase} {a : Action}
    (hcs : src.sig.AllConstructors)
    (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase src.env d.env)
    (h : SourceReads d.toDatabase src) (run : evalAction src a = some post) :
    ∃ d', execActions d (encodeAction a) = some d' ∧ SourceReads d'.toDatabase post := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    obtain ⟨i, d', _, hr, hv⟩ := encodeBuild_reads e (hp e (by simp [actionExprs]))
      (hc e (by simp [actionExprs])) (hd e (by simp [actionExprs])) hρ he
    exact ⟨d', hr, (h.mono (Egglog.FDatabase.execActions_contained hr)).addTerm hv⟩
  · obtain ⟨i, j, d', hr, hi, hj, ho⟩ := encodeUnion_reads hp hc hd huf hρ ha hb
    exact ⟨d', hr, (h.mono (Egglog.FDatabase.execActions_contained hr)).addEq hi hj ho⟩

/-- Rule heads and global action blocks execute while retaining all source facts. -/
theorem encodeActions_reads {src post : Database} {d : FDatabase} {as : List Action}
    (hcs : src.sig.AllConstructors)
    (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d.toDatabase src.env d.env)
    (h : SourceReads d.toDatabase src) (run : evalActions src as = some post) :
    ∃ d', execActions d (encodeActions as) = some d' ∧ SourceReads d'.toDatabase post := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj run
      exact ⟨d, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨m, hfirst, hmid⟩ := encodeAction_reads hcs (hp a List.mem_cons_self)
        (hc a List.mem_cons_self) (hd a List.mem_cons_self) huf hρ h hm
      have hsig := Egglog.FDatabase.execActions_sig hfirst
      have henv := Egglog.FDatabase.execActions_env hfirst
      have hsrcsig := evalAction_sig hm
      have hsrcenv := evalAction_env hm
      obtain ⟨d', hrest, hpost⟩ := ih
        (by rw [hsrcsig]; exact hcs)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha e he f hf hctor => by
          rw [hsig]; exact hc a (List.mem_cons_of_mem _ ha) e he f hf (hsrcsig ▸ hctor))
        (fun a ha e he fk hk => by
          rw [hsig]; exact hd a (List.mem_cons_of_mem _ ha) e he fk hk)
        (by rw [hsig]; exact huf)
        (by rw [hsrcenv, henv]; exact hρ.mono (Egglog.FDatabase.execActions_contained hfirst))
        hmid hr
      exact ⟨d', execActions_append_eq hfirst hrest, hpost⟩

end Egglog.Congruence
