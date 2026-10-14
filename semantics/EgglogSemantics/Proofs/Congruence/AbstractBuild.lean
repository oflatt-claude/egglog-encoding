import EgglogSemantics.Proofs.ActionProgram
import EgglogSemantics.Proofs.Congruence.ActionExprs
import EgglogSemantics.Proofs.Congruence.SourceReads
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Source.Domain

/-! Compiled source actions preserve represented facts using mathematical evaluation. -/

namespace Egglog.Congruence.Abstract

private theorem evalActions_append_eq {d m e : Database} {as bs : List Action}
    (ha : evalActions d as = some m) (hb : evalActions m bs = some e) :
    evalActions d (as ++ bs) = some e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj ha; exact hb
  | cons a as ih =>
      obtain ⟨n, hn, ha⟩ := Option.bind_eq_some_iff.mp ha
      simpa only [List.cons_append, evalActions, hn, Option.bind_some] using ih ha

private theorem evalAction_atom_of_eval {d : Database} {f : FnName} {es : List Expr}
    {ts : List Term} (hf : (d.sig f).isSome = true)
    (he : Expr.evalList d.sig es d.env = some ts) :
    evalAction d (.expr (.app f es)) = some (d.addTerm (.app f ts)) := by
  simp only [evalAction, Expr.evalAtom, hf, if_true, he, Option.map_some]

private theorem out_addTerm {d : Database} (f : FnName) (cs : List Term) (i : Term) :
    (d.addTerm (.app f (cs ++ [i]))).Out f cs [i] := by
  refine ⟨cs, CongList.refl ?_, Database.mem_addTerm _ _⟩
  intro t ht
  exact Database.addTerm_terms ▸ Or.inr
    (Term.arg_subterms (List.mem_append_left _ ht) (Term.self_mem_subterms t))

mutual

/-- A source build executes at a reading substitution and represents its source result.
The target id is the head expression evaluated at target ids, not the source term itself. -/
theorem encodeBuild_reads {sig : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term} {d : Database}, e.OrderingFree →
      (∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d σ d.env → e.eval sig σ = some t →
      ∃ i d', e.eval d.sig d.env = some i ∧
        evalActions d (encodeBuild e) = some d' ∧ ViewRepr d' t i
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
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      have hcols : Expr.evalList m.sig (args ++ [.app f args]) m.env =
          some (is ++ [.app f is]) := by
        rw [hsig, henv]
        rw [Expr.evalList_append_map, his]
        simp only [Expr.evalList, htarget, Option.bind_some, Option.map_some]
      have hwrite := evalAction_atom_of_eval
        (by rw [hsig]; exact hd (f, args.length) List.mem_cons_self) hcols
      refine ⟨.app f is, m.addTerm (.app (viewName f) (is ++ [.app f is])),
        htarget, evalActions_append_eq hm ?_, ?_⟩
      · simp only [evalActions, hwrite, Option.bind_some]
      · exact .app (hviews.mono (evalAction_contained hwrite))
          (out_addTerm (viewName f) is (.app f is))

@[inherit_doc encodeBuild_reads]
theorem encodeBuildArgs_reads {sig : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term} {d : Database}, Expr.OrderingFreeList es →
      (∀ f ∈ Expr.fnsList es, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ Expr.ctorsList es, (d.sig (viewName fk.1)).isSome = true) →
      Env.Reads d σ d.env → Expr.evalList sig es σ = some ts →
      ∃ is d', Expr.evalList d.sig es d.env = some is ∧
        evalActions d (encodeBuildArgs es) = some d' ∧ ViewReprList d' ts is
  | [], _, d, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], d, rfl, rfl, .nil⟩
  | e :: es, _, d, hp, hc, hd, hρ, he => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨i, m, hi, hm, hv⟩ := encodeBuild_reads e (Expr.orderingFreeList_cons hp).1
        (fun f hf => hc f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) hρ ht
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      obtain ⟨is, d', his, hr, hvs⟩ := encodeBuildArgs_reads (d := m) es
        (Expr.orderingFreeList_cons hp).2
        (fun f hf hctor => by rw [hsig]; exact hc f (by simp [Expr.fnsList, hf]) hctor)
        (fun fk hk => by rw [hsig]; exact hd fk (by simp [Expr.ctorsList, hk]))
        (by rw [henv]; exact hρ.mono (evalActions_contained hm)) hts
      rw [hsig, henv] at his
      refine ⟨i :: is, d', ?_, evalActions_append_eq hm hr,
        .cons (hv.mono (evalActions_contained hr)) hvs⟩
      simp only [Expr.evalList, hi, Option.bind_some, his, Option.map_some]

end

/-- The endpoint readings of an encoded union are joined by an explicit UF entry: the link
from the larger id, the other link being a self-loop. -/
theorem encodeUnion_reads {sig : Signature} {σ : Env} {a b : Expr} {ta tb : Term}
    {d : Database} (hp : ∀ e ∈ [a, b], e.OrderingFree)
    (hc : ∀ e ∈ [a, b], ∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d σ d.env)
    (ha : a.eval sig σ = some ta) (hb : b.eval sig σ = some tb) :
    ∃ i j d', evalActions d (encodeAction (.union a b)) = some d' ∧
      ViewRepr d' ta i ∧ ViewRepr d' tb j ∧
      (d'.Out ufName [i] [j] ∨ d'.Out ufName [j] [i]) := by
  obtain ⟨i, m, hi, hm, hia⟩ := encodeBuild_reads a
    (hp a (by simp)) (hc a (by simp)) (hd a (by simp)) hρ ha
  have hsig := evalActions_sig hm
  have henv := evalActions_env hm
  obtain ⟨j, n, hj, hn, hjb⟩ := encodeBuild_reads (d := m) b
    (hp b (by simp))
    (fun f hf hctor => by rw [hsig]; exact hc b (by simp) f hf hctor)
    (fun fk hk => by rw [hsig]; exact hd b (by simp) fk hk)
    (by rw [henv]; exact hρ.mono (evalActions_contained hm)) hb
  have hbuild := evalActions_append_eq hm hn
  rw [hsig, henv] at hj
  have hsig' := evalActions_sig hbuild
  have henv' := evalActions_env hbuild
  have hi' : a.eval n.sig n.env = some i := by rw [hsig', henv']; exact hi
  have hj' : b.eval n.sig n.env = some j := by rw [hsig', henv']; exact hj
  have hmin := eval_min_ids hi' hj'
  have hcols₁ : Expr.evalList n.sig [a, .min a b] n.env = some [i, lowerId i j] := by
    simp only [Expr.evalList, hi', hmin, Option.bind_some, Option.map_some]
  have huf' : (n.sig ufName).isSome = true := by rw [hsig']; exact huf
  have hwrite₁ := evalAction_atom_of_eval huf' hcols₁
  have hcols₂ : Expr.evalList (n.addTerm (.app ufName [i, lowerId i j])).sig [b, .min a b]
      (n.addTerm (.app ufName [i, lowerId i j])).env = some [j, lowerId i j] := by
    change Expr.evalList n.sig [b, .min a b] n.env = _
    simp only [Expr.evalList, hj', hmin, Option.bind_some, Option.map_some]
  have hwrite₂ := evalAction_atom_of_eval (d := n.addTerm (.app ufName [i, lowerId i j]))
    huf' hcols₂
  refine ⟨i, j, (n.addTerm (.app ufName [i, lowerId i j])).addTerm (.app ufName [j, lowerId i j]),
    evalActions_append_eq hbuild ?_, ?_, ?_, ?_⟩
  · simp only [evalActions, hwrite₁, Option.bind_some, hwrite₂]
  · exact ((hia.mono (evalActions_contained hn)).mono
      (evalAction_contained hwrite₁)).mono
      (evalAction_contained hwrite₂)
  · exact (hjb.mono (evalAction_contained hwrite₁)).mono
      (evalAction_contained hwrite₂)
  · have ho₁ := (out_addTerm ufName [i] (lowerId i j)).mono
      (evalAction_contained hwrite₂)
    have ho₂ := out_addTerm (d := n.addTerm (.app ufName [i, lowerId i j]))
      ufName [j] (lowerId i j)
    rcases ids_paired i j with ⟨_, hl⟩ | ⟨_, hl⟩
    · exact Or.inl (by simpa only [List.cons_append, List.nil_append, hl] using ho₁)
    · exact Or.inr (by simpa only [List.cons_append, List.nil_append, hl] using ho₂)

/-- Every successful source action has a successful compiled execution carrying its
new existence and union facts. This does not require rebuilding until the block ends. -/
theorem encodeAction_reads {src post : Database} {d : Database} {a : Action}
    (hcs : src.sig.AllConstructors) (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d src.env d.env)
    (h : SourceReads d src) (run : evalAction src a = some post) :
    ∃ d', evalActions d (encodeAction a) = some d' ∧ SourceReads d' post := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    obtain ⟨i, d', _, hr, hv⟩ := encodeBuild_reads e (hp e (by simp [actionExprs]))
      (hc e (by simp [actionExprs])) (hd e (by simp [actionExprs])) hρ he
    exact ⟨d', hr, (h.mono (evalActions_contained hr)).addTerm hv⟩
  · obtain ⟨i, j, d', hr, hi, hj, ho⟩ := encodeUnion_reads hp hc hd huf hρ ha hb
    exact ⟨d', hr, (h.mono (evalActions_contained hr)).addEq hi hj ho⟩

/-- Rule heads and global action blocks execute while retaining all source facts. -/
theorem encodeActions_reads {src post : Database} {d : Database} {as : List Action}
    (hcs : src.sig.AllConstructors) (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d src.env d.env)
    (h : SourceReads d src) (run : evalActions src as = some post) :
    ∃ d', evalActions d (encodeActions as) = some d' ∧ SourceReads d' post := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj run
      exact ⟨d, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨m, hfirst, hmid⟩ := encodeAction_reads hcs (hp a List.mem_cons_self)
        (hc a List.mem_cons_self) (hd a List.mem_cons_self) huf hρ h hm
      have hsig := evalActions_sig hfirst
      have henv := evalActions_env hfirst
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
        (by rw [hsrcenv, henv]; exact hρ.mono (evalActions_contained hfirst))
        hmid hr
      exact ⟨d', evalActions_append_eq hfirst hrest, hpost⟩

/-- Command-level merge phases between emitted writes cannot lose any source reading. -/
theorem encodeAction_program_reads {src post d D : Database} {a : Action}
    (hcs : src.sig.AllConstructors) (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, (d.sig (viewName fk.1)).isSome = true)
    (huf : (d.sig ufName).isSome = true) (hρ : Env.Reads d src.env d.env)
    (h : SourceReads d src) (hs : evalAction src a = some post)
    (ht : ProgramStep d ((encodeAction a).map Cmd.action) D) : SourceReads D post := by
  obtain ⟨m, hm, hreads⟩ := encodeAction_reads hcs hp hc hd huf hρ h hs
  exact hreads.mono (evalActions_contained_programStep hm ht)

end Egglog.Congruence.Abstract
