import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Proofs.Eval

namespace Egglog.Provenance

private theorem actions_eq_self {db : Database} {as : List Action}
    (h : ∀ a ∈ as, evalAction db a = some db) : evalActions db as = some db := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [evalActions, h a (by simp), Option.bind_some]
      exact ih (fun a ha => h a (by simp [ha]))

private theorem unionFree_mem {as : List Action} (h : Actions.UnionFree as)
    {a : Action} (ha : a ∈ as) : a.UnionFree := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact ih h.2 ha

private theorem mergeBody_equal_data {db : Database} {f : FnName}
    {oldVars newVars : List Var} {body : List Action} {values : List Term} {proof : Term}
    (hu : Actions.UnionFree body)
    (ho : Expr.evalList db.sig (oldVars.map Expr.var) db.env = some values)
    (hn : Expr.evalList db.sig (newVars.map Expr.var) db.env = some values)
    (hp : (Expr.var (proofVar 0)).eval db.sig db.env = some proof)
    (hh : (proof, proof) ∈ db.eqs) :
    evalActions db (encodeMergeBody f oldVars newVars body) = some db := by
  have hkeep : db.addTerm proof = db := by
    unfold Database.addTerm
    simp only [Set.insert_eq_of_mem hh]
  apply actions_eq_self
  intro a ha
  obtain ⟨⟨source, j⟩, hm, rfl⟩ := List.mem_map.mp ha
  have hs := unionFree_mem hu (List.fst_mem_of_mem_zipIdx hm)
  cases source with
  | union _ _ => exact hs.elim
  | expr e =>
      cases e <;>
        simp [encodeAction, evalAction, Expr.evalAtom, ho, hn, hp, hkeep]

private theorem evalList_select {sig : Signature} {σ : Env}
    {lhs rhs : List Expr} {values : List Term}
    (hl : Expr.evalList sig lhs σ = some values)
    (hr : Expr.evalList sig rhs σ = some values) (pairs : List (Var × Expr)) :
    Expr.evalList sig (pairs.map fun ve => Expr.ite lhs rhs (.var ve.1) ve.2) σ =
      Expr.evalList sig (pairs.map fun ve => Expr.var ve.1) σ := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih => simp [Expr.eval, hl, hr, ih]

private theorem mergeResult_equal_data {db : Database} {f : FnName}
    {oldVars newVars : List Var} {res : List Expr} {values : List Term} {proof : Term}
    (hw : oldVars.length = res.length)
    (ho : Expr.evalList db.sig (oldVars.map Expr.var) db.env = some values)
    (hn : Expr.evalList db.sig (newVars.map Expr.var) db.env = some values)
    (hp : (Expr.var (proofVar 0)).eval db.sig db.env = some proof) :
    Expr.evalList db.sig (encodeMergeResult f oldVars newVars res) db.env =
      some (values ++ [proof]) := by
  have hmap : (oldVars.zip res).map (fun ve => Expr.var ve.1) = oldVars.map Expr.var := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map Expr.var) (List.map_fst_zip (Nat.le_of_eq hw))
  simp only [encodeMergeResult, Expr.evalList_append_map]
  rw [evalList_select ho hn, hmap, ho]
  have hp' : Env.lookup (proofVar 0) db.env = some proof := hp
  simp [Expr.evalList, Expr.eval, ho, hn, hp']

/-- Equal data retains its proof; the input rows already retain that proof in the store. -/
theorem encodedMerge_equal_data {db : Database} {f : FnName}
    {oldVars newVars : List Var} {body : List Action} {res : List Expr}
    {values : List Term} {proof : Term}
    (hu : Actions.UnionFree body) (hw : oldVars.length = res.length)
    (ho : Expr.evalList db.sig (oldVars.map Expr.var) db.env = some values)
    (hn : Expr.evalList db.sig (newVars.map Expr.var) db.env = some values)
    (hp : (Expr.var (proofVar 0)).eval db.sig db.env = some proof)
    (hh : (proof, proof) ∈ db.eqs) :
    evalMerge db (encodeMergeBody f oldVars newVars body)
      (encodeMergeResult f oldVars newVars res) = some (db, values ++ [proof]) := by
  simp [evalMerge, mergeBody_equal_data hu ho hn hp hh,
    mergeResult_equal_data hw ho hn hp]

/-- A changed store or output requires different data inputs. -/
theorem encodedMerge_data_distinct {db d : Database} {f : FnName}
    {oldVars newVars : List Var} {body : List Action} {res : List Expr}
    {old new vs : List Term} {proof : Term}
    (hu : Actions.UnionFree body) (hw : oldVars.length = res.length)
    (ho : Expr.evalList db.sig (oldVars.map Expr.var) db.env = some old)
    (hn : Expr.evalList db.sig (newVars.map Expr.var) db.env = some new)
    (hp : (Expr.var (proofVar 0)).eval db.sig db.env = some proof)
    (hh : (proof, proof) ∈ db.eqs)
    (hr : evalMerge db (encodeMergeBody f oldVars newVars body)
      (encodeMergeResult f oldVars newVars res) = some (d, vs))
    (hc : d ≠ db ∨ vs ≠ old ++ [proof]) : old ≠ new := by
  intro he
  subst new
  rw [encodedMerge_equal_data hu hw ho hn hp hh] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
  exact hc.elim (fun h => h rfl) (fun h => h rfl)

end Egglog.Provenance
