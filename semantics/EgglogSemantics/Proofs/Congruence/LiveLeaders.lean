import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.LiveTables
import EgglogSemantics.Proofs.Congruence.Properties

/-!
# Leader lookup in current tables

A merge-normal table has one output tuple per congruent key. In particular, a current
UF self-parent certifies a root: no competing parent or nontrivial parent path can
leave it. These statements use mathematical databases only.
-/

namespace Egglog

/-- Normalized outputs agree even when the lookup keys are merely congruent. -/
theorem MergeSaturated.out_functional {d : Database} (hn : MergeSaturated d)
    {f : FnName} {as bs old new : List Term} (hk : CongList d as bs)
    (ha : d.Out f as old) (hb : d.Out f bs new) : old = new := by
  obtain ⟨cs, hac, ha⟩ := ha
  obtain ⟨ds, hbd, hb⟩ := hb
  exact congrArg Entry.value
    (hn.unique _ ha _ hb rfl (hac.symm.trans (hk.trans hbd)))

/-- An exact-key lookup has a unique current output. -/
theorem MergeSaturated.out_unique {d : Database} (hn : MergeSaturated d)
    {f : FnName} {as old new : List Term}
    (ha : d.Out f as old) (hb : d.Out f as new) : old = new := by
  obtain ⟨cs, hc, hr⟩ := ha
  exact hn.out_functional (hc.trans hc.symm) ⟨cs, hc, hr⟩ hb

namespace Congruence.Live

/-- A successful generated UF atom reads the actual current tuple. The width premise
is the generated table-shape invariant, rather than a claim about malformed stores. -/
theorem uf_match_out {d : Database} (hd : d.Diag) (hs : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1))
    (hwidth : ∀ row ∈ d.entries, row.name = ufName → row.key.length = 1)
    {σ : Env} {v w : Var} {a r : Term}
    (ha : Env.lookup v σ = some a) (hr : Env.lookup w σ = some r)
    (hm : Matches d (.expr (.app ufName [.var v, .var w])) σ) :
    d.Out ufName [a] [r] := by
  have he : (Expr.app ufName [.var v, .var w]).entry d.sig =
      some (ufName, [Expr.var v], [Expr.var w]) := by
    simp [Expr.entry, huf, tableDecl]
  have hv : (Expr.app ufName [.var v, .var w]).eval d.sig σ = none := by
    simp [Expr.eval, Signature.IsCtor, huf, tableDecl]
  have hk : Expr.evalList d.sig [Expr.var v] σ = some [a] := by
    simp [Expr.evalList, Expr.eval, ha]
  have ho : Expr.evalList d.sig [Expr.var w] σ = some [r] := by
    simp [Expr.evalList, Expr.eval, hr]
  obtain ⟨row, hrow, hn, hc⟩ := LiveTables.table_match_current he hv hk ho hm
  have hcols : row.key ++ row.value = [a, r] :=
    (CongList.eq_of_diag (hd.withOperands _) hc).symm
  have hlen := hwidth row hrow hn
  have hkey : row.key = [a] := by
    calc
      row.key = (row.key ++ row.value).take row.key.length := by simp
      _ = [a] := by rw [hlen, hcols]; rfl
  have hvalue : row.value = [r] := by
    calc
      row.value = (row.key ++ row.value).drop row.key.length := by simp
      _ = [r] := by rw [hlen, hcols]; rfl
  have hroweq : row = ⟨ufName, [a], [r]⟩ := by
    cases row
    cases hn
    cases hkey
    cases hvalue
    rfl
  have hexists : a ∈ d.terms :=
    hs.columns row (Or.inl hrow) a (by rw [Entry.columns, hcols]; simp)
  exact ⟨[a], .cons hexists .nil, hroweq ▸ hrow⟩

/-- Unlike a historical self-loop, a current self-parent rules out any other parent. -/
theorem self_parent_only {d : Database} (hn : MergeSaturated d) {r p : Term}
    (hr : d.Out ufName [r] [r]) (hp : d.Out ufName [r] [p]) : p = r := by
  exact List.singleton_inj.mp (hn.out_unique hp hr)

/-- A parent walk starting at a certified root cannot reach another term. -/
theorem walk_from_self_parent {d : Database} (hn : MergeSaturated d) {r p : Term}
    (hr : d.Out ufName [r] [r])
    (hw : Relation.ReflTransGen (fun a b => d.Out ufName [a] [b]) r p) : p = r := by
  induction hw with
  | refl => rfl
  | tail _ hs ih => exact self_parent_only hn hr (ih ▸ hs)

/-- The two positive lookups used by `leaderQuery` select a unique rooted parent. -/
theorem guarded_leader_unique {d : Database} (hn : MergeSaturated d) {a r s : Term}
    (har : d.Out ufName [a] [r]) (hrr : d.Out ufName [r] [r])
    (has : d.Out ufName [a] [s]) :
    s = r ∧ ∀ p, d.Out ufName [r] [p] → p = r :=
  ⟨List.singleton_inj.mp (hn.out_unique has har), fun _ => self_parent_only hn hrr⟩

/-- The congruence compiler still uses no built-in equality between distinct ids. -/
theorem compiled_execution_diagonal {P : Program} {d : Database}
    (h : ProgramStep Database.empty (encode P) d) : d.Diag :=
  (h.noUnions Database.NoUnions.empty (encode_unionFree P)).diag

end Congruence.Live
end Egglog
