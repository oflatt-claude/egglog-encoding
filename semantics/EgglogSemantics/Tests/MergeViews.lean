import EgglogSemantics.Proofs.Congruence.LiveNormalization
import EgglogSemantics.Proofs.Diagonal

/-! Generated minimum merges terminate, but their current UF rows need not be confluent.
Starting with `4↦1, 4↦2, 4↦3`, two merge orders leave respectively `3↦1` and `3↦2`.
A computed query view therefore remains relational; all query atoms must share one view.
The regression uses actual merge bodies and finite normalization derivations. -/

namespace Egglog.Tests.MergeViews

open Egglog.Congruence Egglog.Congruence.Live

private def val (n : Nat) : Term := .lit (.int n)
private def row (k v : Nat) : Entry := ⟨ufName, [val k], [val v]⟩
private abbrev small (n : Nat) : Prop := n ∈ [1, 2, 3, 4]

private def state (rows : Set Entry) (ρ : Env := []) : Database where
  sig := fun f => if f = ufName then some (tableDecl 1) else none
  eqs := {(val 1, val 1), (val 2, val 2), (val 3, val 3), (val 4, val 4)}
  entries := rows
  env := ρ
  rules := ∅

private theorem held {rows : Set Entry} {ρ : Env} {n : Nat} (hn : small n) :
    (val n, val n) ∈ (state rows ρ).eqs := by
  simp only [small, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [state]

private theorem add_val {d : Database} {n : Nat} (hn : (val n, val n) ∈ d.eqs) :
    d.addTerm (val n) = d := by
  have he : d.eqs ∪ {(s, s) | s ∈ (val n).subterms} = d.eqs := by
    apply Set.union_eq_left.mpr
    rintro p ⟨s, hs, rfl⟩
    have hs' : s = val n := by simpa [val] using hs
    simpa [hs'] using hn
  simp only [Database.addTerm, he]

private theorem put_state (rows : Set Entry) (ρ : Env) {k v : Nat}
    (hk : small k) (hv : small v) :
    (state rows ρ).putEntry (row k v) = state (insert (row k v) rows) ρ := by
  have hk' := add_val (held (rows := rows) (ρ := ρ) hk)
  have hv' := add_val (held (rows := rows) (ρ := ρ) hv)
  simp only [Database.putEntry, row, Entry.columns, Database.addTerms,
    List.singleton_append, List.foldl_cons, List.foldl_nil, hk', hv']
  rfl

private theorem state_diag (rows : Set Entry) (ρ : Env := []) : (state rows ρ).Diag := by
  intro p hp
  simp only [state, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

/-- One generated collision, with its two UF side effects retained. -/
private theorem collision (rows : Set Entry) {k a b : Nat}
    (hk : small k) (ha : small a) (hb : small b) (hne : a ≠ b)
    (hmin : Term.least (val a) (val b) = val a)
    (hra : row k a ∈ rows) (hrb : row k b ∈ rows) :
    MergeStep (state rows)
      (state (insert (row k a) (insert (row b a) (insert (row a a)
        ((rows \ {row k a}) \ {row k b}))))) := by
  let rest := (rows \ {row k a}) \ {row k b}
  let bodyRows := insert (row b a) (insert (row a a) rest)
  let ρ := mergeEnv ["old"] ["new"] [val a] [val b]
  have hbody : evalActions { state rest with env := ρ } mergeBody =
      some (state bodyRows ρ) := by
    have he := eval_mergeBody (d := state rest)
      (by simp [state]) (val a) (val b)
    rw [hmin] at he
    change evalActions (state rest ρ) mergeBody =
      some (((state rest ρ).putEntry (row a a)).putEntry (row b a)) at he
    rw [put_state rest ρ ha ha, put_state (insert (row a a) rest) ρ hb ha] at he
    exact he
  have hres : Expr.evalList (state bodyRows ρ).sig mergeResult (state bodyRows ρ).env =
      some [val a] := by
    simpa [state, mergeResult, Expr.evalList, Expr.eval, ρ, mergeEnv, Env.lookup] using
      congrArg (fun t => some [t]) hmin
  have hconf : MergeConflict (tableDecl 1) mergeBody [val a] [val b] := by
    have hvals : val a ≠ val b := by
      intro h
      have := Term.lit.inj h
      have := Lit.int.inj this
      exact hne (by exact_mod_cast this)
    simpa [MergeConflict, FnDecl.unchangedWidth, tableDecl, mergeBody] using hvals
  have hm : MergeValues (state rest) (tableDecl 1) [val a] [val b]
      (state bodyRows) [val a] := .changed rfl hconf hbody hres
  have hs := MergeStep.collide (db := state rows) (old := row k a) (new := row k b)
    (decl := tableDecl 1) hra hrb (by
      intro he
      have hv := congrArg Entry.value he
      simp only [row, List.singleton_inj, val, Term.lit.injEq, Lit.int.injEq] at hv
      exact hne (by exact_mod_cast hv)) rfl (by simp [state, row])
    (.cons (.assert (held hk)) .nil) hm
  change MergeStep (state rows) ((state bodyRows).putEntry (row k a)) at hs
  rw [put_state bodyRows [] hk ha] at hs
  exact hs

private def startRows : Set Entry := {row 4 1, row 4 2, row 4 3}
private def leftMiddle : Set Entry := {row 4 1, row 4 3, row 1 1, row 2 1}
private def rightMiddle : Set Entry := {row 4 1, row 4 2, row 2 2, row 3 2}
private def rightLast : Set Entry := {row 4 1, row 1 1, row 2 1, row 2 2, row 3 2}
private def leftRows : Set Entry := {row 4 1, row 1 1, row 2 1, row 3 1}
private def rightRows : Set Entry := {row 4 1, row 1 1, row 2 1, row 3 2}

private theorem left_first : MergeStep (state startRows) (state leftMiddle) := by
  convert collision startRows (k := 4) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [startRows]) (by simp [startRows]) using 1
  congr 1
  ext e
  simp [leftMiddle, startRows, row, val]
  aesop

private theorem left_second : MergeStep (state leftMiddle) (state leftRows) := by
  convert collision leftMiddle (k := 4) (a := 1) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [leftMiddle]) (by simp [leftMiddle]) using 1
  congr 1
  ext e
  simp [leftRows, leftMiddle, row, val]
  aesop

private theorem right_first : MergeStep (state startRows) (state rightMiddle) := by
  convert collision startRows (k := 4) (a := 2) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [startRows]) (by simp [startRows]) using 1
  congr 1
  ext e
  simp [rightMiddle, startRows, row, val]
  aesop

private theorem right_second : MergeStep (state rightMiddle) (state rightLast) := by
  convert collision rightMiddle (k := 4) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [rightMiddle]) (by simp [rightMiddle]) using 1
  congr 1
  ext e
  simp [rightLast, rightMiddle, row, val]
  aesop

private theorem right_third : MergeStep (state rightLast) (state rightRows) := by
  convert collision rightLast (k := 2) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [rightLast]) (by simp [rightLast]) using 1
  congr 1
  ext e
  simp [rightRows, rightLast, row, val]
  aesop

private theorem left_normal : MergeNormal (state leftRows) := by
  intro a ha b hb _ hk
  have he := CongList.eq_of_diag (state_diag leftRows) hk
  simp only [state, leftRows, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> simp_all [row, val]

private theorem right_normal : MergeNormal (state rightRows) := by
  intro a ha b hb _ hk
  have he := CongList.eq_of_diag (state_diag rightRows) hk
  simp only [state, rightRows, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> simp_all [row, val]

/-- A legal finite generated store has two completed merges with different UF lookups.
Thus termination cannot justify treating interpretation as a unique database view. -/
theorem distinct_normalized_views :
    ∃ d left right : Database, State d ∧ d.Diag ∧
      MergeNormalize d left ∧ MergeNormalize d right ∧
      left.Out ufName [val 3] [val 1] ∧ ¬ right.Out ufName [val 3] [val 1] := by
  refine ⟨state startRows, state leftRows, state rightRows, ?_, state_diag _,
    ⟨(Relation.ReflTransGen.single left_first).tail left_second, left_normal⟩,
    ⟨((Relation.ReflTransGen.single right_first).tail right_second).tail right_third,
      right_normal⟩, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, by simp [state], ?_⟩
    · simp [state]
    · simp [state, startRows]
    · simp [state]
    · intro e he
      simp only [state, startRows, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;>
        exact ⟨by simp [state, row], ⟨_, rfl⟩⟩
  · exact ⟨[val 3], .cons (.assert (held (by decide))) .nil, by simp [state, leftRows, row]⟩
  · rintro ⟨ks, hk, hr⟩
    have he : [val 3] = ks := CongList.eq_of_diag (state_diag rightRows) hk
    rw [← he] at hr
    simp [state, rightRows, row, val] at hr

end Egglog.Tests.MergeViews
