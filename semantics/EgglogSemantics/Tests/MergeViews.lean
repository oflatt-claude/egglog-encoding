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
  eqs := {(val 1, val 1), (val 2, val 2), (val 3, val 3), (val 4, val 4)} ∪
    {(r.atom, r.atom) | r ∈ rows}
  env := ρ
  rules := ∅

private theorem held {rows : Set Entry} {ρ : Env} {n : Nat} (hn : small n) :
    (val n, val n) ∈ (state rows ρ).eqs := by
  simp only [small, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> simp [state]

private theorem row_valid (k v : Nat) : (row k v).Valid (state ∅).sig := by
  refine ⟨tableDecl 1, by simp [state, row], by simp [tableDecl], rfl, rfl, ?_⟩
  simp [Entry.columns, row, val, Term.IsValue, Term.isValue]

private theorem state_entries {rows : Set Entry} {ρ : Env}
    (hr : ∀ r ∈ rows, r.Valid (state ∅).sig) : (state rows ρ).entries = rows := by
  apply Database.entries_eq_of_packed (d := state rows ρ) rfl _ hr
  rintro p (rfl | rfl | rfl | rfl) <;> rfl

private theorem erase_state (rows : Set Entry) (ρ : Env) (r : Entry)
    (hr : r.Valid (state ∅).sig) (hall : ∀ e ∈ rows, e.Valid (state ∅).sig)
    (hcols : ∀ t ∈ r.columns, (t, t) ∈ (state ∅ ρ).eqs) :
    (state rows ρ).eraseEntry r = state (rows \ {r}) ρ := by
  have hn : ∀ p ∈ ({(val 1, val 1), (val 2, val 2), (val 3, val 3),
      (val 4, val 4)} : Set (Term × Term)), p ≠ (r.atom, r.atom) := by
    rintro p (rfl | rfl | rfl | rfl) he <;> simp [val, Entry.atom] at he
  unfold Database.eraseEntry state
  congr 1
  ext p
  constructor
  · rintro (⟨hp | ⟨e, he, rfl⟩, hne⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨e, ⟨he, fun heq => hne (by rw [show e = r from heq]; rfl)⟩, rfl⟩
    · have hh := hcols t ht
      simpa only [state, Set.mem_union, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        false_and, exists_false, or_false] using Or.inl hh
  · rintro (hp | ⟨e, ⟨he, hne⟩, rfl⟩)
    · exact Or.inl ⟨Or.inl hp, hn p hp⟩
    · refine Or.inl ⟨Or.inr ⟨e, he, rfl⟩, ?_⟩
      intro heq
      exact hne ((hall e he).atom_injective hr (congrArg Prod.fst heq))

private theorem put_state (rows : Set Entry) (ρ : Env) {k v : Nat} :
    (state rows ρ).putEntry (row k v) = state (insert (row k v) rows) ρ := by
  apply Database.ext <;> try rfl
  change insert ((row k v).atom, (row k v).atom) (state rows ρ).eqs = _
  ext p
  constructor
  · rintro (rfl | hp)
    · exact Or.inr ⟨row k v, Or.inl rfl, rfl⟩
    · rcases hp with hp | ⟨e, he, rfl⟩
      · exact Or.inl hp
      · exact Or.inr ⟨e, Or.inr he, rfl⟩
  · rintro (hp | ⟨e, he, rfl⟩)
    · exact Or.inr (Or.inl hp)
    · rcases he with rfl | he
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨e, he, rfl⟩)

private theorem state_diag (rows : Set Entry) (ρ : Env := []) : (state rows ρ).Diag := by
  intro p hp
  rcases hp with hp | ⟨e, _, rfl⟩
  · rcases hp with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- One generated collision, with its two UF side effects retained. -/
private theorem collision (rows : Set Entry)
    (hall : ∀ e ∈ rows, e.Valid (state ∅).sig) {k a b : Nat}
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
      (by simp [state]) (val a) (val b) (by rfl) (by rfl)
    rw [hmin] at he
    change evalActions (state rest ρ) mergeBody =
      some (((state rest ρ).putEntry (row a a)).putEntry (row b a)) at he
    rw [put_state rest ρ, put_state (insert (row a a) rest) ρ] at he
    exact he
  have hres : Expr.evalList (state bodyRows ρ).sig mergeResult (state bodyRows ρ).env =
      some [val a] := by
    simpa [state, mergeResult, Expr.evalList, Expr.eval, ρ, mergeEnv, Env.lookup,
      Option.filter_some, Term.isValue, val] using
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
  have herase : ((state rows).eraseEntry (row k a)).eraseEntry (row k b) = state rest := by
    have hcols (v : Nat) (hv : small v) :
        ∀ t ∈ (row k v).columns, (t, t) ∈ (state ∅).eqs := by
      intro t ht
      simp only [row, Entry.columns, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [held hk, held hv]
    rw [erase_state rows [] (row k a) (row_valid k a) hall (hcols a ha),
      erase_state _ [] (row k b) (row_valid k b) (fun e he => hall e he.1) (hcols b hb)]
  have hs := MergeStep.collide (db := state rows) (old := row k a) (new := row k b)
    (decl := tableDecl 1) (by rwa [state_entries hall])
    (by rwa [state_entries hall]) (by
      intro he
      have hv := congrArg Entry.value he
      simp only [row, List.singleton_inj, val, Term.lit.injEq, Lit.int.injEq] at hv
      exact hne (by exact_mod_cast hv)) rfl (by simp [state, row])
    (.cons (.direct (held hk)) .nil) (herase.symm ▸ hm)
  change MergeStep (state rows) ((state bodyRows).putEntry (row k a)) at hs
  rw [put_state bodyRows []] at hs
  exact hs

private def startRows : Set Entry := {row 4 1, row 4 2, row 4 3}

private theorem startRows_valid : ∀ e ∈ startRows, e.Valid (state ∅).sig := by
  intro e he
  simp only [startRows, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl <;> exact row_valid _ _

private def leftMiddle : Set Entry := {row 4 1, row 4 3, row 1 1, row 2 1}

private theorem leftMiddle_valid : ∀ e ∈ leftMiddle, e.Valid (state ∅).sig := by
  intro e he
  simp only [leftMiddle, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact row_valid _ _

private def rightMiddle : Set Entry := {row 4 1, row 4 2, row 2 2, row 3 2}

private theorem rightMiddle_valid : ∀ e ∈ rightMiddle, e.Valid (state ∅).sig := by
  intro e he
  simp only [rightMiddle, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact row_valid _ _

private def rightLast : Set Entry := {row 4 1, row 1 1, row 2 1, row 2 2, row 3 2}

private theorem rightLast_valid : ∀ e ∈ rightLast, e.Valid (state ∅).sig := by
  intro e he
  simp only [rightLast, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact row_valid _ _

private def leftRows : Set Entry := {row 4 1, row 1 1, row 2 1, row 3 1}

private theorem leftRows_valid : ∀ e ∈ leftRows, e.Valid (state ∅).sig := by
  intro e he
  simp only [leftRows, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact row_valid _ _

private def rightRows : Set Entry := {row 4 1, row 1 1, row 2 1, row 3 2}

private theorem rightRows_valid : ∀ e ∈ rightRows, e.Valid (state ∅).sig := by
  intro e he
  simp only [rightRows, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact row_valid _ _


private theorem left_first : MergeStep (state startRows) (state leftMiddle) := by
  convert collision startRows startRows_valid (k := 4) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [startRows]) (by simp [startRows]) using 1
  congr 1
  ext e
  simp [leftMiddle, startRows, row, val]
  aesop

private theorem left_second : MergeStep (state leftMiddle) (state leftRows) := by
  convert collision leftMiddle leftMiddle_valid (k := 4) (a := 1) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [leftMiddle]) (by simp [leftMiddle]) using 1
  congr 1
  ext e
  simp [leftRows, leftMiddle, row, val]
  aesop

private theorem right_first : MergeStep (state startRows) (state rightMiddle) := by
  convert collision startRows startRows_valid (k := 4) (a := 2) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [startRows]) (by simp [startRows]) using 1
  congr 1
  ext e
  simp [rightMiddle, startRows, row, val]
  aesop

private theorem right_second : MergeStep (state rightMiddle) (state rightLast) := by
  convert collision rightMiddle rightMiddle_valid (k := 4) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [rightMiddle]) (by simp [rightMiddle]) using 1
  congr 1
  ext e
  simp [rightLast, rightMiddle, row, val]
  aesop

private theorem right_third : MergeStep (state rightLast) (state rightRows) := by
  convert collision rightLast rightLast_valid (k := 2) (a := 1) (b := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by simp [rightLast]) (by simp [rightLast]) using 1
  congr 1
  ext e
  simp [rightRows, rightLast, row, val]
  aesop

private theorem left_normal : MergeNormal (state leftRows) := by
  intro a ha b hb _ hk
  have he := CongList.eq_of_diag (state_diag leftRows) hk
  rw [state_entries leftRows_valid] at ha hb
  simp only [leftRows, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> simp_all [row, val]

private theorem right_normal : MergeNormal (state rightRows) := by
  intro a ha b hb _ hk
  have he := CongList.eq_of_diag (state_diag rightRows) hk
  rw [state_entries rightRows_valid] at ha hb
  simp only [rightRows, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
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
  · refine ⟨Database.FiniteStore.of_eqs_rules ?_ (by simp [state]), by simp [state], ?_⟩
    · exact (by simp : ({(val 1, val 1), (val 2, val 2), (val 3, val 3),
        (val 4, val 4)} : Set (Term × Term)).Finite).union
        ((by simp [startRows] : startRows.Finite).image fun r : Entry => (r.atom, r.atom))
    · intro e he
      rw [state_entries startRows_valid] at he
      simp only [startRows, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl <;>
        exact ⟨by simp [state, row], ⟨_, rfl⟩⟩
  · exact ⟨[val 3], .cons (.direct (held (by decide))) .nil,
      by rw [state_entries leftRows_valid]; simp [leftRows, row]⟩
  · rintro ⟨ks, hk, hr⟩
    have he : [val 3] = ks := CongList.eq_of_diag (state_diag rightRows) hk
    rw [← he] at hr
    rw [state_entries rightRows_valid] at hr
    simp [rightRows, row, val] at hr

end Egglog.Tests.MergeViews
