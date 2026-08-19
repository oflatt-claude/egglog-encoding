import EgglogSemantics.Encoding.Encode
import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Merge

/-!
# The encoding correspondence: the claim, the decision procedure, and what they cost

`Encoding/Encode.lean` reads the target with `ViewRepr` and `SameClass`. `DiffTest.lean`
sweeps every pair of terms of every in-domain case for

```
Cong src a b  ↔  SameClass tgt a b
```

and reports agreement. This file is what makes those two the *same* claim: `sameClassF`
decides `SameClass` over an `FDatabase`, `sameClassF_iff` proves it, and `mem_closureF_iff`
(`Proofs/Interp.lean`) already does the source side. Without the two of them the sweep is
evidence about a different predicate than the theorem mentions.

## The two hypotheses the decision procedure needs

`sameClassF` reads the view tables the way `difftest` does, and that reading is exact only
under two conditions on the target — one per direction of the iff.

* **`SubtermClosed`**, for `sameClassF → SameClass`. `Database.Out` asks that the key
  columns be terms the database holds, which is subterm closure at the entry term. It is
  `Database.WF`'s own clause, and decidable, so a self-test can report it at the state it
  swept.
* **`EqsRefl`**, for `SameClass → sameClassF`. `Database.Out` reads the key up to
  congruence and the procedure reads it up to equality; the two agree exactly where the
  target asserts no equation but a reflexive one. `encode` emits no `union` — a source
  `union` becomes a `set` of a `@UF` edge — so its targets satisfy it, and
  `difftest correspond`'s `tgt-eqs` column is that measurement, 0 on every case.

Neither is an artefact: both are properties of the state the encoded program runs to, and
both are decided at the witness at the end of this file.

## What is proved, and what is not

* **Proved**, no `sorry`: `sameClassF_iff` and `mem_viewReprsF_iff`, both directions;
  `cong_sameClass`, which reduces the forward half to three obligations with `symm`
  discharged; `witnessProgram_encodeDomain` and `encode_corresponds_witness`.
* **Proved, and the reason the statement reads the interpreter's target**:
  `mergeStep_selfCollision`, `not_mergeSaturated_of_entry`, `not_rebuilt_toDatabase`,
  `not_cmdStep_saturate`, with `refutationState_not_mergeSaturated` instantiating them.
* **`sorry`**, one per obligation and the only four in the library: `encode_assert`,
  `encode_trans`, `encode_congr`, `encode_corresponds_complete`. `encode_corresponds` and
  `encode_corresponds_forward` are assembled from them and carry `sorryAx` through them.
-/

namespace Egglog

/-! ### Where `Cong` is the identity

The encoded program asserts no equation but the reflexive one `addTerm` records, so its
`Cong` is the identity on the terms it holds. That is what lets a *computed* reading of
`Database.Out` — which searches the key's congruence class — read the key up to equality. -/

/-- Every equation the database asserts is reflexive. -/
def Database.EqsRefl (d : Database) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

/-- **Where every asserted equation is reflexive, `Cong` is the identity.** By `Cong.le` at
`R := Eq`: the three closure rules are `Eq`'s own, and `congr`'s premise is `Forall₂ Eq`. -/
theorem Cong.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {a b : Term} (h : Cong d a b) :
    a = b := by
  refine Cong.le (R := fun x y => x = y) (fun x y hm => hr (x, y) hm) (fun _ _ h => h.symm)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun f as bs _ _ hl => ?_) h
  rw [show as = bs from (List.forall₂_eq_eq_eq ▸ hl : as = bs)]

/-- The list form. -/
theorem CongList.eq_of_eqsRefl {d : Database} (hr : d.EqsRefl) {as bs : List Term}
    (h : CongList d as bs) : as = bs :=
  List.forall₂_eq_eq_eq ▸ (h.toForall₂.imp fun _ _ hab => Cong.eq_of_eqsRefl hr hab)

/-- `Database.EqsRefl`, over the interpreter's equation list. `toDatabase` keeps `d.eqs` and
the diagonal of `d.terms`, so this is the whole condition. -/
def FDatabase.EqsRefl (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 = p.2

/-- Decided, so that a self-test can report it. -/
def FDatabase.eqsReflB (d : FDatabase) : Bool := d.eqs.all fun p => p.1 == p.2

theorem FDatabase.eqsReflB_iff (d : FDatabase) : d.eqsReflB = true ↔ d.EqsRefl := by
  simp [FDatabase.eqsReflB, FDatabase.EqsRefl, List.all_eq_true]

theorem FDatabase.EqsRefl.toDatabase {d : FDatabase} (h : d.EqsRefl) :
    d.toDatabase.EqsRefl := by
  intro p hp
  rcases FDatabase.mem_toDatabase_eqs.mp hp with ⟨he, -⟩ | ⟨hp', -, -⟩
  · exact he
  · exact h p hp'

/-- The interpreter's term list is closed under subterms. This is the only part of
`Database.WF` the reading below needs, and unlike `WF` it is decidable, so a self-test can
report it at the state it swept. -/
def FDatabase.SubtermClosed (d : FDatabase) : Prop :=
  ∀ t ∈ d.terms, ∀ s ∈ t.subtermList, s ∈ d.terms

/-- Decided. -/
def FDatabase.subtermClosedB (d : FDatabase) : Bool :=
  d.terms.all fun t => t.subtermList.all fun s => d.terms.contains s

theorem FDatabase.subtermClosedB_iff (d : FDatabase) :
    d.subtermClosedB = true ↔ d.SubtermClosed := by
  simp [FDatabase.subtermClosedB, FDatabase.SubtermClosed, List.all_eq_true]

/-- `Database.WF`'s own clause, read back onto the list. -/
theorem FDatabase.SubtermClosed.of_wf {d : FDatabase} (hw : d.toDatabase.WF) :
    d.SubtermClosed := by
  intro t ht s hs
  have ht' : t ∈ d.toDatabase.terms := by rw [FDatabase.toDatabase_terms]; exact ht
  have hs' : s ∈ d.toDatabase.terms := hw.subtermClosed t ht' ((Term.mem_subtermList t).mp hs)
  rwa [FDatabase.toDatabase_terms] at hs'

/-! ### Reading the target, computed

`ViewRepr` as a function from a source term to the list of ids the target gives it: one view
read per subterm, joined on ids. An application's ids are the e-class columns of every view
entry of its head whose key columns are, pointwise, ids of its children.

This is `DiffTest.lean`'s `viewReprs` with the table reading inlined — entries read out of
`terms`, which is what `Database.Out` says, and the key/value split taken from the source
term's own arity rather than from the program's constructor list. -/

/-- Pointwise membership: `ks` picks, per column, one of the ids that column's child was
given. `false` at unequal lengths, which is what makes a view entry of the wrong width no
entry at all. -/
def memAll : List (List Term) → List Term → Bool
  | [], [] => true
  | r :: rs, k :: ks => decide (k ∈ r) && memAll rs ks
  | _, _ => false

/-- The id a view entry gives the source application `f a…`, or `none` where the entry is
not one: the head has to be `f`'s view, the width has to be the key plus the two value
columns, and the key columns have to be ids of the children, which `rs` carries. -/
def viewIdOf (rs : List (List Term)) (f : FnName) (n : Nat) : Term → Option Term
  | .app g cs =>
      if g = viewName f ∧ cs.length = n + 2 ∧ memAll rs (cs.take n) = true then
        (cs.drop n).head?
      else none
  | .lit _ => none

/-- **What a reading found**: the entry term, split into its columns. Both directions of the
link read the table through this. -/
theorem viewIdOf_eq_some {rs : List (List Term)} {f : FnName} {n : Nat} {t e : Term} :
    viewIdOf rs f n t = some e ↔
      ∃ ks pf, t = .app (viewName f) (ks ++ [e, pf]) ∧ ks.length = n ∧
        memAll rs ks = true := by
  match t with
  | .lit l => simp [viewIdOf]
  | .app g cs =>
    simp only [viewIdOf]
    constructor
    · intro h
      split at h
      · rename_i hcond
        obtain ⟨rfl, hlen, hall⟩ := hcond
        have hdlen : (cs.drop n).length = 2 := by rw [List.length_drop, hlen]; omega
        obtain ⟨e', pf, hd⟩ := List.length_eq_two.mp hdlen
        rw [hd] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        refine ⟨cs.take n, pf, ?_, ?_, hall⟩
        · rw [← hd, List.take_append_drop]
        · rw [List.length_take, hlen]; omega
      · exact absurd h (by simp)
    · rintro ⟨ks, pf, hteq, hklen, hall⟩
      simp only [Term.app.injEq] at hteq
      obtain ⟨rfl, rfl⟩ := hteq
      rw [List.take_left' hklen, List.drop_left' hklen,
        if_pos ⟨rfl, by simp [hklen], hall⟩]
      rfl

mutual

/-- The ids the target gives a source term: `ViewRepr d.toDatabase t`, computed.

A literal is its own id where the target holds it and has none where it does not:
`encodeBuild` emits no action for a literal, so a literal never keys a view entry. -/
def viewReprsF (d : FDatabase) : Term → List Term
  | .lit l => if (Term.lit l) ∈ d.terms then [Term.lit l] else []
  | .app f as => d.terms.filterMap (viewIdOf (viewReprsListF d as) f as.length)

/-- `viewReprsF` over an argument list, one id list per column. -/
def viewReprsListF (d : FDatabase) : List Term → List (List Term)
  | [] => []
  | t :: ts => viewReprsF d t :: viewReprsListF d ts

end

/-- `SameClass d.toDatabase`, computed: one id the target gives both terms. -/
def sameClassF (d : FDatabase) (a b : Term) : Bool :=
  (viewReprsF d a).any fun e => decide (e ∈ viewReprsF d b)

/-! ### The link, computed to stated

`SubtermClosed` is what this direction spends: `Database.Out` asks that the key columns be
terms the database holds, and they are subterms of the entry term the reading found. -/

mutual

theorem viewRepr_of_mem_viewReprsF {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (t e : Term), e ∈ viewReprsF d t → ViewRepr d.toDatabase t e
  | .lit l, e, h => by
    simp only [viewReprsF] at h
    split at h
    · rename_i hm
      rw [List.mem_singleton] at h
      subst h
      exact .lit (by rw [FDatabase.toDatabase_terms]; exact hm)
    · exact absurd h (by simp)
  | .app f as, e, h => by
    simp only [viewReprsF, List.mem_filterMap] at h
    obtain ⟨t, ht, hid⟩ := h
    obtain ⟨ks, pf, rfl, hklen, hall⟩ := viewIdOf_eq_some.mp hid
    have hmem : Term.app (viewName f) (ks ++ [e, pf]) ∈ d.toDatabase.terms := by
      rw [FDatabase.toDatabase_terms]; exact ht
    refine .app (viewReprList_of_memAll hsc as ks hall) (Database.out_self hmem ?_)
    intro x hx
    rw [FDatabase.toDatabase_terms]
    exact hsc _ ht x ((Term.mem_subtermList _).mpr
      (Term.IsSubterm.arg (List.mem_append_left _ hx) (.refl x)))

theorem viewReprList_of_memAll {d : FDatabase} (hsc : d.SubtermClosed) :
    ∀ (as ks : List Term), memAll (viewReprsListF d as) ks = true →
      ViewReprList d.toDatabase as ks
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h (by simp [viewReprsListF, memAll])
  | _ :: _, [], h => absurd h (by simp [viewReprsListF, memAll])
  | a :: as, k :: ks, h => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons (viewRepr_of_mem_viewReprsF hsc a k h.1) (viewReprList_of_memAll hsc as ks h.2)

end

/-! ### The link, stated to computed

`EqsRefl` is what this direction spends, and it is spent in exactly one place: `Out`'s
`CongList` premise reads the key up to congruence, and the reading found the entry keyed by
the ids themselves. -/

/-- `ViewReprList` reads one id per column. -/
theorem ViewReprList.length_eq {d : Database} : ∀ {as es : List Term},
    ViewReprList d as es → es.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ hl => by simp [ViewReprList.length_eq hl]

mutual

theorem mem_viewReprsF_of_viewRepr {d : FDatabase} (hr : d.EqsRefl) {t e : Term}
    (h : ViewRepr d.toDatabase t e) : e ∈ viewReprsF d t := by
  match h with
  | .lit hm =>
    rw [FDatabase.toDatabase_terms] at hm
    have hm' : (Term.lit _) ∈ d.terms := hm
    simp only [viewReprsF, if_pos hm', List.mem_singleton]
  | @ViewRepr.app _ f as es e pf hl ho =>
    obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : es = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    rw [FDatabase.toDatabase_terms] at hmem
    simp only [viewReprsF, List.mem_filterMap]
    exact ⟨_, hmem, viewIdOf_eq_some.mpr
      ⟨es, pf, rfl, hl.length_eq, memAll_of_viewReprList hr as es hl⟩⟩

theorem memAll_of_viewReprList {d : FDatabase} (hr : d.EqsRefl) :
    ∀ (as es : List Term), ViewReprList d.toDatabase as es →
      memAll (viewReprsListF d as) es = true
  | _, _, .nil => by simp [viewReprsListF, memAll]
  | a :: as, e :: es, .cons hab hl => by
    simp only [viewReprsListF, memAll, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨mem_viewReprsF_of_viewRepr hr hab, memAll_of_viewReprList hr as es hl⟩

end

/-! ### The two links, joined

`sameClassF_iff` is the theorem the corpus result needs: what `difftest correspond` computes
on the target is what `Encode.lean`'s `SameClass` says about it. -/

/-- **`viewReprsF` decides `ViewRepr`.** -/
theorem mem_viewReprsF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (t e : Term) : e ∈ viewReprsF d t ↔ ViewRepr d.toDatabase t e :=
  ⟨viewRepr_of_mem_viewReprsF hsc t e, mem_viewReprsF_of_viewRepr hr⟩

/-- **`sameClassF` decides `SameClass`.** -/
theorem sameClassF_iff {d : FDatabase} (hsc : d.SubtermClosed) (hr : d.EqsRefl)
    (a b : Term) :
    sameClassF d a b = true ↔ SameClass d.toDatabase a b := by
  simp only [sameClassF, List.any_eq_true, decide_eq_true_eq, SameClass]
  constructor
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mp hea, (mem_viewReprsF_iff hsc hr b e).mp heb⟩
  · rintro ⟨e, hea, heb⟩
    exact ⟨e, (mem_viewReprsF_iff hsc hr a e).mpr hea, (mem_viewReprsF_iff hsc hr b e).mpr heb⟩

/-! ### The proof column against `MergeSaturated`

**`Rebuilt` is unsatisfiable again**, and this time it is `mergeBody` that does it rather
than the rebuild rules. `ENCODING.md`'s finding 1 was that no state `encode` ran to
satisfied `Rebuilt`, and `Cmd.saturate rebuildRuleset` was the repair; the proof column
(`@UF(t) ↦ (p, pf)`) landed after it and reopened the hole one level down.

The mechanism is `Spec/Step.lean`'s own reading of a collision: **every entry collides with
itself** — `MergeSaturated` is "no collision *changes* anything" for exactly that reason —
and the shared `:merge` body writes, for the colliding pair, the edge

```
@UF (ordering-max old0 new0) ↦ (ordering-min old0 new0, @Trans (@Sym hi_pf) lo_pf)
```

At a self-collision `old0 = new0` and `old1 = new1 = pf`, so the body writes the self-loop
`@UF(v) ↦ (v, @Trans (@Sym pf) pf)`: a **new term**, one composition larger than the proof
it started from. `MergeSaturated` therefore forces the whole tower `selfProof^[n] pf` into
the state, so no state with finitely many terms — no state the interpreter can hold, and no
state a run can reach — is `MergeSaturated` once it holds one `@UF` entry.

`identityVals := some 1` is what keeps the *implementation* out of this: it takes the proof
column out of the change test, so a collision that moves only the proof resolves to the
resident row. `Spec/Step.lean`'s `MergeStep` and `MergeSaturated` do not read
`identityVals` — the specification has no notion of a column that does not count — so the
gap is between the two, and closing it is a change to `Spec/`. -/

/-- The proof the shared `:merge` body composes when an entry collides with **itself**:
`@Trans (@Sym pf) pf`, one composition larger than `pf`. -/
def selfProof (pf : Term) : Term := .app transName [.app symName [pf], pf]

/-- `Term.blt` is irreflexive, so every `ordering-gt` on a tie is `false` and every one of
the four bundled choices takes its `else` branch. -/
theorem Term.blt_self (t : Term) : Term.blt t t = false := by
  by_cases h : Term.blt t t = true
  · rw [Term.blt_asymm t t h] at h; exact absurd h (by simp)
  · simpa using h

/-- **Every entry of a table carrying the encoding's `:merge` collides with itself**, and
the body writes a `@UF` self-loop at the entry's value column whose proof is `selfProof` of
the entry's own. -/
theorem mergeStep_selfCollision {d : Database} {f : FnName} {decl : FnDecl}
    (hsig : d.sig f = some decl) (hm : decl.merge = some (.merge mergeBody mergeResult))
    (hsym : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName)
    {as : List Term} {v pf : Term} (hlen : as.length = decl.arity)
    (hargs : ∀ a ∈ as, a ∈ d.terms) (hmem : Term.app f (as ++ [v, pf]) ∈ d.terms) :
    ∃ d', MergeStep d d' ∧ Term.app ufName [v, v, selfProof pf] ∈ d'.terms := by
  simp only [symName, transName] at hsym htr
  have henv : mergeEnv [v, pf] [v, pf] =
      [("old0", v), ("new0", v), ("old1", pf), ("new1", pf)] := rfl
  have hbody : evalActions { d with env := mergeEnv [v, pf] [v, pf] } mergeBody =
      some (({ d with env := mergeEnv [v, pf] [v, pf] }).addTerm
        (.app ufName [v, v, selfProof pf])) := by
    simp [mergeBody, evalActions, evalAction, Expr.eval, Expr.evalList, Prim.ofName,
      Prim.apply, maxE, minE, ifE, gtE, transE, symE, hiPfE, loPfE, henv, Env.lookup,
      Term.blt_self, hsym, htr, selfProof, symName, transName]
  have hres : Expr.evalList ({ d with env := mergeEnv [v, pf] [v, pf] }).sig mergeResult
      (mergeEnv [v, pf] [v, pf]) = some [v, pf] := by
    simp [mergeResult, Expr.eval, Expr.evalList, Prim.ofName, Prim.apply, minE, ifE, gtE,
      loPfE, henv, Env.lookup, Term.blt_self]
  refine ⟨_, MergeStep.collide hsig hm hlen hlen hmem hmem (CongList.refl hargs) hbody hres,
    ?_⟩
  have h1 : Term.app ufName [v, v, selfProof pf] ∈
      (({ d with env := mergeEnv [v, pf] [v, pf] }).addTerm
        (.app ufName [v, v, selfProof pf])).terms := Database.mem_addTerm _ _
  have h2 := (Database.Contained.addTerm (Term.app f (as ++ [v, pf])) _).terms h1
  refine Cong.mono ?_ h2
  exact ⟨subset_rfl⟩

/-- **The tower.** A `MergeSaturated` state holding one `@UF` self-loop holds every
`selfProof` iterate of its proof. -/
theorem mergeSaturated_selfProof_tower {d : Database} (hsat : MergeSaturated d)
    (hsig : d.sig ufName = some ufDecl) (hsym : d.sig.IsCtor symName)
    (htr : d.sig.IsCtor transName) {v pf : Term} (hv : v ∈ d.terms)
    (hmem : Term.app ufName [v, v, pf] ∈ d.terms) :
    ∀ n, Term.app ufName [v, v, selfProof^[n] pf] ∈ d.terms := by
  intro n
  induction n with
  | zero => simpa using hmem
  | succ n ih =>
    obtain ⟨d', hstep, hmem'⟩ :=
      mergeStep_selfCollision (as := [v]) hsig rfl hsym htr rfl
        (by intro a ha; rw [List.mem_singleton] at ha; exact ha ▸ hv) (by simpa using ih)
    rw [Function.iterate_succ_apply']
    exact hsat d' hstep ▸ hmem'

/-- `selfProof` strictly grows a term, so the tower is an injection of `ℕ` into the state. -/
theorem sizeOf_lt_selfProof (pf : Term) : sizeOf pf < sizeOf (selfProof pf) := by
  simp only [selfProof, Term.app.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
  omega

/-- The tower's proofs grow without bound: `selfProof^[n] pf` is at least `n` big. -/
theorem le_sizeOf_selfProof_iterate (pf : Term) : ∀ n, n ≤ sizeOf (selfProof^[n] pf)
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact Nat.lt_of_le_of_lt (le_sizeOf_selfProof_iterate pf n) (sizeOf_lt_selfProof _)

/-- **No state whose terms fit in a list is `MergeSaturated` once it holds a `@UF` entry.**

The hypothesis is "listable" rather than `Set.Finite` because that is the form the states
this is about come in: `FDatabase.toDatabase`'s terms are exactly a list, and a state a run
reaches is built from `Database.empty` by finitely many steps each adding finitely many
terms. `not_mergeSaturated_toDatabase` is the reading at an interpreter state. -/
theorem not_mergeSaturated_of_ufEntry {d : Database} {l : List Term}
    (hfin : ∀ t ∈ d.terms, t ∈ l) (hsig : d.sig ufName = some ufDecl)
    (hsym : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName) {v pf : Term}
    (hv : v ∈ d.terms) (hmem : Term.app ufName [v, v, pf] ∈ d.terms) :
    ¬ MergeSaturated d := by
  intro hsat
  set n := sizeOf l with hn
  have hin := hfin _ (mergeSaturated_selfProof_tower hsat hsig hsym htr hv hmem n)
  have hlt : sizeOf (Term.app ufName [v, v, selfProof^[n] pf]) < sizeOf l :=
    List.sizeOf_lt_of_mem hin
  have hsub : sizeOf (selfProof^[n] pf) < sizeOf (Term.app ufName [v, v, selfProof^[n] pf]) := by
    simp only [Term.app.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega
  have := le_sizeOf_selfProof_iterate pf n
  omega

/-- **One entry of one view is enough.** The `:merge` body is shared by `@UF` and every
view, so a state holding a single view entry — which is a state that has built a single
term — already fails `MergeSaturated`. -/
theorem not_mergeSaturated_of_entry {d : Database} {l : List Term}
    (hfin : ∀ t ∈ d.terms, t ∈ l) (hsub : ∀ t ∈ d.terms, t.subterms ⊆ d.terms)
    (hufsig : d.sig ufName = some ufDecl)
    (hsym : d.sig.IsCtor symName) (htr : d.sig.IsCtor transName)
    {f : FnName} {decl : FnDecl} (hsigf : d.sig f = some decl)
    (hm : decl.merge = some (.merge mergeBody mergeResult))
    {as : List Term} {v pf : Term} (hlen : as.length = decl.arity)
    (hmem : Term.app f (as ++ [v, pf]) ∈ d.terms) : ¬ MergeSaturated d := by
  intro hsat
  have hargs : ∀ a ∈ as, a ∈ d.terms := fun a ha =>
    hsub _ hmem (Term.IsSubterm.arg (List.mem_append_left _ ha) (.refl a))
  have hv : v ∈ d.terms := hsub _ hmem (Term.IsSubterm.arg (by simp) (.refl v))
  obtain ⟨d', hstep, hmem'⟩ := mergeStep_selfCollision hsigf hm hsym htr hlen hargs hmem
  rw [hsat d' hstep] at hmem'
  exact not_mergeSaturated_of_ufEntry hfin hufsig hsym htr hv hmem' hsat

/-- The same at an interpreter state, where the list is `terms` itself. **This is the state
`difftest correspond` computes**: the target of every case in the corpus holds `@UF` entries
— 180 of them — so none of them is a state `Cmd.saturate` can step to. -/
theorem not_mergeSaturated_toDatabase {d : FDatabase}
    (hsig : d.sig ufName = some ufDecl) (hsym : d.sig.IsCtor symName)
    (htr : d.sig.IsCtor transName) {v pf : Term} (hv : v ∈ d.terms)
    (hmem : Term.app ufName [v, v, pf] ∈ d.terms) : ¬ MergeSaturated d.toDatabase := by
  refine not_mergeSaturated_of_ufEntry (l := d.terms) (v := v) (pf := pf) ?_ hsig hsym htr ?_ ?_
  · intro t ht; rwa [FDatabase.toDatabase_terms] at ht
  · rw [FDatabase.toDatabase_terms]; exact hv
  · rw [FDatabase.toDatabase_terms]; exact hmem

/-- **And so `Rebuilt` is unsatisfiable there**, which is the hypothesis `ENCODING.md`'s
finding 1 was about: `Rebuilt`'s second conjunct *is* `MergeSaturated`. -/
theorem not_rebuilt_toDatabase {P : Program} {d : FDatabase}
    (hsig : d.sig ufName = some ufDecl) (hsym : d.sig.IsCtor symName)
    (htr : d.sig.IsCtor transName) {v pf : Term} (hv : v ∈ d.terms)
    (hmem : Term.app ufName [v, v, pf] ∈ d.terms) : ¬ Rebuilt P d.toDatabase :=
  fun h => not_mergeSaturated_toDatabase hsig hsym htr hv hmem h.2

/-- **And no `Cmd.saturate` steps from such a state**, whatever its ruleset: `SaturateReach`
ends `RunSaturated`, whose second conjunct is `MergeSaturated`, and `MergeStep` only ever
adds — so the state it ends at holds the `@UF` entry this one did. -/
theorem not_cmdStep_saturate {R : RulesetName} {d : FDatabase} {d' : Database}
    (hsig : d'.sig ufName = some ufDecl) (hsym : d'.sig.IsCtor symName)
    (htr : d'.sig.IsCtor transName) {l : List Term} (hfin : ∀ t ∈ d'.terms, t ∈ l)
    {v pf : Term} (hv : v ∈ d.terms) (hmem : Term.app ufName [v, v, pf] ∈ d.terms) :
    ¬ CmdStep d.toDatabase (.saturate R) d' := by
  intro h
  have hsat : SaturateReach R d.toDatabase d' := cmdStep_saturate_iff.mp h
  have hcont : d.toDatabase.Contained d' := RunReach.contained hsat.1
  refine not_mergeSaturated_of_ufEntry hfin hsig hsym htr (v := v) (pf := pf) ?_ ?_ hsat.2.2
  · exact hcont.terms (by rw [FDatabase.toDatabase_terms]; exact hv)
  · exact hcont.terms (by rw [FDatabase.toDatabase_terms]; exact hmem)

/-! #### The refutation, instantiated

A refutation whose hypotheses nothing satisfies is worth as little as a theorem whose
hypotheses nothing satisfies, so here is a state that satisfies them: the encoding's own
`@UF` and proof declarations, one `@UF` self-loop, and nothing else. No run is needed to
build it and none is run to check it. -/

/-- A term to hang the state on. -/
private def refA : Term := .app "A" []

/-- The state: `@UF`, `@Sym` and `@Trans` declared as the prelude declares them, and the
single entry `@UF(A) ↦ (A, @Fiat)`. -/
def refutationState : FDatabase where
  sig := fun n =>
    if n = ufName then some ufDecl
    else if n = symName then some (proofDecl 1)
    else if n = transName then some (proofDecl 2)
    else none
  terms := [refA, .app fiatName [], .app ufName [refA, refA, .app fiatName []]]
  rows := []
  eqs := []
  env := []
  rules := []

/-- **And it is not `MergeSaturated`**, so `not_mergeSaturated_toDatabase` refutes something
that exists. The state is the shape every encoded run reaches: `encodePrelude` emits
`.decl ufName ufDecl` and the proof declarations, and the shared `:merge` writes a `@UF`
edge at the first collision of the first view entry. -/
theorem refutationState_not_mergeSaturated :
    ¬ MergeSaturated refutationState.toDatabase := by
  refine not_mergeSaturated_toDatabase (v := refA) (pf := .app fiatName []) rfl
    ⟨proofDecl 1, by simp [refutationState, ufName, symName], rfl⟩
    ⟨proofDecl 2, by simp [refutationState, ufName, symName, transName], rfl⟩
    (by simp [refutationState, refA]) (by simp [refutationState, refA])

/-! ### The statement

**The target is the interpreter's, not the specification's.** The natural statement carries
`ProgramStep Database.empty (encode P) tgt`, and that hypothesis is unsatisfiable for every
`P` that builds a term: `encode` emits `Cmd.saturate rebuildRuleset` after every writing
command, `SaturateReach` ends at a `RunSaturated` state, `RunSaturated`'s second conjunct is
`MergeSaturated`, and `not_mergeSaturated_of_entry` above refutes that at any state holding
one view entry. Stating it anyway would be stating a theorem that says nothing — which is
the failure `ENCODING.md` records — so the hypothesis is `execM (encode P) = some tgt`
instead: the run `difftest` performs, and the state the corpus result is about.

The two are not the same claim. `execM` under-fires relative to the specification
(`Proofs/Merge.lean`, `execM_contained`: the enumerator is stricter than `ValidEnv`, and
`Impl/`'s merge phase reads `identityVals` where `MergeStep` does not), so this is a
statement about the reference implementation's target. Turning it back into a statement
about `Spec/` needs `MergeSaturated` to stop counting the proof column, which is a change to
`Spec/Step.lean`.

The source side keeps `ProgramStep`: a source program is constructor-only, `exec_programStep`
is an equality there, and the witness discharges the hypothesis through it. -/

/-- `EncodeDomain.ctorsOnly`, in the form `exec_programStep` asks for. -/
theorem Program.EncodeDomain.ctorDecls {P : Program} (h : P.EncodeDomain) : P.CtorDecls := by
  intro c hc
  match c with
  | .decl f dc => exact h.ctorsOnly _ hc f dc rfl
  | .action _ => trivial
  | .rule _ => trivial
  | .run _ => trivial
  | .saturate _ => trivial

/-! #### The forward half, by cases on `Cong`

`Cong` has four constructors and no `refl`, so the forward half is four obligations.
`symm` is free — `SameClass` is symmetric by construction — and the other three are stated
below, unproved. `cong_sameClass` is the reduction itself and is proved: it is `Cong.le` at
`R := SameClass tgt`. -/

/-- The three obligations `Cong.le` leaves once `symm` is discharged. -/
structure CongObligations (src tgt : Database) : Prop where
  /-- Every equation the source *asserts* — a reflexive one per term built, and one per
  `union` — the target's views agree on. One clause per writer. -/
  assert : ∀ a b, (a, b) ∈ src.eqs → SameClass tgt a b
  /-- The target's e-classes compose. This is `Database.Out`'s functionality at the view:
  two view entries at one key have merged, so their e-class columns are one class. -/
  trans : ∀ a b c, SameClass tgt a b → SameClass tgt b c → SameClass tgt a c
  /-- Congruence: children in one class put their applications in one class. This is what
  the rebuild is for, and it is the whole difficulty. -/
  congr : ∀ f as bs, Cong src (.app f as) (.app f as) → Cong src (.app f bs) (.app f bs) →
    List.Forall₂ (SameClass tgt) as bs → SameClass tgt (.app f as) (.app f bs)

/-- **The forward half is exactly those three.** `Cong` is the least relation closed under
its four rules (`Cong.le`), and `SameClass` is closed under `symm` outright. -/
theorem cong_sameClass {src tgt : Database} (h : CongObligations src tgt) {a b : Term}
    (hc : Cong src a b) : SameClass tgt a b :=
  Cong.le h.assert (fun _ _ hab => hab.symm) h.trans h.congr hc

/-- **Obligation `assert`, at the encoding.** Two writers to cover. `Database.addTerm`
writes a reflexive equation per subterm and `encodeBuild` writes `@fView(es) ↦ (f es, @Fiat)`
for the application it encodes, which is the id `ViewRepr` reads; `evalAction`'s `union`
writes a `@UF` edge, whose two endpoints share a view id only once the rebuild has re-keyed
them, so this clause rests on the rebuild exactly as `congr` does. **Not proved.** -/
theorem encode_assert {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b : Term) (h : (a, b) ∈ src.eqs) : SameClass tgt.toDatabase a b := by
  sorry

/-- **Obligation `trans`, at the encoding.** Needs the view's functional dependency: if `b`
reads to `e₁` and to `e₂` then the two entries collided on a congruent key and the `:merge`
unioned them, so `e₁` and `e₂` are one class — and, at a rebuilt state, one id. Not free
from the flat reading, which is why the union-find walk was there. **Not proved.** -/
theorem encode_trans {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (a b c : Term) (hab : SameClass tgt.toDatabase a b) (hbc : SameClass tgt.toDatabase b c) :
    SameClass tgt.toDatabase a c := by
  sorry

/-- **Obligation `congr`, at the encoding.** The rebuild rules re-key a view entry to its
children's `@UF` leaders, so two applications whose children share ids key the *same* view
entry and the `:merge` unions their e-class columns. This is the whole difficulty and it is
what a rebuilt state buys. **Not proved.** -/
theorem encode_congr {P : Program} {src : Database} {tgt : FDatabase} (hdom : P.EncodeDomain)
    (hsrc : ProgramStep Database.empty P src) (htgt : execM (encode P) = some tgt)
    (f : FnName) (as bs : List Term) (ha : Cong src (.app f as) (.app f as))
    (hb : Cong src (.app f bs) (.app f bs))
    (hl : List.Forall₂ (SameClass tgt.toDatabase) as bs) :
    SameClass tgt.toDatabase (.app f as) (.app f bs) := by
  sorry

/-- **No equality is lost**: assembled from the three obligations, with `symm` free. -/
theorem encode_corresponds_forward {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (h : Cong src a b) :
    SameClass tgt.toDatabase a b :=
  cong_sameClass ⟨encode_assert hdom hsrc htgt, encode_trans hdom hsrc htgt,
    encode_congr hdom hsrc htgt⟩ h

/-- **No equality is invented.** The target-side induction has no `Cong.le` to lean on:
`SameClass` is an existential over view entries, so this half is an invariant over the
commands that write them — every view entry the encoding records is an equality the source
derives. **Not proved.** -/
theorem encode_corresponds_complete {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) {a b : Term} (h : SameClass tgt.toDatabase a b) :
    Cong src a b := by
  sorry

/-- **The correspondence.** `difftest correspond 64` runs exactly this claim over the 70
in-domain cases and the seventeen probes, through `sameClassF` and `closureF`, and reports
70 agreeing, 0 LOST, 0 INVENTED — and `link-diff` 0, which is what says the swept relation
is this one.

`EncodeDomain` is still needed: outside it `encode` is not defined for the program at all —
a `:merge` declaration has no table triple to emit, and a source name in the generated
namespace collides with one. `Rebuilt` is *not* a hypothesis: it is a postcondition
(`cmdStep_rebuilt`), and one nothing satisfies (`not_rebuilt_toDatabase`), so what the two
unproved halves have to lean on is the interpreter's own saturation instead. -/
theorem encode_corresponds {P : Program} {src : Database} {tgt : FDatabase}
    (hdom : P.EncodeDomain) (hsrc : ProgramStep Database.empty P src)
    (htgt : execM (encode P) = some tgt) (a b : Term) :
    Cong src a b ↔ SameClass tgt.toDatabase a b :=
  ⟨encode_corresponds_forward hdom hsrc htgt, encode_corresponds_complete hdom hsrc htgt⟩

/-! ### The witness

`ENCODING.md`: two of thirteen previous M11 statements were vacuous and nobody noticed,
because they carried `sorry`. So before the `sorry`s above are allowed to stand, here is a
program whose three hypotheses hold **together**, and a pair of term pairs at which both
sides of the conclusion are non-trivial — one both say yes to, one both say no to. An `iff`
between two relations that are always false is true and worthless; `agree-true` is the same
measurement over the whole corpus, and it is 778.

The two runs cannot be `#guard`s: an encoded action is followed by a saturating rebuild, and
running one during elaboration took `lake build difftest` past fifteen minutes. So the
witness is this theorem — compiled, no `sorry` — whose hypotheses are all *decidable* facts
about one concrete program, and `difftest correspond-selftest` evaluates them and reports.
-/

/-- The witness program: two applications made congruent by a `union` of their leaves, with
its constructors declared. `DiffTest.lean`'s `unionCase`, written out because that file is
downstream of this one. It is the smallest program that derives an equality between distinct
terms — two, in fact: `One = Two` and the two `Add`s above them. -/
def witnessProgram : Program :=
  [.decl "Add" { arity := 2, outArity := 1, merge := none },
   .decl "One" { arity := 0, outArity := 1, merge := none },
   .decl "Two" { arity := 0, outArity := 1, merge := none },
   .action (.expr (.app "Add" [.app "One" [], .app "Two" []])),
   .action (.expr (.app "Add" [.app "Two" [], .app "One" []])),
   .action (.union (.app "One" []) (.app "Two" []))]

/-- `(One)`. -/
def witnessOne : Term := .app "One" []

/-- `(Two)`, which the program unions with `witnessOne`. -/
def witnessTwo : Term := .app "Two" []

/-- `(Add One Two)`, which is congruent to `(Add Two One)` and *not* to `(One)`. -/
def witnessAdd : Term := .app "Add" [witnessOne, witnessTwo]

/-- The witness is in `encode`'s domain, at compile time: `Program.encodeDomainB` and its
equivalence live downstream in `DiffTest.lean`, so the six clauses are discharged here
directly. -/
theorem witnessProgram_encodeDomain : witnessProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc f dc heq
    subst heq
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with h | h | h | h | h | h | h <;> simp_all
  noSet := by
    intro c hc
    simp only [witnessProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | h <;> trivial
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  noAtVar := by decide +kernel
  noAtRuleset := by decide +kernel

/-- **The hypotheses of `encode_corresponds` are simultaneously satisfiable, and both sides
of its conclusion are inhabited and refutable at the witness.**

Everything it asks of the two runs is decidable and is checked at run time by
`difftest correspond-selftest`; `hdom` is discharged here, at compile time. -/
theorem encode_corresponds_witness {d e : FDatabase} {a b c₁ c₂ : Term}
    (hd : exec witnessProgram = some d) (he : execM (encode witnessProgram) = some e)
    (hsc : e.SubtermClosed) (hr : e.EqsRefl)
    (hyes₁ : (a, b) ∈ d.closureF) (hyes₂ : sameClassF e a b = true)
    (hno₁ : (c₁, c₂) ∉ d.closureF) (hno₂ : sameClassF e c₁ c₂ = false) :
    ∃ src, witnessProgram.EncodeDomain ∧ ProgramStep Database.empty witnessProgram src ∧
      execM (encode witnessProgram) = some e ∧
      (Cong src a b ∧ SameClass e.toDatabase a b) ∧
      (¬ Cong src c₁ c₂ ∧ ¬ SameClass e.toDatabase c₁ c₂) := by
  refine ⟨d.toDatabase, witnessProgram_encodeDomain, ?_, he, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (exec_programStep witnessProgram_encodeDomain.ctorDecls
      (Or.inr (by rw [hd]; simp))).mp (by rw [hd]; rfl)
  · exact FDatabase.mem_closureF_iff.mp hyes₁
  · exact (sameClassF_iff hsc hr a b).mp hyes₂
  · exact fun h => hno₁ (FDatabase.mem_closureF_iff.mpr h)
  · exact fun h => by simp [(sameClassF_iff hsc hr c₁ c₂).mpr h] at hno₂

end Egglog
