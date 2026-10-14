import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.Merge

/-! Union-free execution and the resulting diagonal built-in congruence. -/

namespace Egglog

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

/-- `FDatabase.SubtermClosed`, decided: the only part of `Database.WF` the reading below
needs, and a self-test can report it at the state it swept. -/
def FDatabase.subtermClosedB (d : FDatabase) : Bool :=
  d.terms.all fun t => t.subtermList.all fun s => d.terms.contains s

theorem FDatabase.subtermClosedB_iff (d : FDatabase) :
    d.subtermClosedB = true ↔ d.SubtermClosed := by
  simp [FDatabase.subtermClosedB, FDatabase.SubtermClosed, Term.ListClosed, List.all_eq_true]

/-- `Database.WF`'s own clause, read back onto the list. -/
theorem FDatabase.SubtermClosed.of_wf {d : FDatabase} (hw : d.toDatabase.WF) :
    d.SubtermClosed := by
  intro t ht s hs
  have ht' : t ∈ d.toDatabase.terms := by rw [FDatabase.toDatabase_terms]; exact ht
  have hs' : s ∈ d.toDatabase.terms := hw.subtermClosed t ht' ((Term.mem_subtermList t).mp hs)
  rwa [FDatabase.toDatabase_terms] at hs'

/-- **A state whose equations, merge bodies and rule heads are all union-free.**
`Database.NoUnions`' three fields, read off an `FDatabase`: the three phases read one
each. -/
structure FDatabase.NoUnions (d : FDatabase) : Prop where
  /-- The state asserts nothing, which is `Database.Diag` in its strongest form. -/
  eqs : d.eqs = []
  /-- No `:merge` body asserts anything, which is what a merge phase runs. -/
  sig : Signature.UnionFree d.sig
  /-- No rule head asserts anything, which is what a round runs. -/
  rules : ∀ r ∈ d.rules, Actions.UnionFree r.actions

/-- `addRow` is an `addTerm` and an index write. -/
theorem FDatabase.addRow_eqs (f : FnName) (as vs : List Term) (d : FDatabase) :
    (d.addRow f as vs).eqs = d.eqs := rfl

/-- A round's accumulator takes its signature and rules from the left and its equations from
both. -/
theorem FDatabase.NoUnions.union {d₁ d₂ : FDatabase} (h₁ : d₁.NoUnions) (h₂ : d₂.eqs = []) :
    (d₁.union d₂).NoUnions where
  eqs := by simp [FDatabase.union, h₁.eqs, h₂]
  sig := h₁.sig
  rules := h₁.rules

/-- **One action.** `Action.union` is the only case that reaches `addEq`, and `Action.UnionFree`
is exactly its exclusion. -/
theorem execAction_noUnions {d d' : FDatabase} {a : Action} (hu : a.UnionFree)
    (hn : d.NoUnions) (h : execAction d a = some d') : d'.NoUnions := by
  cases a with
  | expr e =>
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨hn.eqs, hn.sig, hn.rules⟩
  | union e₁ e₂ => exact absurd hu (by simp [Action.UnionFree])

@[inherit_doc execAction_noUnions]
theorem execActions_noUnions : ∀ {as : List Action} {d d' : FDatabase},
    Actions.UnionFree as → d.NoUnions → execActions d as = some d' → d'.NoUnions
  | [], _, _, _, hn, h => by rw [execActions, Option.some.injEq] at h; exact h ▸ hn
  | a :: as, _, _, hu, hn, h => by
      rw [execActions] at h
      obtain ⟨e, he, hrest⟩ := Option.bind_eq_some_iff.mp h
      exact execActions_noUnions hu.2 (execAction_noUnions hu.1 hn he) hrest

/-- A rule head runs its block under the match and then restores the environment and the rule
set. -/
theorem execLocalActions_noUnions {d d' : FDatabase} {as : List Action} {σ : Env}
    (hu : Actions.UnionFree as) (hn : d.NoUnions) (h : execLocalActions d as σ = some d') :
    d'.NoUnions := by
  rw [execLocalActions] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have := execActions_noUnions hu (show ({d with env := σ ++ d.env} : FDatabase).NoUnions from
    ⟨hn.eqs, hn.sig, hn.rules⟩) he
  exact ⟨this.eqs, this.sig, hn.rules⟩

/-- One firing, unioned into the accumulator. -/
theorem fireInto_noUnions {d acc : FDatabase} {r : Rule} {σ : Env}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) (ha : acc.NoUnions) :
    (fireInto d r acc σ).NoUnions := by
  rw [fireInto]
  cases hf : execLocalActions d r.actions σ with
  | none => exact ha
  | some d' => exact ha.union (execLocalActions_noUnions hu hn hf).eqs

@[inherit_doc fireInto_noUnions]
theorem fireRule_noUnions {d acc : FDatabase} {r : Rule}
    (hu : Actions.UnionFree r.actions) (hn : d.NoUnions) (ha : acc.NoUnions) :
    (fireRule d acc r).NoUnions := by
  rw [fireRule]
  induction matchQuery d r.query generalizing acc with
  | nil => exact ha
  | cons σ σs ih => exact ih (fireInto_noUnions hu hn ha)

/-- The round's fold, with the accumulator generalized; the pre-state the matches are read off
is fixed. -/
theorem foldl_fireRule_noUnions {d : FDatabase} (hn : d.NoUnions) :
    ∀ (rs : List Rule), (∀ r ∈ rs, Actions.UnionFree r.actions) →
      ∀ {acc : FDatabase}, acc.NoUnions → (rs.foldl (fireRule d) acc).NoUnions
  | [], _, _, ha => ha
  | r :: rs, hu, _, ha =>
      foldl_fireRule_noUnions hn rs (fun r' hr' => hu r' (List.mem_cons_of_mem _ hr'))
        (fireRule_noUnions (hu r List.mem_cons_self) hn ha)

/-- **One round.** Every rule of the ruleset is one the state holds, so `rules` covers them. -/
theorem execRunRules_noUnions {R : RulesetName} {d : FDatabase} (hn : d.NoUnions) :
    (execRunRules R d).NoUnions :=
  foldl_fireRule_noUnions hn _ (fun r hr => hn.rules r (List.mem_of_mem_filter hr)) hn

/-- **One `:merge` firing.** The body is read from the signature, which is where `sig` is
spent; the surviving row is an `addTerm`, and `env`/`rules` come back from the pre-state. -/
theorem mergeOneOriented_noUnions {cl : Finset (Term × Term)} {d d' : FDatabase} {r₁ r₂ : Row}
    (hn : d.NoUnions) (h : d.mergeOneOriented cl r₁ r₂ = some d') : d'.NoUnions := by
  rw [FDatabase.mergeOneOriented] at h
  split at h
  · rename_i body res hm
    obtain ⟨dc, hdc, hmm⟩ := Option.bind_eq_some_iff.mp hm
    have hbody : Actions.UnionFree body := hn.sig _ _ hdc _ hmm
    split at h
    · split at h
      · rw [Option.some.injEq] at h
        exact ⟨by rw [← h]; exact hn.eqs, by rw [← h]; exact hn.sig, by rw [← h]; exact hn.rules⟩
      · obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h
        have hE : e.NoUnions :=
          execActions_noUnions hbody
            (show ({d with env := mergeEnv r₂.out r₁.out} : FDatabase).NoUnions from
              ⟨hn.eqs, hn.sig, hn.rules⟩) he
        exact ⟨by rw [show _ = (e.addTerm (.app r₂.fn (r₂.args ++ vs))).eqs from rfl,
                  FDatabase.addTerm_eqs]; exact hE.eqs,
          hE.sig, hn.rules⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

@[inherit_doc mergeOneOriented_noUnions]
theorem mergeOneWith_noUnions {cl : Finset (Term × Term)} {d d' : FDatabase} {r₁ r₂ : Row}
    (hn : d.NoUnions) (h : FDatabase.mergeOneWith cl d r₁ r₂ = some d') : d'.NoUnions := by
  rw [FDatabase.mergeOneWith] at h
  split at h
  · exact mergeOneOriented_noUnions hn h
  · exact mergeOneOriented_noUnions hn h

/-- A rebuild moves rows only. -/
theorem rebuild_noUnions {cl : Finset (Term × Term)} {d : FDatabase} (hn : d.NoUnions) :
    (FDatabase.rebuild cl d).NoUnions := ⟨hn.eqs, hn.sig, hn.rules⟩

/-- A merge pass's inner fold: every firing runs at the accumulator. -/
theorem foldl_mergeInner_noUnions {cl : Finset (Term × Term)} {r₁ : Row} :
    ∀ (rows : List Row) {acc : FDatabase}, acc.NoUnions →
      (rows.foldl (fun acc' r₂ => if r₁ == r₂ then acc' else
        match FDatabase.mergeOneWith cl acc' r₁ r₂ with
        | some acc'' => acc''
        | none => acc') acc).NoUnions
  | [], _, ha => ha
  | _ :: rows, acc, ha => by
      rename_i r₂
      refine foldl_mergeInner_noUnions rows ?_
      by_cases hb : r₁ == r₂
      · simpa [hb] using ha
      · simp only [hb, Bool.false_eq_true, if_false]
        cases hm : FDatabase.mergeOneWith cl acc r₁ r₂ with
        | none => exact ha
        | some acc'' => exact mergeOneWith_noUnions ha hm

@[inherit_doc foldl_mergeInner_noUnions]
theorem foldl_mergeOuter_noUnions {cl : Finset (Term × Term)} {e : FDatabase} :
    ∀ (rows : List Row) {acc : FDatabase}, acc.NoUnions →
      (rows.foldl (fun acc r₁ =>
        e.rows.foldl (fun acc' r₂ => if r₁ == r₂ then acc' else
          match FDatabase.mergeOneWith cl acc' r₁ r₂ with
          | some acc'' => acc''
          | none => acc') acc) acc).NoUnions
  | [], _, ha => ha
  | _ :: rows, _, ha =>
      foldl_mergeOuter_noUnions rows (foldl_mergeInner_noUnions e.rows ha)

/-- **One merge pass.** -/
theorem mergeRound_noUnions {d : FDatabase} (hn : d.NoUnions) : d.mergeRound.NoUnions := by
  rw [FDatabase.mergeRound]
  split
  · exact hn
  · exact foldl_mergeOuter_noUnions _ (rebuild_noUnions hn)

/-- **A merge phase**, however many passes it takes. -/
theorem mergeSaturateF_noUnions : ∀ (n : Nat) {d d' : FDatabase}, d.NoUnions →
    FDatabase.mergeSaturateF n d = some d' → d'.NoUnions
  | 0, _, _, hn, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact absurd h (by simp)
  | n + 1, _, _, hn, h => by
      rw [FDatabase.mergeSaturateF] at h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact mergeSaturateF_noUnions n (mergeRound_noUnions hn) h

/-- **One round of a ruleset, with its merge phase.** -/
theorem runRoundM_noUnions {R : RulesetName} {d d' : FDatabase} (hn : d.NoUnions)
    (h : d.runRoundM R = some d') : d'.NoUnions :=
  mergeSaturateF_noUnions _ (execRunRules_noUnions hn) h

/-- **Rounds to the interpreter's fixpoint.** -/
theorem runSaturateM_noUnions {R : RulesetName} : ∀ (n : Nat) {d d' : FDatabase}, d.NoUnions →
    FDatabase.runSaturateM R n d = some d' → d'.NoUnions
  | 0, _, _, hn, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact absurd h (by simp)
  | n + 1, _, _, hn, h => by
      rw [FDatabase.runSaturateM] at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rw [Option.some.injEq] at h; exact h ▸ hn
      · exact runSaturateM_noUnions n (runRoundM_noUnions hn he) h

/-- **One command.** `.decl` is the only writer of `sig` and `.rule` the only writer of
`rules`, which is why `Cmd.UnionFree` is stated at those two and at an action. -/
theorem execCmdM_noUnions {d d' : FDatabase} {c : Cmd} (hu : c.UnionFree) (hn : d.NoUnions)
    (h : d.execCmdM c = some d') : d'.NoUnions := by
  cases c with
  | action a =>
      rw [FDatabase.execCmdM] at h
      obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
      exact mergeSaturateF_noUnions _ (execAction_noUnions hu hn (he)) h
  | rule r =>
      rw [FDatabase.execCmdM, Option.some.injEq] at h
      refine ⟨by rw [← h]; exact hn.eqs, by rw [← h]; exact hn.sig, ?_⟩
      intro r' hr'
      rcases List.mem_cons.mp
        (show r' ∈ r :: d.rules by rw [← h] at hr'; exact hr')
        with rfl | h'
      · simpa using hu
      · exact hn.rules r' h'
  | run R => exact runRoundM_noUnions hn h
  | saturate R => exact runSaturateM_noUnions _ hn h
  | decl f dc =>
      rw [FDatabase.execCmdM, Option.some.injEq] at h
      refine ⟨by rw [← h]; exact hn.eqs, ?_, by rw [← h]; exact hn.rules⟩
      intro g dc' hg
      rw [← h] at hg
      have hg' : Function.update d.sig f (some dc) g = some dc' := hg
      by_cases hgf : g = f
      · subst hgf
        rw [Function.update_self, Option.some.injEq] at hg'
        exact hg' ▸ hu
      · rw [Function.update_of_ne hgf] at hg'
        exact hn.sig g dc' hg'

@[inherit_doc execCmdM_noUnions]
theorem execProgramM_noUnions : ∀ {p : Program} {d d' : FDatabase}, Program.UnionFree p →
    d.NoUnions → d.execProgramM p = some d' → d'.NoUnions
  | [], _, _, _, hn, h => by rw [FDatabase.execProgramM, Option.some.injEq] at h; exact h ▸ hn
  | c :: cs, _, _, hu, hn, h => by
      rw [FDatabase.execProgramM] at h
      obtain ⟨e, he, hrest⟩ := Option.bind_eq_some_iff.mp h
      exact execProgramM_noUnions hu.2 (execCmdM_noUnions hu.1 hn he) hrest

/-- The initial state asserts nothing, declares nothing and holds no rule. -/
theorem empty_noUnions : FDatabase.empty.NoUnions :=
  ⟨rfl, by intro f dc h; exact absurd h (by simp [FDatabase.empty]),
    by intro r hr; exact absurd hr (by simp [FDatabase.empty])⟩

/-- **A union-free program reaches no state that asserts anything.** -/
theorem execM_noUnions {p : Program} (hu : Program.UnionFree p) {d : FDatabase}
    (h : execM p = some d) : d.NoUnions :=
  execProgramM_noUnions hu empty_noUnions h

/-- **Congruent key tuples are equal, against a diagonal closure.** Stated at the closure and
not at a state, because `FDatabase.mergeRound` compares against the closure of its
**pre-pass** state while the accumulator has moved on. -/
theorem eq_of_congrKeys {cl : Finset (Term × Term)} (hcl : ∀ p ∈ cl, p.1 = p.2) :
    ∀ {as bs : List Term}, FDatabase.congrKeys cl as bs = true → as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs h
    have hlen := (Bool.and_eq_true_iff.mp h).1
    have h0 : (0 : Nat) = bs.length := by simpa using hlen
    exact (List.eq_nil_of_length_eq_zero h0.symm).symm
  | cons a as ih =>
    intro bs h
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp h
    match bs with
    | [] => simp at hlen
    | b :: bs' =>
      have hlen' : (as.length == bs'.length) = true := by simpa using hlen
      have hall' := List.all_eq_true.mp hall
      have hab : (a, b) ∈ cl := by
        have hq := hall' (a, b) (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
        simpa using hq
      have hrest : FDatabase.congrKeys cl as bs' = true :=
        Bool.and_eq_true_iff.mpr ⟨hlen', List.all_eq_true.mpr (fun q hq =>
          hall' q (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hq))⟩
      have heq : a = b := hcl (a, b) hab
      rw [heq, ih hrest]

theorem FDatabase.SubtermClosed.addRow {d : FDatabase} (h : d.SubtermClosed) (g : FnName)
    (as vs : List Term) : (FDatabase.addRow g as vs d).SubtermClosed :=
  h.addTerm (.app g (as ++ vs))

/-- A column of a term the list holds is a term the list holds. -/
theorem FDatabase.mem_terms_of_column {d : FDatabase} (hsc : d.SubtermClosed) {g : FnName}
    {cols : List Term} (hmem : Term.app g cols ∈ d.terms) {c : Term} (hc : c ∈ cols) :
    c ∈ d.terms :=
  hsc _ hmem c ((Term.mem_subtermList _).mpr
    (Term.arg_subterms hc (Term.self_mem_subterms c)))

/-- An indexed function row has a recorded entry at exactly its keys when
built-in equality is diagonal. -/
theorem mem_terms_of_indexOk {d : FDatabase} (hr : d.EqsRefl) (hidx : d.IndexOk)
    {r : Row} (hm : r ∈ d.rows) (hmg : d.sig.mergeOf r.fn ≠ none) :
    Term.app r.fn (r.args ++ r.out) ∈ d.terms := by
  obtain ⟨bs, hcl, hmem⟩ := hidx.entry r hm hmg
  obtain rfl : r.args = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
  rw [FDatabase.toDatabase_terms] at hmem
  exact hmem

/-- A state that asserts nothing asserts nothing non-reflexive. -/
theorem FDatabase.NoUnions.eqsRefl {d : FDatabase} (h : d.NoUnions) : d.EqsRefl := by
  intro p hp
  rw [h.eqs] at hp
  exact absurd hp (by simp)

/-- **The closure of a state that asserts nothing is the diagonal.** -/
theorem diag_closureF {d : FDatabase} (hr : d.EqsRefl) {p : Term × Term}
    (hp : p ∈ d.closureF) : p.1 = p.2 :=
  Cong.eq_of_eqsRefl hr.toDatabase (FDatabase.mem_closureF_iff.mp (by
    rw [show (p.1, p.2) = p from rfl]; exact hp))

end Egglog
