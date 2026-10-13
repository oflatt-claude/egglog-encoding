import EgglogSemantics.Congruence.State
import EgglogSemantics.Congruence.Signature

/-! The two writes of a generated table merge: retain the smaller id and link the
other id to it. No proof payload participates in either operation. -/

namespace Egglog.Congruence

def lowerId (old new : Term) : Term := if Term.blt new old then new else old

def upperId (old new : Term) : Term := if Term.blt new old then old else new

theorem ids_paired (old new : Term) :
    (upperId old new = old ∧ lowerId old new = new) ∨
    (upperId old new = new ∧ lowerId old new = old) := by
  by_cases h : Term.blt new old <;> simp [upperId, lowerId, h]

/-- The generated edge points from the larger id to the smaller one. -/
theorem lowerId_le_upperId (old new : Term) :
    lowerId old new = upperId old new ∨ Term.blt (lowerId old new) (upperId old new) = true := by
  unfold lowerId upperId
  by_cases h : Term.blt new old = true
  · simp [h]
  · simp only [if_neg h]
    rcases eq_or_ne old new with he | hn
    · exact Or.inl he
    · exact Or.inr ((Term.blt_total old new hn).resolve_right h)

theorem eval_merge_max {sig : Signature} {old new : Term} :
    (maxE (.var "old") (.var "new")).eval sig (mergeEnv [old] [new]) =
      some (upperId old new) := by
  simp [maxE, ifE, gtE, Expr.eval, Expr.evalList, mergeEnv, Env.lookup,
    Prim.ofName, Prim.apply, upperId]

theorem eval_merge_min {sig : Signature} {old new : Term} :
    (minE (.var "old") (.var "new")).eval sig (mergeEnv [old] [new]) =
      some (lowerId old new) := by
  simp [minE, ifE, gtE, Expr.eval, Expr.evalList, mergeEnv, Env.lookup,
    Prim.ofName, Prim.apply, lowerId]

/-- This equation also describes failure when UF has not been declared. -/
theorem execActions_mergeBody {m : FDatabase} {old new : Term}
    (henv : m.env = mergeEnv [old] [new]) :
    execActions m mergeBody =
      if (m.sig ufName).isSome then
        some (m.addAtom (.app ufName [upperId old new, lowerId old new]))
      else none := by
  simp [mergeBody, execActions, execAction, Expr.evalAtom,
    show Prim.ofName ufName = none from rfl, henv, Expr.evalList,
    eval_merge_max, eval_merge_min]

theorem execActions_mergeBody_inv {m m' : FDatabase} {old new : Term}
    (henv : m.env = mergeEnv [old] [new])
    (h : execActions m mergeBody = some m') :
    m' = m.addAtom (.app ufName [upperId old new, lowerId old new]) := by
  rw [execActions_mergeBody henv] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem evalList_mergeResult {sig : Signature} {old new : Term} :
    Expr.evalList sig mergeResult (mergeEnv [old] [new]) = some [lowerId old new] := by
  simp [mergeResult, Expr.evalList, eval_merge_min]

/-- Two colliding views justify equality of their output ids through existing source
applications at congruent children. -/
theorem EntrySound.collide {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) : Cong src a b := by
  obtain ⟨as, ham, hal, hae⟩ := ha
  obtain ⟨bs, hbm, hbl, hbe⟩ := hb
  exact hae.symm.trans ((Cong.congr ham hbm (hal.trans hbl.symm)).trans hbe)

theorem EntrySound.select_lower {src : Database} {f : FnName} {cs : List Term} {a b : Term}
    (ha : EntrySound src f cs a) (hb : EntrySound src f cs b) :
    EntrySound src f cs (lowerId a b) := by
  unfold lowerId
  split <;> assumption

/-- With one output and structural keys, ignoring a collision is possible only when
its two rows are identical. Merge rounds already skip such pairs. -/
theorem noConflict_iff_eq {arity : Nat} {r₁ r₂ : Row}
    (hfn : r₁.fn = r₂.fn) (hargs : r₁.args = r₂.args)
    (h₁ : r₁.out.length = 1) (h₂ : r₂.out.length = 1) :
    FDatabase.noConflict ((tableDecl arity).unchangedWidth mergeBody) r₁ r₂ = true ↔
      r₁ = r₂ := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h₁
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp h₂
  simp only [tableDecl, FnDecl.unchangedWidth, mergeBody, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte, FDatabase.noConflict, ha, hb]
  cases r₁
  cases r₂
  simp_all

/-- A table collision creates only one new source equality: the UF edge connecting
its two already justified output ids. The surviving entry is one of the inputs. -/
theorem mergeOneOriented_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : SoundTerms d src)
    (hfire : d.mergeOneOriented cl r₁ r₂ = some e) : SoundTerms e src := by
  rw [FDatabase.mergeOneOriented] at hfire
  split at hfire
  next body res hms =>
    obtain ⟨dc, hdc, hmergedc⟩ := Option.bind_eq_some_iff.mp hms
    obtain ⟨hname, rfl, rfl, hout, huf, -⟩ := hshape r₁.fn dc hdc body res hmergedc
    split at hfire
    next hg =>
      obtain ⟨⟨⟨hfn, hkeys⟩, hmem₁⟩, hmem₂⟩ : ((r₁.fn = r₂.fn ∧
          FDatabase.congrKeys cl r₁.args r₂.args = true) ∧ r₁ ∈ d.rows) ∧ r₂ ∈ d.rows := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] using hg
      have hmg₁ : d.sig.mergeOf r₁.fn ≠ none := by rw [hms]; simp
      have hmg₂ : d.sig.mergeOf r₂.fn ≠ none := by rw [← hfn]; exact hmg₁
      have hE₁ := mem_terms_of_indexOk hr hidx hmem₁ hmg₁
      have hE₂ := mem_terms_of_indexOk hr hidx hmem₂ hmg₂
      have hargs : r₁.args = r₂.args := eq_of_congrKeys hcl hkeys
      obtain ⟨hk₁, hw₁⟩ := hidx.width r₁ hmem₁ dc hdc hmg₁
      obtain ⟨-, hw₂⟩ := hidx.width r₂ hmem₂ dc (by rw [← hfn]; exact hdc) hmg₂
      rw [hout] at hw₁ hw₂
      obtain ⟨new, hnew⟩ := List.length_eq_one_iff.mp hw₁
      obtain ⟨old, hold⟩ := List.length_eq_one_iff.mp hw₂
      have hn : new ∈ d.terms := FDatabase.mem_terms_of_column hsc hE₁ (by rw [hnew]; simp)
      have ho : old ∈ d.terms := FDatabase.mem_terms_of_column hsc hE₂ (by rw [hold]; simp)
      have hE₁' : Term.app r₂.fn (r₂.args ++ [new]) ∈ d.terms := by
        rw [← hfn, ← hargs, ← hnew]; exact hE₁
      have hE₂' : Term.app r₂.fn (r₂.args ++ [old]) ∈ d.terms := by
        rw [← hold]; exact hE₂
      have hc : Cong src old new := by
        rcases hname with hu | ⟨f, hv⟩
        · obtain ⟨key, hkey⟩ : ∃ key, r₁.args = [key] := by
            rw [huf hu] at hk₁
            exact List.length_eq_one_iff.mp hk₁
          have hn' : Cong src key new := h.2 key new (by
            simpa [← hfn, hu, ← hargs, hkey] using hE₁')
          have ho' : Cong src key old := h.2 key old (by
            simpa [← hfn, hu, ← hargs, hkey] using hE₂')
          exact ho'.symm.trans hn'
        · exact EntrySound.collide
            (h.1 f r₂.args old (by simpa [← hfn, hv] using hE₂'))
            (h.1 f r₂.args new (by simpa [← hfn, hv] using hE₁'))
      split at hfire
      next =>
        obtain rfl := Option.some.inj hfire
        exact h.mono_terms (fun _ ht => ht)
      next =>
        obtain ⟨m, hm, hfire⟩ := Option.bind_eq_some_iff.mp hfire
        obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hfire
        have henv : ({ d with env := mergeEnv r₂.out r₁.out } : FDatabase).env =
            mergeEnv [old] [new] := by rw [hnew, hold]
        obtain rfl := execActions_mergeBody_inv henv hm
        have henv' : (FDatabase.addAtom (.app ufName [upperId old new, lowerId old new])
            { d with env := mergeEnv r₂.out r₁.out }).env = mergeEnv [old] [new] := henv
        rw [henv', evalList_mergeResult, Option.some.injEq] at hvs
        subst vs
        have hupper : upperId old new ∈ d.terms := by
          unfold upperId; split <;> assumption
        have hlower : lowerId old new ∈ d.terms := by
          unfold lowerId; split <;> assumption
        have hul : Cong src (upperId old new) (lowerId old new) := by
          rcases ids_paired old new with ⟨hu, hl⟩ | ⟨hu, hl⟩
          · simpa [hu, hl] using hc
          · simpa [hu, hl] using hc.symm
        have hsurv : Term.app r₂.fn (r₂.args ++ [lowerId old new]) ∈ d.terms := by
          unfold lowerId; split <;> assumption
        have hstep := h.addUF hsc hupper hlower hul
        have hsc' := hsc.addTerm (.app ufName [upperId old new, lowerId old new])
        exact SoundTerms.mono_terms (fun _ ht => ht)
          (hstep.addTerm_of_mem hsc' (FDatabase.mem_addTerm_of_mem hsurv))
    next => exact absurd hfire (by simp)
  next => exact absurd hfire (by simp)

theorem mergeOneWith_soundTerms {src : Database} {cl : Finset (Term × Term)}
    {d e : FDatabase} {r₁ r₂ : Row}
    (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (h : SoundTerms d src)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : SoundTerms e src := by
  rcases FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he <;>
    exact mergeOneOriented_soundTerms hshape hr hsc hidx hcl h (he ▸ hm)

/-- **A merge pass preserves the invariant.** The rebuild writes `rows` only, so it costs
nothing; every firing is `mergeOneWith_soundTerms`. -/
theorem mergeRound_soundTerms {src : Database} {d : FDatabase}
    (hshape : MergeShape d.sig)
    (hinv : d.Inv) (hn : d.NoUnions) (h : SoundTerms d src) :
    SoundTerms d.mergeRound src := by
  have hlegal := hshape.mergesLegal
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      SoundTerms d.mergeRound src := by
    refine FDatabase.mergeRound_induction
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ SoundTerms x src)
      ⟨hinv, rfl, hn, h⟩
      ⟨FDatabase.Inv.rebuild hinv FDatabase.closureSound_closureF, rfl, rebuild_noUnions hn,
        h.mono_terms (fun t ht => ht)⟩ ?_
    intro x y r₁ r₂ hx hy
    refine ⟨FDatabase.mergeOneWith_inv hx.1 (by rw [hx.2.1]; exact hlegal) hy,
      ((FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_soundTerms (by rw [hx.2.1]; exact hshape) hx.2.2.1.eqsRefl
      (FDatabase.SubtermClosed.of_wf hx.1.wf) hx.1.index hdiag hx.2.2.2 hy
  exact key.2.2.2

/-- **The whole merge phase preserves the invariant**, which is what `FDatabase.execCmdM` runs
after every top-level action and at the end of every round. -/
theorem mergeSaturateF_soundTerms {src : Database} : ∀ (n : Nat) {d e : FDatabase},
    MergeShape d.sig → d.Inv → d.NoUnions →
    SoundTerms d src → FDatabase.mergeSaturateF n d = some e → SoundTerms e src
  | 0, d, e, _, _, _, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · exact absurd hrun (by simp)
  | n + 1, d, e, hshape, hinv, hn, h, hrun => by
      rw [FDatabase.mergeSaturateF] at hrun
      split at hrun
      · rw [Option.some.injEq] at hrun; exact hrun ▸ h
      · have hsig : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_soundTerms n (by rw [hsig]; exact hshape)
          (FDatabase.Inv.mergeRound_of_legalMerges hinv hshape.mergesLegal)
          (mergeRound_noUnions hn) (mergeRound_soundTerms hshape hinv hn h) hrun

end Egglog.Congruence
