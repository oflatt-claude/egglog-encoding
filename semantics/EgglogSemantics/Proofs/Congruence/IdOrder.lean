import EgglogSemantics.Proofs.Order
import EgglogSemantics.Proofs.Congruence.Correspond

/-! Ordering of the structural ids selected by generated merges. -/

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

/-- `lowerId` is the term `Expr.min` evaluates to. -/
theorem lowerId_eq_least (old new : Term) : lowerId old new = Term.least old new := rfl

theorem lowerId_eq_or (old new : Term) : lowerId old new = old ∨ lowerId old new = new := by
  unfold lowerId
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Both links a collision writes descend: the smaller id is at or below either operand. -/
theorem lowerId_le_left (old new : Term) :
    lowerId old new = old ∨ Term.blt (lowerId old new) old = true := by
  unfold lowerId
  split
  · exact Or.inr ‹_›
  · exact Or.inl rfl

@[inherit_doc lowerId_le_left]
theorem lowerId_le_right (old new : Term) :
    lowerId old new = new ∨ Term.blt (lowerId old new) new = true := by
  unfold lowerId
  by_cases h : Term.blt new old = true
  · rw [if_pos h]; exact Or.inl rfl
  · rw [if_neg h]
    rcases eq_or_ne old new with he | hn
    · exact Or.inl he
    · exact Or.inr ((Term.blt_total old new hn).resolve_right h)

/-- Distinct ids are strictly ordered, so the link from the larger one is an edge. -/
theorem lowerId_lt_upperId {old new : Term} (h : old ≠ new) :
    Term.blt (lowerId old new) (upperId old new) = true := by
  rcases lowerId_le_upperId old new with heq | hlt
  · exfalso
    unfold lowerId upperId at heq
    split at heq
    · exact h heq.symm
    · exact h heq
  · exact hlt

/-- The smaller id is source-congruent to either operand once the operands are. -/
theorem cong_lowerId_left {src : Database} {a b : Term} (h : Cong src a b) :
    Cong src a (lowerId a b) := by
  unfold lowerId
  split
  · exact h
  · exact h.mem_of.1

@[inherit_doc cong_lowerId_left]
theorem cong_lowerId_right {src : Database} {a b : Term} (h : Cong src a b) :
    Cong src b (lowerId a b) := by
  unfold lowerId
  split
  · exact h.mem_of.2
  · exact h.symm

/-- The compiler explicitly binds its one-column inputs as `old` and `new`. -/
theorem mergeEnv_pair (old new : Term) :
    mergeEnv ["old"] ["new"] [old] [new] =
      [("old", old), ("new", new)] := rfl

theorem eval_merge_min {sig : Signature} {old new : Term} :
    (Expr.min (.var "old") (.var "new")).eval sig (mergeEnv ["old"] ["new"] [old] [new]) =
      some (lowerId old new) := by
  simp [Expr.eval, mergeEnv_pair, Env.lookup, lowerId, Term.least]


end Egglog.Congruence
