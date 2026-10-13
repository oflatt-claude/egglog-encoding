import EgglogSemantics.Source.Domain

/-! Source arity consistency, shared by the independent encoding passes. -/

namespace Egglog

/-- All occurrences of a source function agree on its arity. -/
def Program.AritiesAgree (P : Program) : Prop :=
  ∀ fk ∈ P.ctors, ∀ gl ∈ P.ctors, fk.1 = gl.1 → fk.2 = gl.2

/-! ### The clause, and the notion the tree already had

`Program.EncodeDomain.aritiesAgree` is stated over `Tests/Egg.lean`'s
`Program.arityConflicts` — the notion `Impl/Check.lean` and `Encoding/Encode.lean` already
cite as egglog's "Function already bound" — and `Program.AritiesAgree` is the form the
legality proofs consume, over `Program.ctors`. The two are the same list read two ways:
`Expr.ctors` *is* `Expr.fnArities`, and `Cmd.ctors` is contained in `Cmd.fnArities` at every
command (a function-entry atoms head and a `:merge` body are the two entries only the latter
records, and the domain has neither). `EncodeDomain.noPrim` is what pays for the primitive
filter. -/

mutual

/-- The two readings of an expression's applied names are one. -/
theorem Expr.ctors_eq_fnArities : ∀ (e : Expr), e.ctors = e.fnArities
  | .lit _ => rfl
  | .var _ => rfl
  | .app f args => by
      rw [Expr.ctors, Expr.fnArities, Expr.ctorsList_eq_fnAritiesL args]

@[inherit_doc Expr.ctors_eq_fnArities]
theorem Expr.ctorsList_eq_fnAritiesL : ∀ (es : List Expr),
    Expr.ctorsList es = Expr.fnAritiesL es
  | [] => rfl
  | e :: es => by
      rw [Expr.ctorsList, Expr.fnAritiesL, Expr.ctors_eq_fnArities e,
        Expr.ctorsList_eq_fnAritiesL es]

end

@[inherit_doc Expr.ctors_eq_fnArities]
theorem Action.ctors_eq_fnArities (a : Action) : a.ctors = a.fnArities := by
  cases a <;>
    simp [Action.ctors, Action.fnArities, Expr.ctors_eq_fnArities]

/-- A read's own head is the one entry `Program.ctors` does not record and `fnArities`
does. -/
theorem Pattern.mem_fnArities_of_mem_ctors {p : Pattern} {fk : FnName × Nat}
    (h : fk ∈ p.ctors) : fk ∈ p.fnArities := by
  cases p <;>
    simp only [Pattern.ctors, Pattern.fnArities, Expr.ctors_eq_fnArities,
      List.mem_append] at h ⊢ <;> tauto

@[inherit_doc Pattern.mem_fnArities_of_mem_ctors]
theorem Cmd.mem_fnArities_of_mem_ctors {c : Cmd} {fk : FnName × Nat}
    (hc : c.CtorDecl) (h : fk ∈ c.ctors) : fk ∈ c.fnArities := by
  cases c with
  | action a => rw [Cmd.ctors, Action.ctors_eq_fnArities] at h; exact h
  | rule r =>
      rw [Cmd.ctors] at h
      rw [Cmd.fnArities]
      rcases List.mem_append.mp h with h' | h'
      · obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp h'
        exact List.mem_append_left _
          (List.mem_flatMap.mpr ⟨p, hp, Pattern.mem_fnArities_of_mem_ctors hf⟩)
      · obtain ⟨a, ha, hf⟩ := List.mem_flatMap.mp h'
        exact List.mem_append_right _
          (List.mem_flatMap.mpr ⟨a, ha, Action.ctors_eq_fnArities a ▸ hf⟩)
  | run R => exact absurd h (by simp [Cmd.ctors])
  | saturate R => exact absurd h (by simp [Cmd.ctors])
  | decl f dc =>
      rw [Cmd.ctors] at h
      obtain rfl : fk = (f, dc.arity) := by simpa using h
      change dc.merge = none at hc
      simp [Cmd.fnArities, FnDecl.entryWidth, hc]

/-- A list of at most one element has at most one element. -/
private theorem eq_of_length_le_one {α : Type} {l : List α} (h : l.length ≤ 1) :
    ∀ a ∈ l, ∀ b ∈ l, a = b := by
  match l with
  | [] => intro a ha; exact absurd ha (by simp)
  | [x] => intro a ha b hb; rw [List.mem_singleton] at ha hb; rw [ha, hb]
  | x :: y :: t => exact absurd h (by simp)

/-- **The domain's clause, in the form the legality proofs consume.** -/
theorem Program.EncodeDomain.aritiesAgree' {P : Program} (h : P.EncodeDomain) :
    P.AritiesAgree := by
  have hsub : ∀ fk ∈ P.ctors, fk ∈ P.fnArities := by
    intro fk hfk
    obtain ⟨c, hc, hfc⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hfk)
    refine List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_flatMap.mpr
      ⟨c, hc, Cmd.mem_fnArities_of_mem_ctors (h.ctorsOnly c hc) hfc⟩, ?_⟩)
    rw [h.noPrim fk hfk]; rfl
  intro fk hfk gl hgl hname
  by_contra hne
  have hfa : fk ∈ P.fnArities := hsub fk hfk
  have hga : gl ∈ P.fnArities := hsub gl hgl
  have hlen : (P.fnArities.filter fun fa => fa.1 == fk.1).length ≤ 1 := by
    by_contra hc
    refine absurd h.aritiesAgree (fun hz => ?_)
    rw [Program.arityConflicts, List.dedup_eq_nil, List.filter_eq_nil_iff] at hz
    exact absurd (hz fk.1 (List.mem_map_of_mem hfa)) (by simpa using Nat.lt_of_not_le hc)
  refine hne ?_
  have := eq_of_length_le_one hlen fk (List.mem_filter.mpr ⟨hfa, by simp⟩)
    gl (List.mem_filter.mpr ⟨hga, by simp [hname]⟩)
  rw [this]

/-- A source name is not in the generated namespace. -/
theorem noAt_of_mem_ctors {P : Program} (hdom : P.EncodeDomain) {fk : FnName × Nat}
    (h : fk ∈ P.ctors) : ¬ "@".isPrefixOf fk.1 :=
  hdom.noAt fk.1 (by
    rw [Program.names]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨fk, h, rfl⟩)))))

end Egglog
