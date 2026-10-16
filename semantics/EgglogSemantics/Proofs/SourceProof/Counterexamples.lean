import EgglogSemantics.Proofs.SourceProof.Support

/-! One stored `Table(A)` row and `A = B` can justify the spelling `Table(B)`.
They do not establish a second row or authorize running its merge body. -/

namespace Egglog.SourceProof.Counterexamples

set_option linter.hashCommand false

private def ctor : FnDecl := ⟨0, 1, none, none⟩
private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def c : Term := .app "C" []
private def row (x : Term) : Term := .app "Table" [x]
private def body : List Action := [.union (.var "old") c.toExpr]

private def seedActions : List Action :=
  [.expr (row a).toExpr, .union a.toExpr b.toExpr, .expr c.toExpr]

private def program : Program :=
  [.decl "A" ctor, .decl "B" ctor, .decl "C" ctor,
   .decl "Table" ⟨0, 1, some (.merge ["old"] ["new"] body [.var "old"]), none⟩,
   .rule ⟨[], seedActions, "R"⟩, .saturate "R"]

-- An empty-query rule supplies both anchors.
#guard (contextOf program).any fun C =>
  (actionsFacts C.sig [] seedActions).any fun fs =>
    decide ((⟨row a, row a⟩ : Claim) ∈ fs ∧ (⟨a, b⟩ : Claim) ∈ fs)

private def snapshot : Database :=
  { Database.empty with eqs := {(row a, row a), (a, b), (c, c)} }

private def isC : Term → Bool
  | .lit _ => false
  | .app f _ => f == "C"

private theorem same_isC {s t : Term} (h : Cong snapshot s t) : isC s = isC t := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct hp =>
      simp only [snapshot, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp | hp <;> cases hp <;> rfl
  | subterm => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr => rfl
  | nil | cons => trivial

private theorem merge_equality_absent : ¬ Cong snapshot a c := by
  intro h
  have he := same_isC h
  change false = true at he
  contradiction

private theorem second_row_absent : (row b, row b) ∉ snapshot.eqs := by
  simp [snapshot, row, a, b, c]

-- Running the merge body at two row spellings would assert the unsupported equality.
#guard (contextOf program).any fun C =>
  (actionsFacts C.sig (mergeEnv ["old"] ["new"] [a] [b]) body).any fun fs =>
    decide ((⟨a, c⟩ : Claim) ∈ fs)

/-- Congruence establishes the second spelling without establishing a collision. -/
private theorem second_spelling {db : Database} (hw : db.WF)
    (hrow : Cong db (row a) (row a)) (hab : Cong db a b) :
    Claim.Supported db ⟨row b, row b⟩ := by
  have base := Claim.Holds.supported (c := ⟨row a, row a⟩) hw hrow
  have child := Claim.Holds.supported (c := ⟨a, b⟩) hw hab
  have rewritten := base.congr (i := 0) child rfl
  exact rewritten.symm.trans rewritten

end Egglog.SourceProof.Counterexamples
