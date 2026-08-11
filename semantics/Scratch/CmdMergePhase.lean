import EgglogSemantics.Spec.Step

/-!
# Is a merge phase after *every* command semantics-preserving?

Scratch, not part of the library. `CmdStep` now runs `cmdEffect` and then a merge phase,
where `.rule` and `.decl` previously took none.

* `.rule` — neutral: `ruleStep_iff` shows the new step is a merge phase of the *pre-state*
  followed by the old effect, so it adds no state a merge phase before the command does not
  already reach.
* `.decl` — **not** neutral, and freshness does not save it: `decl_enables_merge` gives a
  database where `f` is undeclared and nothing merges, and declaring `f` enables a merge
  step, because a `:merge` result may name a function declared later.
-/

namespace Egglog
namespace Scratch

/-! ### `Cong` reads `eqs` and nothing else -/

theorem Cong.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {a b : Term}
    (hc : Cong d₁ a b) : Cong d₂ a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList d₂ as bs) with
  | assert hab => exact Cong.assert (h ▸ hab)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ ih₁ ih₂ ih => exact Cong.congr ih₁ ih₂ ih
  | nil => exact CongList.nil
  | cons _ _ ih₁ ih₂ => exact CongList.cons ih₁ ih₂

theorem CongList.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := by
  induction hc using CongList.rec (motive_1 := fun a b _ => Cong d₂ a b) with
  | assert hab => exact Cong.assert (h ▸ hab)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ ih₁ ih₂ ih => exact Cong.congr ih₁ ih₂ ih
  | nil => exact CongList.nil
  | cons _ _ ih₁ ih₂ => exact CongList.cons ih₁ ih₂

theorem mem_terms_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Cong.of_eqs_eq h ht

/-! ### Adding a rule commutes with a merge step -/

theorem evalAction_rules (db : Database) (R : Set Rule) (a : Action) :
    evalAction { db with rules := R } a
      = (evalAction db a).map fun d => { d with rules := R } := by
  cases a with
  | expr e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | letBind v e => cases h : e.eval db.sig db.env <;> simp [evalAction, h, Database.addTerm]
  | union e₁ e₂ =>
      cases h₁ : e₁.eval db.sig db.env <;> cases h₂ : e₂.eval db.sig db.env <;>
        simp [evalAction, h₁, h₂, Database.addEq, Database.addTerm]
  | set f args out =>
      cases h₁ : Expr.evalList db.sig args db.env <;>
        cases h₂ : Expr.evalList db.sig out db.env <;>
          simp [evalAction, h₁, h₂, Database.addTerm]

theorem evalActions_rules (R : Set Rule) : ∀ (db : Database) (as : List Action),
    evalActions { db with rules := R } as
      = (evalActions db as).map fun d => { d with rules := R }
  | _, [] => by simp [evalActions]
  | db, a :: as => by
      cases h : evalAction db a with
      | none => simp [evalActions, evalAction_rules, h]
      | some d =>
          have hstep : evalActions { db with rules := R } (a :: as)
              = evalActions { d with rules := R } as := by
            simp [evalActions, evalAction_rules, h]
          rw [hstep, evalActions_rules R d as]
          simp [evalActions, h]

theorem MergeStep.rules_eq {db db' : Database} (h : MergeStep db db') :
    db'.rules = db.rules := by cases h; rfl

theorem MergeStep.setRules {db db' : Database} (h : MergeStep db db') (R : Set Rule) :
    MergeStep { db with rules := R } { db' with rules := R } := by
  cases h with
  | @collide d f decl as bs a b vs body res hsig hmerge ha hb hma hmb hcl heval hres =>
      refine MergeStep.collide (d := { d with rules := R }) hsig hmerge ha hb
        (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hma)
        (mem_terms_of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hmb)
        (CongList.of_eqs_eq (d₁ := db) (d₂ := { db with rules := R }) rfl hcl) ?_ hres
      rw [show ({ db with rules := R, env := mergeEnv a b } : Database)
            = { { db with env := mergeEnv a b } with rules := R } from rfl,
        evalActions_rules, heval]
      rfl

/-- The merge phase a `rules` update gained runs just as well *before* the update. -/
theorem mergeClosure_setRules {db db' : Database} {R : Set Rule} :
    MergeClosure { db with rules := R } db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := R } := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨db, Relation.ReflTransGen.refl, rfl⟩
    | @tail x y _ hstep ih =>
        obtain ⟨d, hcl, rfl⟩ := ih
        have hstep' : MergeStep d { y with rules := d.rules } :=
          MergeStep.setRules hstep d.rules
        have hrules : y.rules = R := MergeStep.rules_eq hstep
        exact ⟨{ y with rules := d.rules }, hcl.tail hstep', by rw [← hrules]⟩
  · rintro ⟨d, hcl, rfl⟩
    induction hcl with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (MergeStep.setRules hstep R)

/-- **`.rule` is neutral.** The new step is a merge phase of the pre-state followed by the
old effect: every state it adds is one the *preceding* merge phase already reaches. -/
theorem ruleStep_iff {db db' : Database} {r : Rule} :
    CmdStep db (.rule r) db' ↔
      ∃ d, MergeClosure db d ∧ db' = { d with rules := insert r db.rules } := by
  simpa [CmdStep, cmdEffect] using
    mergeClosure_setRules (db := db) (db' := db') (R := insert r db.rules)

/-! ### `.decl` is not neutral

`g` is a merge function whose `:merge` result names `f`, and `f` is declared afterwards.
`Program.DeclsFresh` permits that, and no other static check forbids it either, since a
`:merge` body is not walked into. -/

def fdecl : FnDecl := { arity := 0, outArity := 1, merge := none }

def gdecl : FnDecl := { arity := 1, outArity := 1, merge := some (.merge [] [.app "f" []]) }

def t0 : Term := .lit (.int 0)

/-- `g`'s one entry: key `0`, value `0`. -/
def entry : Term := .app "g" [t0, t0]

def db₀ : Database where
  sig := fun n => if n = "g" then some gdecl else none
  eqs := {(t0, t0), (entry, entry)}
  env := []
  rules := ∅

/-- What the old `CmdStep.decl` reached, and the whole of it. -/
def db₁ : Database := { db₀ with sig := Function.update db₀.sig "f" (some fdecl) }

theorem oldDecl : cmdEffect db₀ (.decl "f" fdecl) = some db₁ := rfl

/-- `f` is fresh, so `Check.declFresh` admits `(constructor f)` here. -/
theorem f_fresh : db₀.sig "f" = none := by simp [db₀]

theorem cong_db₀ {a b : Term} (h : Cong db₀ a b) : a = b ∧ (a = t0 ∨ a = entry) := by
  induction h using Cong.rec (motive_2 := fun as bs _ => as = bs) with
  | assert hab =>
      simp only [db₀, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | symm _ ih => obtain ⟨rfl, h⟩ := ih; exact ⟨rfl, h⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨rfl, h⟩ := ih₁; obtain ⟨rfl, -⟩ := ih₂; exact ⟨rfl, h⟩
  | congr _ _ _ ih₁ _ ih => subst ih; exact ⟨rfl, ih₁.2⟩
  | nil => rfl
  | cons _ _ ih₁ ih₂ => obtain ⟨rfl, -⟩ := ih₁; rw [ih₂]

/-- Every application `db₀` holds is `g`'s entry, of the width `g` declares: the state is
`DeclaredTerms`, so the counterexample is not a malformed database. -/
theorem declaredTerms_db₀ : db₀.DeclaredTerms := by
  intro f as hmem
  obtain ⟨-, h | h⟩ := cong_db₀ hmem
  · exact absurd h (by simp [t0])
  · obtain ⟨rfl, rfl⟩ : f = "g" ∧ as = [t0, t0] := by simpa [entry] using h
    exact ⟨gdecl, by simp [db₀], rfl⟩

/-- **Nothing merges before the declaration.** `g`'s `:merge` result names `f`, which is
undeclared, so `Expr.evalList` returns `none` and `MergeStep.collide` cannot fire. -/
theorem no_merge_before (x : Database) : ¬ MergeStep db₀ x := by
  intro h
  cases h with
  | @collide d f decl as bs a b vs body res hsig hmerge _ _ _ _ _ heval hres =>
      have hdecl : decl = gdecl := by
        by_cases hf : f = "g"
        · subst hf; simpa [db₀] using hsig.symm
        · simp [db₀, hf] at hsig
      subst hdecl
      simp only [gdecl, Option.some.injEq, MergeSpec.merge.injEq] at hmerge
      obtain ⟨rfl, rfl⟩ := hmerge
      simp only [evalActions, Option.some.injEq] at heval
      subst heval
      simp [Expr.evalList, Expr.eval, Prim.ofName, Signature.IsCtor, db₀] at hres

/-- **The declaration enables a merge step.** `f` fresh and the state `DeclaredTerms` do
not prevent it: the new `.decl` step reaches a database the old one could not. -/
theorem decl_enables_merge :
    ∃ db', CmdStep db₀ (.decl "f" fdecl) db' ∧ db' ≠ db₁ := by
  have hg : db₁.sig "g" = some gdecl := by simp [db₁, db₀]
  have hctor : db₁.sig.IsCtor "f" := ⟨fdecl, by simp [db₁], rfl⟩
  have hentry : entry ∈ db₁.terms := Cong.assert (by simp [db₁, db₀])
  have ht0 : Cong db₁ t0 t0 := Cong.assert (by simp [db₁, db₀])
  have hres : Expr.evalList db₁.sig [Expr.app "f" []] (mergeEnv [t0] [t0]) =
      some [Term.app "f" []] := by
    simp [Expr.evalList, Expr.eval, Prim.ofName, hctor]
  refine ⟨_, ⟨db₁, rfl, Relation.ReflTransGen.single (MergeStep.collide (f := "g")
    (d := { db₁ with env := mergeEnv [t0] [t0] }) (as := [t0]) (bs := [t0]) (a := [t0])
    (b := [t0]) hg rfl rfl rfl hentry hentry (CongList.cons ht0 CongList.nil) rfl hres)⟩, ?_⟩
  intro hcontra
  have hmem : (Term.app "g" [t0, .app "f" []], Term.app "g" [t0, .app "f" []]) ∈ db₁.eqs := by
    rw [← hcontra]
    exact Or.inr ⟨_, Term.IsSubterm.refl _, rfl⟩
  simp [db₁, db₀, entry, t0] at hmem

end Scratch
end Egglog
