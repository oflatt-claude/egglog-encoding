import EgglogSemantics.Encoding.Encode
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Spec.Step

/-! # Is `Rebuilt` satisfiable?

`Encoding/Encode.lean`'s `Rebuilt P d` is the hypothesis `encode_complete`,
`encode_simulation` and `encode_simulation_run` carry. This file settles whether it is
satisfiable, over two source programs that differ only in *which* term is built:

* `P₁ = (f 1) (union 1 2)` — the union's larger endpoint `2` is not a view key, so the
  rebuild has nothing to move. `rebuilt₁ : Rebuilt P₁ d₁` — **satisfiable**.
* `P₀ = (f 2) (union 1 2)` — the union's larger endpoint `2` *is* the view key. The
  column-0 rebuild rule then has a firing that writes a row the state lacks, and neither
  an action nor a merge step can ever write it, because `encode P₀` contains no
  `Cmd.run`. `not_rebuilt₀ : ¬ Rebuilt P₀ d₀`.

`rebuilt_rekeys` is the general form of the second point: **any** state satisfying
`Rebuilt` must already hold every re-keyed view row. `d₀` and `d₁` are the states the two
encoded programs run to (hand-computed from `encode₀`/`encode₁`; the `ProgramStep`
derivation itself is not formalized here).
-/

namespace Egglog
namespace RebuiltVacuity

/-! ### The two source programs -/

/-- `(f 2)` then `(union 1 2)`. The union's larger endpoint `2` is a view key. -/
def P₀ : Program :=
  [.action (.expr (.app "f" [.lit (.int 2)])),
   .action (.union (.lit (.int 1)) (.lit (.int 2)))]

/-- `(f 1)` then `(union 1 2)`. The union's larger endpoint `2` is *not* a view key. -/
def P₁ : Program :=
  [.action (.expr (.app "f" [.lit (.int 1)])),
   .action (.union (.lit (.int 1)) (.lit (.int 2)))]

/-- Purely syntactic `run` test; `Cmd` derives nothing. -/
def isRun : Cmd → Bool
  | .run => true
  | _ => false

example : P₀.all (fun c => !isRun c) = true := by rfl

example : (encode P₀).all (fun c => !isRun c) = true := by rfl

example : (encode P₁).all (fun c => !isRun c) = true := by rfl

example : Program.ctors P₀ = [("f", 1)] := by rfl
example : Program.ctors P₁ = [("f", 1)] := by rfl

/-! ### The maintenance rules, spelled out -/

/-- `@fView`. -/
def viewF : FnName := viewName "f"
/-- `@fTerm`. -/
def termF : FnName := termName "f"

/-- The e-class rebuild rule for `f`. -/
def eclassRuleF : Rule :=
  { query := [.values [.var "@e"] viewF [.var "@c0"],
              .values [.var "@x"] ufName [.var "@e"]],
    actions := [.set viewF [.var "@c0"] [.var "@x"]] }

/-- The column-0 rebuild rule for `f`: re-key a view row to its child's `@UF` leader. -/
def colRuleF : Rule :=
  { query := [.values [.var "@e"] viewF [.var "@c0"],
              .values [.var "@x"] ufName [.var "@c0"]],
    actions := [.set viewF [.var "@x"] [.var "@e"]] }

theorem maintenance₀ :
    maintenanceRules P₀ = [pathCompressRule, eclassRuleF, colRuleF] := by rfl

theorem maintenance₁ :
    maintenanceRules P₁ = [pathCompressRule, eclassRuleF, colRuleF] := by rfl

theorem colRuleF_mem₀ : colRuleF ∈ maintenanceRules P₀ := by
  rw [maintenance₀]; exact .tail _ (.tail _ (.head _))

theorem colRuleF_mem₁ : colRuleF ∈ maintenanceRules P₁ := by
  rw [maintenance₁]; exact .tail _ (.tail _ (.head _))

theorem eclassRuleF_mem₁ : eclassRuleF ∈ maintenanceRules P₁ := by
  rw [maintenance₁]; exact .tail _ (.head _)

theorem pathCompressRule_mem₁ : pathCompressRule ∈ maintenanceRules P₁ := by
  rw [maintenance₁]; exact .head _

/-! ### The encoded programs, spelled out -/

theorem encode₀ :
    encode P₀ =
      [.decl ufName ufDecl, .decl viewF (viewDecl 1), .decl termF (termDecl 1),
       .rule pathCompressRule, .rule eclassRuleF, .rule colRuleF,
       .action (.set termF [.lit (.int 2), .app "f" [.lit (.int 2)]] [unitE]),
       .action (.set viewF [.lit (.int 2)] [.app "f" [.lit (.int 2)]]),
       .action (.letBind (freshVar 0) (.app viewF [.lit (.int 2)])),
       .action (.set ufName [maxE (.lit (.int 1)) (.lit (.int 2))]
                            [minE (.lit (.int 1)) (.lit (.int 2))])] := by
  rfl

theorem encode₁ :
    encode P₁ =
      [.decl ufName ufDecl, .decl viewF (viewDecl 1), .decl termF (termDecl 1),
       .rule pathCompressRule, .rule eclassRuleF, .rule colRuleF,
       .action (.set termF [.lit (.int 1), .app "f" [.lit (.int 1)]] [unitE]),
       .action (.set viewF [.lit (.int 1)] [.app "f" [.lit (.int 1)]]),
       .action (.letBind (freshVar 0) (.app viewF [.lit (.int 1)])),
       .action (.set ufName [maxE (.lit (.int 1)) (.lit (.int 2))]
                            [minE (.lit (.int 1)) (.lit (.int 2))])] := by
  rfl

/-! ### `encode`'s domain -/

theorem encodeDomain₀ : P₀.EncodeDomain where
  ctorsOnly := by
    intro c hc f d h
    simp only [P₀, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact Cmd.noConfusion h
  noSet := by
    intro c hc
    simp only [P₀, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial
  noPrim := by decide
  noAt := by decide +kernel
  noAtVar := by decide

theorem encodeDomain₁ : P₁.EncodeDomain where
  ctorsOnly := by
    intro c hc f d h
    simp only [P₁, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact Cmd.noConfusion h
  noSet := by
    intro c hc
    simp only [P₁, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> trivial
  noPrim := by decide
  noAt := by decide +kernel
  noAtVar := by decide

/-! ### Terms and the target signature -/

/-- `0`, the stand-in for `()`. -/
def t0 : Term := .lit (.int 0)
/-- `1`. -/
def t1 : Term := .lit (.int 1)
/-- `2`. -/
def t2 : Term := .lit (.int 2)
/-- `f 2`, the skolem id of `(f 2)`. -/
def ft2 : Term := .app "f" [t2]

/-- The signature the three prelude `decl`s install. -/
def sig₀ : Signature :=
  Function.update
    (Function.update
      (Function.update (fun _ => (none : Option FnDecl)) ufName (some ufDecl))
      viewF (some (viewDecl 1)))
    termF (some (termDecl 1))

/-! ### The state `encode P₀` runs to

Computed by hand from `encode₀`: the three `set`s, the `letBind`, the constructor rows
`addTerm` inserts, and the two `@UF` self-loops the merge phases write. -/

/-- `d₀`'s terms. -/
def terms₀ : List Term := [t0, t1, t2, ft2]

/-- `d₀`'s rows. -/
def rows₀ : List Row :=
  [ ⟨"f", [t2], [ft2]⟩,
    ⟨termF, [t2, ft2], [t0]⟩,
    ⟨viewF, [t2], [ft2]⟩,
    ⟨ufName, [ft2], [ft2]⟩,
    ⟨ufName, [t2], [t1]⟩,
    ⟨ufName, [t1], [t1]⟩ ]

/-- The state `encode P₀` runs to. -/
def d₀ : Database where
  sig := sig₀
  terms := {t | t ∈ terms₀}
  rows := {r | r ∈ rows₀}
  eqs := ∅
  env := [(freshVar 0, ft2)]
  rules := {r | r ∈ maintenanceRules P₀}

/-! ### Environment helpers -/

theorem lookup_append_of_none {v : Var} {σ τ : Env} (h : Env.lookup v σ = none) :
    Env.lookup v (σ ++ τ) = Env.lookup v τ := by
  induction σ with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨w, t⟩ := b
    simp only [Env.lookup, List.cons_append] at h ⊢
    by_cases hvw : v = w
    · simp only [if_pos hvw] at h; exact absurd h (by simp)
    · simp only [if_neg hvw] at h ⊢; exact ih h

theorem freeVars_var_of_none {v : Var} {σ : Env} (h : Env.lookup v σ = none) :
    Expr.freeVars (.var v) σ = [v] := by simp [Expr.freeVars, h]

/-! ### `addTerms`, the extension a `values` atom reads its congruence in

`Proofs/Database.lean` has these; this file imports only `Spec/`, and two four-line
inductions are cheaper than the coupling. -/

theorem mem_addTerms {db : Database} {ts : List Term} {t : Term} (h : t ∈ db.terms) :
    t ∈ (db.addTerms ts).terms := by
  induction ts generalizing db with
  | nil => exact h
  | cons u us ih => exact ih (Or.inl h)

theorem addTerms_eqs {db : Database} {ts : List Term} : (db.addTerms ts).eqs = db.eqs := by
  induction ts generalizing db with
  | nil => rfl
  | cons u us ih => exact ih

/-! ### `Rebuilt` forces every view row to be re-keyed already

The column-0 rebuild rule fires on any state holding a view row `@fView [c] ↦ [e]` and a
union-find row `@UF [c] ↦ [x]`, and writes `@fView [x] ↦ [e]`. So a `Rebuilt` state must
already hold that row — no reachability argument needed. -/
theorem rebuilt_rekeys {P : Program} {d : Database}
    (hmem : colRuleF ∈ maintenanceRules P)
    (he0 : Env.lookup "@e" d.env = none)
    (hc0 : Env.lookup "@c0" d.env = none)
    (hx0 : Env.lookup "@x" d.env = none)
    {c e x : Term}
    (hview : Row.mk viewF [c] [e] ∈ d.rows) (huf : Row.mk ufName [c] [x] ∈ d.rows)
    (hcT : c ∈ d.terms) (heT : e ∈ d.terms) (hxT : x ∈ d.terms)
    (hreb : Rebuilt P d) : Row.mk viewF [x] [e] ∈ d.rows := by
  classical
  -- the two per-pattern substitutions and their union
  let σ₁ : Env := [("@e", e), ("@c0", c)]
  let σ₂ : Env := [("@x", x), ("@c0", c)]
  let σ : Env := σ₁ ++ σ₂
  have d1 : σ₁ = [("@e", e), ("@c0", c)] := rfl
  have d2 : σ₂ = [("@x", x), ("@c0", c)] := rfl
  -- environment lookups
  have l1e : Env.lookup "@e" (d.env ++ σ₁) = some e := by
    rw [lookup_append_of_none he0]; rfl
  have l1c : Env.lookup "@c0" (d.env ++ σ₁) = some c := by
    rw [lookup_append_of_none hc0]; rfl
  have l2x : Env.lookup "@x" (d.env ++ σ₂) = some x := by
    rw [lookup_append_of_none hx0]; rfl
  have l2c : Env.lookup "@c0" (d.env ++ σ₂) = some c := by
    rw [lookup_append_of_none hc0]; rfl
  have lσx : Env.lookup "@x" (d.env ++ σ) = some x := by
    rw [lookup_append_of_none hx0]; rfl
  have lσe : Env.lookup "@e" (d.env ++ σ) = some e := by
    rw [lookup_append_of_none he0]; rfl
  -- free variables
  have hfe : Expr.freeVars (.var "@e") d.env = ["@e"] := freeVars_var_of_none he0
  have hfc : Expr.freeVars (.var "@c0") d.env = ["@c0"] := freeVars_var_of_none hc0
  have hfx : Expr.freeVars (.var "@x") d.env = ["@x"] := freeVars_var_of_none hx0
  have hv1 : Expr.freeVarsList [Expr.var "@e"] d.env ∪
      Expr.freeVarsList [Expr.var "@c0"] d.env = ["@e", "@c0"] := by
    show (Expr.freeVars (.var "@e") d.env ∪ Expr.freeVarsList [] d.env) ∪
      (Expr.freeVars (.var "@c0") d.env ∪ Expr.freeVarsList [] d.env) = _
    rw [hfe, hfc]; rfl
  have hv2 : Expr.freeVarsList [Expr.var "@x"] d.env ∪
      Expr.freeVarsList [Expr.var "@c0"] d.env = ["@x", "@c0"] := by
    show (Expr.freeVars (.var "@x") d.env ∪ Expr.freeVarsList [] d.env) ∪
      (Expr.freeVars (.var "@c0") d.env ∪ Expr.freeVarsList [] d.env) = _
    rw [hfx, hfc]; rfl
  -- the operands are variables bound to terms `d` holds, so the database a `values` atom
  -- extends with them still holds them
  have hext : ∀ (as vs : List Term) {t : Term}, t ∈ d.terms →
      t ∈ ((d.addTerms as).addTerms vs).terms := by
    intro _ _ _ ht; exact mem_addTerms (mem_addTerms ht)
  -- the two `MValidSubst`s
  have s1 : MValidSubst d (.values [.var "@e"] viewF [.var "@c0"]) σ₁ := by
    refine .values ⟨?_, ?_⟩ (by rw [Expr.evalList_cons, Expr.eval_var, l1e]; rfl)
      (by rw [Expr.evalList_cons, Expr.eval_var, l1c]; rfl)
      (.cons (.refl (hext _ _ hcT)) .nil) (.cons (.refl (hext _ _ heT)) .nil) hview
    · rw [hv1]; exact List.Perm.refl _
    · rintro ⟨v, t⟩ hb
      rw [d1] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
      rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact heT
      · exact hcT
  have s2 : MValidSubst d (.values [.var "@x"] ufName [.var "@c0"]) σ₂ := by
    refine .values ⟨?_, ?_⟩ (by rw [Expr.evalList_cons, Expr.eval_var, l2x]; rfl)
      (by rw [Expr.evalList_cons, Expr.eval_var, l2c]; rfl)
      (.cons (.refl (hext _ _ hcT)) .nil) (.cons (.refl (hext _ _ hxT)) .nil) huf
    · rw [hv2]; exact List.Perm.refl _
    · rintro ⟨v, t⟩ hb
      rw [d2] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
      rcases hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hxT
      · exact hcT
  -- the query substitution
  have hq : MValidQuerySubst d colRuleF.query σ := by
    refine ⟨[σ₁, σ₂], ?_, ?_⟩
    · exact .cons s1 (.cons s2 .nil)
    · refine .step ⟨?_, rfl⟩ (.single σ)
      rintro ⟨v, tt⟩ hb u hu
      rw [d1] at hb
      rw [d2] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [Env.lookup] at hu
      · simp [Env.lookup] at hu
        exact hu
  -- the head runs
  have hact : evalLocalActions d colRuleF.actions σ
      = some { (({ d with env := d.env ++ σ }).addRow viewF [x] [e]) with
        env := d.env, rules := d.rules } := by
    have h1 : evalAction { d with env := d.env ++ σ } (.set viewF [.var "@x"] [.var "@e"])
        = some (({ d with env := d.env ++ σ }).addRow viewF [x] [e]) := by
      rw [evalAction,
        show Expr.evalList d.sig [Expr.var "@x"] ({ d with env := d.env ++ σ } : Database).env
          = some [x] by rw [Expr.evalList_cons, Expr.eval_var]; erw [lσx]; rfl,
        Option.bind_some,
        show Expr.evalList d.sig [Expr.var "@e"] ({ d with env := d.env ++ σ } : Database).env
          = some [e] by rw [Expr.evalList_cons, Expr.eval_var]; erw [lσe]; rfl]
      rfl
    rw [evalLocalActions, show colRuleF.actions = [Action.set viewF [.var "@x"] [.var "@e"]]
      from rfl, evalActions_cons, h1]
    rfl
  have hres : ({ (({ d with env := d.env ++ σ }).addRow viewF [x] [e]) with
      env := d.env, rules := d.rules } : Database) ∈ RuleResults d colRuleF :=
    ⟨σ, hq, hact⟩
  have hcont := hreb.1 colRuleF hmem _ hres
  exact hcont.rows (Set.mem_insert _ _)

/-! ### Applying it to `d₀`: `encode P₀`'s state is not `Rebuilt` -/

theorem sigView₀ : d₀.sig.mergeOf viewF = MergeSpec.merge mergeBody mergeResult := rfl
theorem sigUF₀ : d₀.sig.mergeOf ufName = MergeSpec.merge mergeBody mergeResult := rfl

theorem hV₀ : d₀.sig.mergeOf viewF ≠ MergeSpec.union := by
  rw [sigView₀]; exact fun h => MergeSpec.noConfusion h

theorem hU₀ : d₀.sig.mergeOf ufName ≠ MergeSpec.union := by
  rw [sigUF₀]; exact fun h => MergeSpec.noConfusion h

theorem env_e₀ : Env.lookup "@e" d₀.env = none := by rfl
theorem env_c₀ : Env.lookup "@c0" d₀.env = none := by rfl
theorem env_x₀ : Env.lookup "@x" d₀.env = none := by rfl

theorem viewRow₀ : Row.mk viewF [t2] [ft2] ∈ d₀.rows := by
  show Row.mk viewF [t2] [ft2] ∈ rows₀
  decide

theorem ufRow₀ : Row.mk ufName [t2] [t1] ∈ d₀.rows := by
  show Row.mk ufName [t2] [t1] ∈ rows₀
  decide

/-- The re-keyed row the rebuild wants is **not** there. -/
theorem missing₀ : Row.mk viewF [t1] [ft2] ∉ d₀.rows := by
  show ¬ (Row.mk viewF [t1] [ft2] ∈ rows₀)
  decide

/-- **`encode P₀`'s final state is not `Rebuilt`.** -/
theorem not_rebuilt₀ : ¬ Rebuilt P₀ d₀ := fun hreb =>
  missing₀ (rebuilt_rekeys colRuleF_mem₀ env_e₀ env_c₀ env_x₀ viewRow₀ ufRow₀
    (by show t2 ∈ terms₀; decide) (by show ft2 ∈ terms₀; decide)
    (by show t1 ∈ terms₀; decide) hreb)

/-! ### Generic tools for the positive direction -/

/-! In a database with no asserted equalities whose `.union`-function rows are all
constructor rows, `MCong` is syntactic equality (`encode_mcong_eq`'s content). -/
mutual

/-- `MCong` is syntactic equality there. -/
theorem mcong_eq {db : Database} (heq : db.eqs = ∅)
    (hrows : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args]) {x y : Term} (h : MCong db x y) : x = y := by
  match h with
  | .assert hm => rw [heq] at hm; simp at hm
  | .refl _ => rfl
  | .symm h => exact (mcong_eq heq hrows h).symm
  | .trans h₁ h₂ => exact (mcong_eq heq hrows h₁).trans (mcong_eq heq hrows h₂)
  | .fd ha hb hu hl hxy =>
    have hab := mcongList_eq heq hrows hl
    have hA := hrows _ ha hu
    have hB := hrows _ hb hu
    simp only at hA hB
    subst hab
    rw [hA, hB] at hxy
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rfl

/-- `mcong_eq` over lists. -/
theorem mcongList_eq {db : Database} (heq : db.eqs = ∅)
    (hrows : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args]) {xs ys : List Term} (h : MCongList db xs ys) : xs = ys := by
  match h with
  | .nil => rfl
  | .cons hab hl => rw [mcong_eq heq hrows hab, mcongList_eq heq hrows hl]

end

/-- Adding a term the database already holds, with its constructor rows, changes nothing. -/
theorem addTerm_eq_self {db : Database} {t : Term}
    (h1 : t.subterms ⊆ db.terms) (h2 : t.ctorRows ⊆ db.rows) : db.addTerm t = db := by
  unfold Database.addTerm
  rw [Set.union_eq_self_of_subset_right h1, Set.union_eq_self_of_subset_right h2]

theorem addTerms_eq_self {db : Database} {ts : List Term}
    (h : ∀ t ∈ ts, t.subterms ⊆ db.terms ∧ t.ctorRows ⊆ db.rows) : db.addTerms ts = db := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have h1 := h t (by simp)
    show Database.addTerms ts (db.addTerm t) = db
    rw [addTerm_eq_self h1.1 h1.2]
    exact ih fun s hs => h s (by simp [hs])

/-- Asserting a row the database already holds, over terms it already holds, changes
nothing. -/
theorem addRow_eq_self {db : Database} {f : FnName} {as vs : List Term}
    (h : ∀ t ∈ as ++ vs, t.subterms ⊆ db.terms ∧ t.ctorRows ⊆ db.rows)
    (hrow : Row.mk f as vs ∈ db.rows) : db.addRow f as vs = db := by
  have h1 : db.addTerms as = db := addTerms_eq_self fun t ht => h t (by simp [ht])
  have h2 : db.addTerms vs = db := addTerms_eq_self fun t ht => h t (by simp [ht])
  unfold Database.addRow
  rw [h1, h2, Set.insert_eq_self.mpr hrow]

/-! ### Inverting evaluation -/

theorem meval_var' {sig : Signature} {σ : Env} {v : Var} {t : Term}
    (h : Expr.eval sig (.var v) σ = some t) : Env.lookup v σ = some t := h

theorem mevalList_one {sig : Signature} {σ : Env} {e : Expr} {ts : List Term}
    (h : Expr.evalList sig [e] σ = some ts) :
    ∃ t, ts = [t] ∧ Expr.eval sig e σ = some t := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, hrest⟩ := h
  rw [Expr.evalList_nil, Option.map_some, Option.some.injEq] at hrest
  exact ⟨t, hrest.symm, ht⟩

theorem mevalList_two {sig : Signature} {σ : Env} {e₁ e₂ : Expr} {ts : List Term}
    (h : Expr.evalList sig [e₁, e₂] σ = some ts) :
    ∃ u v, ts = [u, v] ∧ Expr.eval sig e₁ σ = some u ∧ Expr.eval sig e₂ σ = some v := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨u, hu, hrest⟩ := h
  obtain ⟨vs, hvs, heq⟩ := Option.map_eq_some_iff.mp hrest
  obtain ⟨v, rfl, hv⟩ := mevalList_one hvs
  exact ⟨u, v, heq.symm, hu, hv⟩

/-- `(ordering-max old new)` in the merge environment of a self-collision is `p`. -/
theorem meval_max_self {sig : Signature} {p t : Term}
    (h : Expr.eval sig (maxE (.var "old") (.var "new")) [("old", p), ("new", p)]
      = some t) : t = p := by
  rw [maxE, Expr.eval_app_prim (p := Prim.orderingMax) rfl, Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, happly⟩ := h
  obtain ⟨u, v, rfl, hu, hv⟩ := mevalList_two hts
  have hu' : u = p := by have := meval_var' hu; simpa [Env.lookup] using this.symm
  have hv' : v = p := by have := meval_var' hv; simpa [Env.lookup] using this.symm
  subst hu'; subst hv'
  simp only [Prim.apply, Term.orderingMax, Option.some.injEq] at happly
  rw [← happly]
  split <;> rfl

/-- `(ordering-min old new)` in the merge environment of a self-collision is `p`. -/
theorem meval_min_self {sig : Signature} {p t : Term}
    (h : Expr.eval sig (minE (.var "old") (.var "new")) [("old", p), ("new", p)]
      = some t) : t = p := by
  rw [minE, Expr.eval_app_prim (p := Prim.orderingMin) rfl, Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, happly⟩ := h
  obtain ⟨u, v, rfl, hu, hv⟩ := mevalList_two hts
  have hu' : u = p := by have := meval_var' hu; simpa [Env.lookup] using this.symm
  have hv' : v = p := by have := meval_var' hv; simpa [Env.lookup] using this.symm
  subst hu'; subst hv'
  simp only [Prim.apply, Term.orderingMin, Option.some.injEq] at happly
  rw [← happly]
  split <;> rfl

/-! ### The state `encode P₁` runs to

`P₁` unions the two distinct terms `1` and `2`, but the union's larger endpoint `2` is
not a view key, so the rebuild has nothing to move. -/

/-- `f 1`. -/
def ft1 : Term := .app "f" [t1]

/-- `d₁`'s terms. -/
def terms₁ : List Term := [t0, t1, t2, ft1]

/-- `d₁`'s rows. -/
def rows₁ : List Row :=
  [ ⟨"f", [t1], [ft1]⟩,
    ⟨termF, [t1, ft1], [t0]⟩,
    ⟨viewF, [t1], [ft1]⟩,
    ⟨ufName, [ft1], [ft1]⟩,
    ⟨ufName, [t2], [t1]⟩,
    ⟨ufName, [t1], [t1]⟩ ]

/-- The state `encode P₁` runs to. -/
def d₁ : Database where
  sig := sig₀
  terms := {t | t ∈ terms₁}
  rows := {r | r ∈ rows₁}
  eqs := ∅
  env := [(freshVar 0, ft1)]
  rules := {r | r ∈ maintenanceRules P₁}

/-! ### Decidable facts about `d₁`'s row list -/

theorem fnList₁ : ∀ r ∈ rows₁, r.fn = ufName ∨ r.fn = viewF ∨ r.fn = "f" ∨ r.fn = termF := by
  decide

theorem outLen₁ : ∀ r ∈ rows₁, r.out.length = 1 := by decide

theorem fnKey₁ : ∀ r₁ ∈ rows₁, ∀ r₂ ∈ rows₁, r₁.fn = r₂.fn → r₁.args = r₂.args →
    r₁.out = r₂.out := by decide

theorem loops₁ : ∀ r ∈ rows₁, (r.fn = ufName ∨ r.fn = viewF) →
    ∀ p ∈ r.out, Row.mk ufName [p] [p] ∈ rows₁ := by decide

theorem rowTerms₁ : ∀ r ∈ rows₁, (∀ t ∈ r.args, t ∈ terms₁) ∧ (∀ t ∈ r.out, t ∈ terms₁) := by
  decide

/-! ### Subterms and constructor rows of `d₁`'s terms -/

theorem isSubterm_lit {s : Term} {l : Lit} (h : Term.IsSubterm s (.lit l)) : s = .lit l := by
  cases h with | refl => rfl

theorem isSubterm_app1 {s a : Term} {f : FnName} (h : Term.IsSubterm s (.app f [a])) :
    s = .app f [a] ∨ Term.IsSubterm s a := by
  cases h with
  | refl => exact Or.inl rfl
  | arg hm hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; exact Or.inr (hm ▸ hs)

theorem sub₁ : ∀ t ∈ terms₁, t.subterms ⊆ d₁.terms ∧ t.ctorRows ⊆ d₁.rows := by
  intro t ht
  simp only [terms₁, List.mem_cons, List.not_mem_nil, or_false] at ht
  constructor
  · rcases ht with rfl | rfl | rfl | rfl
    · intro s hs; rw [isSubterm_lit hs]; show _ ∈ terms₁; decide
    · intro s hs; rw [isSubterm_lit hs]; show _ ∈ terms₁; decide
    · intro s hs; rw [isSubterm_lit hs]; show _ ∈ terms₁; decide
    · intro s hs
      rcases isSubterm_app1 hs with rfl | hs'
      · show _ ∈ terms₁; decide
      · rw [isSubterm_lit hs']; show _ ∈ terms₁; decide
  · rcases ht with rfl | rfl | rfl | rfl
    · rintro ⟨g, args, out⟩ ⟨h1, h2⟩; exact absurd (isSubterm_lit h2) (by simp)
    · rintro ⟨g, args, out⟩ ⟨h1, h2⟩; exact absurd (isSubterm_lit h2) (by simp)
    · rintro ⟨g, args, out⟩ ⟨h1, h2⟩; exact absurd (isSubterm_lit h2) (by simp)
    · rintro ⟨g, args, out⟩ ⟨h1, h2⟩
      simp only at h1 h2
      rcases isSubterm_app1 h2 with heq | hs'
      · injection heq with e1 e2
        subst e1; subst e2; subst h1
        show _ ∈ rows₁; decide
      · exact absurd (isSubterm_lit hs') (by simp)

/-! ### `d₁` satisfies the `MCong`-is-equality hypotheses -/

theorem eqs₁ : d₁.eqs = ∅ := rfl

theorem ctorUnion₁ : ∀ r ∈ d₁.rows, d₁.sig.mergeOf r.fn = MergeSpec.union →
    r.out = [.app r.fn r.args] := by
  intro r hr
  have hr : r ∈ rows₁ := hr
  simp only [rows₁, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> intro h
  · rfl
  all_goals exact absurd h (by intro hh; exact MergeSpec.noConfusion hh)

/-! ### Conjunct 2: `d₁` is `MergeSaturated`

Every collision in `d₁` is a self-collision, and the shared `:merge` body on a
self-collision re-derives rows `d₁` already holds — including the `@UF` self-loop, which
is exactly why the loops are in `rows₁`. -/
theorem mergeSaturated₁ : MergeSaturated d₁ := by
  intro db' hstep
  cases hstep with
  | @collide dmid f as bs a b vs body res ha hb hl hm hact hres =>
    have hab : as = bs := mcongList_eq eqs₁ ctorUnion₁ hl
    subst hab
    have haL : Row.mk f as a ∈ rows₁ := ha
    have hbL : Row.mk f as b ∈ rows₁ := hb
    have hout : a = b := fnKey₁ _ haL _ hbL rfl rfl
    subst hout
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (outLen₁ _ haL)
    have hfv : f = ufName ∨ f = viewF := by
      have hfl : f = ufName ∨ f = viewF ∨ f = "f" ∨ f = termF := fnList₁ _ haL
      rcases hfl with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · subst h
        have hu : MergeSpec.union = MergeSpec.merge body res := hm
        exact absurd hu (fun hh => MergeSpec.noConfusion hh)
      · subst h
        have hn : MergeSpec.noMerge = MergeSpec.merge body res := hm
        exact absurd hn (fun hh => MergeSpec.noConfusion hh)
    have hbody : body = mergeBody ∧ res = mergeResult := by
      rcases hfv with h | h <;> subst h <;>
        (have hm' : MergeSpec.merge mergeBody mergeResult = MergeSpec.merge body res := hm
         injection hm' with e1 e2
         exact ⟨e1.symm, e2.symm⟩)
    obtain ⟨rfl, rfl⟩ := hbody
    have hpT : p ∈ terms₁ := (rowTerms₁ _ haL).2 p (by simp)
    have hasT : ∀ t ∈ as, t ∈ terms₁ := (rowTerms₁ _ haL).1
    have hloop : Row.mk ufName [p] [p] ∈ rows₁ := loops₁ _ haL hfv p (by simp)
    rw [mergeBody, evalActions_cons] at hact
    cases hstep : evalAction { d₁ with env := mergeEnv [p] [p] }
        (.set ufName [maxE (.var "old") (.var "new")] [minE (.var "old") (.var "new")]) with
    | none => rw [hstep] at hact; simp at hact
    | some dm =>
      rw [hstep, Option.bind_some, evalActions_nil, Option.some.injEq] at hact
      subst hact
      simp only [evalAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hstep
      obtain ⟨ua, hargs, uv, houts, rfl⟩ := hstep
      obtain ⟨u, rfl, hu⟩ := mevalList_one hargs
      obtain ⟨w, rfl, hw⟩ := mevalList_one houts
      obtain ⟨v, rfl, hv⟩ := mevalList_one (by rw [mergeResult] at hres; exact hres)
      rw [meval_max_self hu, meval_min_self hw, meval_min_self hv]
      have hA : ({ d₁ with env := mergeEnv [p] [p] } : Database).addRow ufName [p] [p]
          = { d₁ with env := mergeEnv [p] [p] } := by
        refine addRow_eq_self ?_ hloop
        intro t ht
        have ht' : t = p := by simpa using ht
        rw [ht']
        exact sub₁ p hpT
      have hB : ({ d₁ with env := mergeEnv [p] [p] } : Database).addRow f as [p]
          = { d₁ with env := mergeEnv [p] [p] } := by
        refine addRow_eq_self ?_ ha
        intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact sub₁ t (hasT t h)
        · have ht' : t = p := by simpa using h
          rw [ht']
          exact sub₁ p hpT
      rw [hA, hB]

/-! ### Conjunct 1 at `d₁`: the row set is closed under all three maintenance rules

Each of the three rules concludes one row, determined by the two rows its body matched.
Since `MCong d₁` is syntactic equality (`mcong_eq` + `eqs₁`/`ctorUnion₁`), a firing is
exactly a pair of rows of the right two functions joined on a column, so these three
decidable closure facts are the whole finite content of `Rebuilt`'s first conjunct at
`d₁`. -/

/-- `pathCompressRule`: `@UF a ↦ b`, `@UF b ↦ c` ⊢ `@UF a ↦ c`. -/
theorem pathCompress_closed₁ : ∀ r₁ ∈ rows₁, ∀ r₂ ∈ rows₁,
    r₁.fn = ufName → r₂.fn = ufName → r₁.out = r₂.args →
    Row.mk ufName r₁.args r₂.out ∈ rows₁ := by decide

/-- The e-class rebuild rule: `@fView cs ↦ e`, `@UF e ↦ x` ⊢ `@fView cs ↦ x`. -/
theorem eclass_closed₁ : ∀ rv ∈ rows₁, ∀ ru ∈ rows₁,
    rv.fn = viewF → ru.fn = ufName → rv.out = ru.args →
    Row.mk viewF rv.args ru.out ∈ rows₁ := by decide

/-- The column-0 rebuild rule: `@fView [c] ↦ e`, `@UF c ↦ x` ⊢ `@fView [x] ↦ e`. -/
theorem col_closed₁ : ∀ rv ∈ rows₁, ∀ ru ∈ rows₁,
    rv.fn = viewF → ru.fn = ufName → rv.args = ru.args →
    Row.mk viewF ru.out rv.out ∈ rows₁ := by decide

/-- The same closure fails at `d₀` — which is `not_rebuilt₀` again, decidably. -/
theorem col_not_closed₀ : ¬ (∀ rv ∈ rows₀, ∀ ru ∈ rows₀,
    rv.fn = viewF → ru.fn = ufName → rv.args = ru.args →
    Row.mk viewF ru.out rv.out ∈ rows₀) := by decide

/-! ### Plumbing for inverting a query substitution -/

theorem lookup_append_of_some {v : Var} {σ τ : Env} {t : Term} (h : Env.lookup v σ = some t) :
    Env.lookup v (σ ++ τ) = some t := by
  induction σ with
  | nil => simp [Env.lookup] at h
  | cons b rest ih =>
    obtain ⟨w, u⟩ := b
    simp only [Env.lookup, List.cons_append] at h ⊢
    by_cases hvw : v = w
    · simp only [if_pos hvw] at h ⊢; exact h
    · simp only [if_neg hvw] at h ⊢; exact ih h

theorem lookup_eq_none_of_dom {v : Var} {σ : Env} (h : v ∉ Env.dom σ) :
    Env.lookup v σ = none := by
  induction σ with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨w, u⟩ := b
    simp only [Env.dom, List.map_cons, List.mem_cons, not_or] at h
    simp only [Env.lookup, if_neg h.1]
    exact ih (by simpa [Env.dom] using h.2)

theorem mem_of_lookup {v : Var} {σ : Env} {t : Term} (h : Env.lookup v σ = some t) :
    (v, t) ∈ σ := by
  induction σ with
  | nil => simp [Env.lookup] at h
  | cons b rest ih =>
    obtain ⟨w, u⟩ := b
    simp only [Env.lookup] at h
    by_cases hvw : v = w
    · simp only [if_pos hvw, Option.some.injEq] at h
      subst hvw; subst h; exact List.Mem.head _
    · simp only [if_neg hvw] at h
      exact List.Mem.tail _ (ih h)

/-- The extended database a `MValidSubst.eq` premise talks about still has
`MCong = (· = ·)`. -/
theorem ctorUnion_addTerm {db : Database} {t : Term}
    (h : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union → r.out = [.app r.fn r.args]) :
    ∀ r ∈ (db.addTerm t).rows, (db.addTerm t).sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] := by
  intro r hr hu
  rcases hr with hr | hr
  · exact h r hr hu
  · exact hr.1

/-- `ctorUnion_addTerm` over a list: the extension a `MValidSubst.values` premise reads
its congruence in. -/
theorem ctorUnion_addTerms {db : Database} {ts : List Term}
    (h : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union → r.out = [.app r.fn r.args]) :
    ∀ r ∈ (db.addTerms ts).rows, (db.addTerms ts).sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (ctorUnion_addTerm h)

/-- Inverting `MValidSubst` on the one pattern shape every maintenance rule uses: a
one-column row atom at a variable key.

Shorter than it was, because a read is now the atom itself rather than an `.eq` whose
right-hand side read a row, and the `Prim.ofName`/`mergeOf` side conditions that ruled
out the other evaluation rules are gone.

Both congruence premises are read in the database extended with the atom's operands, so
`mcong_eq`'s two side conditions are discharged there: `addTerms` touches neither `eqs`
nor any `.union` function's rows beyond the constructor rows it adds. -/
theorem invert_eq_pattern {d : Database} (heq : d.eqs = ∅)
    (hrows : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union → r.out = [.app r.fn r.args])
    {G : FnName} {V W : Var} {σ : Env}
    (h : MValidSubst d (.values [.var V] G [.var W]) σ) :
    (Env.dom σ).Perm (Expr.freeVarsList [Expr.var V] d.env ∪
        Expr.freeVarsList [Expr.var W] d.env) ∧
      ∃ tv tw, Env.lookup V (d.env ++ σ) = some tv ∧
        Env.lookup W (d.env ++ σ) = some tw ∧ Row.mk G [tw] [tv] ∈ d.rows := by
  cases h with
  | values hve hvs has hts hus hrow =>
    refine ⟨hve.1, ?_⟩
    obtain ⟨tv, rfl, hv⟩ := mevalList_one hvs
    obtain ⟨tw, rfl, hw⟩ := mevalList_one has
    have heq' : ((d.addTerms [tw]).addTerms [tv]).eqs = ∅ := by
      rw [addTerms_eqs, addTerms_eqs]; exact heq
    have hrows' := ctorUnion_addTerms (ts := [tv]) (ctorUnion_addTerms (ts := [tw]) hrows)
    have hb : [tw] = _ := mcongList_eq heq' hrows' hts
    have hw' : [tv] = _ := mcongList_eq heq' hrows' hus
    subst hb; subst hw'
    exact ⟨tv, tw, meval_var' hv, meval_var' hw, hrow⟩

theorem lookup_none_of_perm {v : Var} {σ : Env} {l : List Var}
    (hp : (Env.dom σ).Perm l) (h : v ∉ l) : Env.lookup v σ = none :=
  lookup_eq_none_of_dom fun hm => h (hp.mem_iff.mp hm)

theorem lookup3_left {v : Var} {σa σb : Env} {t : Term}
    (hd : Env.lookup v d₁.env = none) (h : Env.lookup v σa = some t) :
    Env.lookup v (d₁.env ++ (σa ++ σb)) = some t := by
  rw [lookup_append_of_none hd]; exact lookup_append_of_some h

theorem lookup3_right {v : Var} {σa σb : Env} {t : Term}
    (hd : Env.lookup v d₁.env = none) (ha : Env.lookup v σa = none)
    (h : Env.lookup v σb = some t) :
    Env.lookup v (d₁.env ++ (σa ++ σb)) = some t := by
  rw [lookup_append_of_none hd, lookup_append_of_none ha]; exact h

theorem noAtVar₁ (v : Var) (h : v ≠ freshVar 0) : Env.lookup v d₁.env = none := by
  simp [d₁, Env.lookup, h]

/-- Every firing of a maintenance rule at `d₁`, unpacked.

All three maintenance rules have the same shape: two row atoms reading a one-column table
at a variable key, and a head that `set`s a one-column row from two variables. -/
theorem two_pattern_firing {V₁ W₁ V₂ W₂ A B : Var} {G₁ G₂ F : FnName} {d' : Database}
    (hfv1 : Expr.freeVarsList [Expr.var V₁] d₁.env ∪
      Expr.freeVarsList [Expr.var W₁] d₁.env = [V₁, W₁])
    (hfv2 : Expr.freeVarsList [Expr.var V₂] d₁.env ∪
      Expr.freeVarsList [Expr.var W₂] d₁.env = [V₂, W₂])
    (hd : d' ∈ RuleResults d₁ ⟨[.values [.var V₁] G₁ [.var W₁],
                                .values [.var V₂] G₂ [.var W₂]],
                               [.set F [.var A] [.var B]]⟩) :
    ∃ (σa σb : Env) (tv1 tw1 tv2 tw2 ta tb : Term),
      (Env.dom σa).Perm [V₁, W₁] ∧ (Env.dom σb).Perm [V₂, W₂] ∧
      Env.lookup V₁ (d₁.env ++ σa) = some tv1 ∧ Env.lookup W₁ (d₁.env ++ σa) = some tw1 ∧
      Env.lookup V₂ (d₁.env ++ σb) = some tv2 ∧ Env.lookup W₂ (d₁.env ++ σb) = some tw2 ∧
      Row.mk G₁ [tw1] [tv1] ∈ rows₁ ∧ Row.mk G₂ [tw2] [tv2] ∈ rows₁ ∧
      (∀ v t u, Env.lookup v σa = some t → Env.lookup v σb = some u → t = u) ∧
      Env.lookup A (d₁.env ++ (σa ++ σb)) = some ta ∧
      Env.lookup B (d₁.env ++ (σa ++ σb)) = some tb ∧
      d' = { (({ d₁ with env := d₁.env ++ (σa ++ σb) }).addRow F [ta] [tb]) with
               env := d₁.env, rules := d₁.rules } := by
  obtain ⟨σ, hq, hloc⟩ := hd
  obtain ⟨dd, hact, rfl⟩ := evalLocalActions_eq_some hloc
  obtain ⟨σs, hall, hun⟩ := hq
  cases hall with
  | cons s1 rest =>
    cases rest with
    | cons s2 rest2 =>
      cases rest2
      cases hun with
      | step hu hrest =>
        cases hrest with
        | single =>
          obtain ⟨hcompat, rfl⟩ := hu
          obtain ⟨hd1, tv1, tw1, h1v, h1w, hr1⟩ :=
            invert_eq_pattern eqs₁ ctorUnion₁ s1
          obtain ⟨hd2, tv2, tw2, h2v, h2w, hr2⟩ :=
            invert_eq_pattern eqs₁ ctorUnion₁ s2
          rw [hfv1] at hd1
          rw [hfv2] at hd2
          rw [evalActions_cons] at hact
          cases hstep : evalAction _ (Action.set F [Expr.var A] [Expr.var B]) with
          | none => rw [hstep] at hact; simp at hact
          | some dm =>
            rw [hstep, Option.bind_some, evalActions_nil, Option.some.injEq] at hact
            subst hact
            simp only [evalAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hstep
            obtain ⟨as, hargs, vs, houts, rfl⟩ := hstep
            obtain ⟨ta, rfl, hA⟩ := mevalList_one hargs
            obtain ⟨tb, rfl, hB⟩ := mevalList_one houts
            exact ⟨_, _, tv1, tw1, tv2, tw2, ta, tb, hd1, hd2, h1v, h1w, h2v, h2w,
              hr1, hr2,
              fun v t u hvt hvu => hcompat (v, t) (mem_of_lookup hvt) u hvu,
              meval_var' hA, meval_var' hB, rfl⟩

/-! ### Conjunct 1 at `d₁` -/

/-- Firing any of the three maintenance rules at `d₁` reproduces `d₁`. -/
theorem contained_of_firing {F : FnName} {ta tb : Term} {E : Env}
    (hrow : Row.mk F [ta] [tb] ∈ rows₁) :
    Database.Contained ({ (({ d₁ with env := E }).addRow F [ta] [tb]) with
        env := d₁.env, rules := d₁.rules } : Database) d₁ := by
  have hta : ta ∈ terms₁ := (rowTerms₁ _ hrow).1 ta (by simp)
  have htb : tb ∈ terms₁ := (rowTerms₁ _ hrow).2 tb (by simp)
  have hself : ({ d₁ with env := E } : Database).addRow F [ta] [tb] = { d₁ with env := E } := by
    refine addRow_eq_self ?_ hrow
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · have : t = ta := by simpa using h
      rw [this]; exact sub₁ ta hta
    · have : t = tb := by simpa using h
      rw [this]; exact sub₁ tb htb
  rw [hself]
  exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem rebuilt_conj1 : ∀ r ∈ maintenanceRules P₁, ∀ d' ∈ RuleResults d₁ r,
    Database.Contained d' d₁ := by
  have fv : ∀ (V W : Var), Env.lookup V d₁.env = none →
      Env.lookup W d₁.env = none →
      Expr.freeVarsList [Expr.var V] d₁.env ∪ Expr.freeVarsList [Expr.var W] d₁.env =
        List.insert V [W] := by
    intro V W hV hW
    show (Expr.freeVars (.var V) d₁.env ∪ Expr.freeVarsList [] d₁.env) ∪
      (Expr.freeVars (.var W) d₁.env ∪ Expr.freeVarsList [] d₁.env) = _
    rw [freeVars_var_of_none hV, freeVars_var_of_none hW]
    rfl
  intro r hr d' hd'
  rw [maintenance₁] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  -- path compression: `@UF a ↦ b`, `@UF b ↦ c` ⊢ `@UF a ↦ c`
  · obtain ⟨σa, σb, tv1, tw1, tv2, tw2, ta, tb, hda, hdb, h1v, h1w, h2v, h2w,
      hr1, hr2, hcom, hAl, hBl, rfl⟩ :=
      two_pattern_firing (V₁ := "@b") (W₁ := "@a") (V₂ := "@c") (W₂ := "@b")
        (fv _ _ (by rfl) (by rfl)) (fv _ _ (by rfl) (by rfl)) hd'
    rw [lookup_append_of_none (by rfl : Env.lookup "@b" d₁.env = none)] at h1v
    rw [lookup_append_of_none (by rfl : Env.lookup "@a" d₁.env = none)] at h1w
    rw [lookup_append_of_none (by rfl : Env.lookup "@c" d₁.env = none)] at h2v
    rw [lookup_append_of_none (by rfl : Env.lookup "@b" d₁.env = none)] at h2w
    have hta : ta = tw1 := by
      rw [lookup3_left (by rfl) h1w] at hAl; exact (Option.some.injEq _ _ ▸ hAl).symm
    have htb : tb = tv2 := by
      rw [lookup3_right (by rfl) (lookup_none_of_perm hda (by decide)) h2v] at hBl
      exact (Option.some.injEq _ _ ▸ hBl).symm
    have hlink : tv1 = tw2 := hcom "@b" tv1 tw2 h1v h2w
    subst hta; subst htb; subst hlink
    exact contained_of_firing (pathCompress_closed₁ _ hr1 _ hr2 rfl rfl rfl)
  -- e-class rebuild: `@fView cs ↦ e`, `@UF e ↦ x` ⊢ `@fView cs ↦ x`
  · obtain ⟨σa, σb, tv1, tw1, tv2, tw2, ta, tb, hda, hdb, h1v, h1w, h2v, h2w,
      hr1, hr2, hcom, hAl, hBl, rfl⟩ :=
      two_pattern_firing (V₁ := "@e") (W₁ := "@c0") (V₂ := "@x") (W₂ := "@e")
        (fv _ _ (by rfl) (by rfl)) (fv _ _ (by rfl) (by rfl)) hd'
    rw [lookup_append_of_none (by rfl : Env.lookup "@e" d₁.env = none)] at h1v
    rw [lookup_append_of_none (by rfl : Env.lookup "@c0" d₁.env = none)] at h1w
    rw [lookup_append_of_none (by rfl : Env.lookup "@x" d₁.env = none)] at h2v
    rw [lookup_append_of_none (by rfl : Env.lookup "@e" d₁.env = none)] at h2w
    have hta : ta = tw1 := by
      rw [lookup3_left (by rfl) h1w] at hAl; exact (Option.some.injEq _ _ ▸ hAl).symm
    have htb : tb = tv2 := by
      rw [lookup3_right (by rfl) (lookup_none_of_perm hda (by decide)) h2v] at hBl
      exact (Option.some.injEq _ _ ▸ hBl).symm
    have hlink : tv1 = tw2 := hcom "@e" tv1 tw2 h1v h2w
    subst hta; subst htb; subst hlink
    exact contained_of_firing (eclass_closed₁ _ hr1 _ hr2 rfl rfl rfl)
  -- column rebuild: `@fView [c] ↦ e`, `@UF c ↦ x` ⊢ `@fView [x] ↦ e`
  · obtain ⟨σa, σb, tv1, tw1, tv2, tw2, ta, tb, hda, hdb, h1v, h1w, h2v, h2w,
      hr1, hr2, hcom, hAl, hBl, rfl⟩ :=
      two_pattern_firing (V₁ := "@e") (W₁ := "@c0") (V₂ := "@x") (W₂ := "@c0")
        (fv _ _ (by rfl) (by rfl)) (fv _ _ (by rfl) (by rfl)) hd'
    rw [lookup_append_of_none (by rfl : Env.lookup "@e" d₁.env = none)] at h1v
    rw [lookup_append_of_none (by rfl : Env.lookup "@c0" d₁.env = none)] at h1w
    rw [lookup_append_of_none (by rfl : Env.lookup "@x" d₁.env = none)] at h2v
    rw [lookup_append_of_none (by rfl : Env.lookup "@c0" d₁.env = none)] at h2w
    have hta : ta = tv2 := by
      rw [lookup3_right (by rfl) (lookup_none_of_perm hda (by decide)) h2v] at hAl
      exact (Option.some.injEq _ _ ▸ hAl).symm
    have htb : tb = tv1 := by
      rw [lookup3_left (by rfl) h1v] at hBl; exact (Option.some.injEq _ _ ▸ hBl).symm
    have hlink : tw1 = tw2 := hcom "@c0" tw1 tw2 h1w h2w
    subst hta; subst htb; subst hlink
    exact contained_of_firing (col_closed₁ _ hr1 _ hr2 rfl rfl rfl)

/-- **`Rebuilt` is satisfiable.** `P₁` unions the two distinct terms `1` and `2`. -/
theorem rebuilt₁ : Rebuilt P₁ d₁ := ⟨rebuilt_conj1, mergeSaturated₁⟩

/-! ### The source side is untouched by merge phases

`CmdStep.action` now runs a `MergeClosure` after every command. On the *source* side of
`encode` that leg is always the identity: `EncodeDomain` makes every function a
constructor, and `MergeStep` needs a `.merge` function. So appending `(run)`s to a
rule-free source program is a genuine no-op, and the "append to both sides" caveat in
`encode_complete`'s docstring only bites when `P` has rules. -/

theorem mergeOf_union_of_allConstructors {sig : Signature} (h : sig.AllConstructors)
    (f : FnName) : sig.mergeOf f = MergeSpec.union := by
  unfold Signature.mergeOf
  cases hf : sig f with
  | none => rfl
  | some dd => exact h f dd hf

theorem no_mergeStep {d d' : Database} (h : d.sig.AllConstructors) (hs : MergeStep d d') :
    False := by
  cases hs with
  | collide _ _ _ hm _ _ =>
    rw [mergeOf_union_of_allConstructors h] at hm
    exact MergeSpec.noConfusion hm

theorem mergeClosure_eq_of_allConstructors {d d' : Database} (h : d.sig.AllConstructors)
    (hc : MergeClosure d d') : d' = d := by
  induction hc with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    exact (no_mergeStep h hstep).elim

/-! ### Axioms -/


end RebuiltVacuity
end Egglog
