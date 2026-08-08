import EgglogSemantics.Spec.Merge
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Interp

/-!
# What M9 has to prove

`MERGE.md` says which theorem buys what. Six are still unproved; the rest are proved.

The load-bearing one is `mcong_iff_cong`: where the rows are the constructor rows
(`Database.CtorRows`) and the signature is all constructors, the generalized relation is
exactly M2's `Cong`. That is what makes replacing `Cong` by `MCong` a refactor rather
than a rewrite — without it every M2–M8 theorem would have to be reproved rather than
transported.

Four statements needed repair, and the repairs are the interesting output:

* `Expr.MEval_of_eval`'s `∀ f, Prim.ofName f = none` is **unsatisfiable**
  (`not_forall_ofName_eq_none`), so it is vacuous. `Expr.NoPrim` and
  `Expr.MEval_of_eval'` are the version that is not, and `Expr.eval_of_MEval` is the
  converse M11 wants — it needs no `CtorRows`.
* `MCong.mono`, `MCongList.mono` and `Database.Out.mono` are **false** as stated:
  `Contained` ignores `sig` and `fd` fires only at `.union`. See
  `mcong_mono_needs_sig`. They carry `d₁.sig = d₂.sig`.
* `MergeStep.self_id` and `MergeStep.wf` need the row half of well-formedness
  (`Database.RowsWF`), which `Database.WF` deliberately omits, and `self_id`
  additionally needs `ctorRowsOf db.terms ⊆ db.rows`.
* `FDatabase.closureF_ok`'s `←` direction is false without "every application the
  database holds is a `.union` function's".

`MergeStep.diamond_of_join` and `RunStep.unique_of_confluent` are the two `MERGE.md`
flags as guesses, and both have hypotheses that cannot be used; their docstrings say
what replaces them.
-/

namespace Egglog
/-! ### Constructor-determined rows

`Database.toM` is gone: `Database` *is* the M9 database now, so the embedding it named
is the identity and `CtorRows` is what the theorem below quantifies over instead. -/
theorem Database.mem_rows_iff {db : Database} (h : db.CtorRows) {f : FnName}
    {as vs : List Term} :
    Row.mk f as vs ∈ db.rows ↔ vs = [.app f as] ∧ Term.app f as ∈ db.terms := by
  rw [h]; exact Iff.rfl

/-! ### The generalized relation is the old one

Two directions, two hypotheses. `MCong → Cong` needs only that the rows are constructor
rows, because a constructor row is one whatever the signature says. `Cong → MCong` also
needs `AllConstructors`, which is what licenses `fd`. -/
mutual

/-- Every functional-dependency derivation over constructor rows is an M2 derivation.

`fd` is the only interesting case: its two rows are constructor rows, so their outputs
are `.app f as` and `.app f bs` and both applications are in `db.terms` — the two
premises `Cong.congr` wants. -/
theorem MCong.toCong {db : Database} (hrows : db.CtorRows) {a b : Term}
    (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong hrows h)
  | .trans h₁ h₂ => exact .trans (MCong.toCong hrows h₁) (MCong.toCong hrows h₂)
  | .fd ha hb _ hl hxy =>
    obtain ⟨rfl, hma⟩ := (Database.mem_rows_iff hrows).mp ha
    obtain ⟨rfl, hmb⟩ := (Database.mem_rows_iff hrows).mp hb
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList hrows hl)

theorem MCongList.toCongList {db : Database} (hrows : db.CtorRows) {as bs : List Term}
    (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.toCong hrows hab) (MCongList.toCongList hrows hl)

end

mutual

/-- Every M2 derivation is a functional-dependency derivation.

`congr` is the only interesting case, and its two membership premises are exactly what is
needed: `RowsComplete` turns each into a row `fd` can use, and `CtorTerms` says the
function they are applications of is a constructor, which is what lets `fd` fire.

Stated over `CtorTerms`/`RowsComplete` rather than `AllConstructors`/`CtorRows` because
those two **survive merging** — they constrain `terms` and the constructor rows, neither
of which a merge touches (`FDatabase.mergeRound_confined`) — whereas `CtorRows` fails at
the first `:merge` declaration. That is what lets the interpreter's `closureF`, which
computes `Cong`, be read as `MCong` in a database that has merge functions in it, and it
is the reason the refinement chain below can exist at all. -/
theorem Cong.toMCong' {db : Database} (hterms : db.CtorTerms) (hrows : db.RowsComplete)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong' hterms hrows h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong' hterms hrows h₁) (Cong.toMCong' hterms hrows h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs])
      (hrows ⟨rfl, hma⟩) (hrows ⟨rfl, hmb⟩) (hterms f as hma)
      (CongList.toMCongList' hterms hrows hl) (by simp)

theorem CongList.toMCongList' {db : Database} (hterms : db.CtorTerms)
    (hrows : db.RowsComplete) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong' hterms hrows hab) (CongList.toMCongList' hterms hrows hl)

end

/-- `AllConstructors` gives `CtorTerms`: `mergeOf` defaults an undeclared name to `.union`
and `AllConstructors` says every declared one is `.union` too. -/
theorem Signature.AllConstructors.ctorTerms {db : Database}
    (hsig : db.sig.AllConstructors) : db.CtorTerms :=
  fun f _ _ => Signature.mergeOf_eq_union hsig f

/-- `CtorRows` gives `RowsComplete`: it is the equality, this is one inclusion of it.

Written with `▸` rather than `h.ge`: the latter goes through `Set`'s order instances and
puts `Classical.choice` into the axiom set of everything downstream, including
`mcong_iff_cong`, which is otherwise `propext` alone. -/
theorem Database.CtorRows.rowsComplete {db : Database} (h : db.CtorRows) :
    db.RowsComplete := fun _ hr => h.symm ▸ hr

theorem Cong.toMCong {db : Database} (hsig : db.sig.AllConstructors) (hrows : db.CtorRows)
    {a b : Term} (h : Cong db a b) : MCong db a b :=
  Cong.toMCong' hsig.ctorTerms hrows.rowsComplete h

theorem CongList.toMCongList {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {as bs : List Term} (h : CongList db as bs) :
    MCongList db as bs :=
  CongList.toMCongList' hsig.ctorTerms hrows.rowsComplete h

/-- **The compatibility theorem.** Where the rows are the constructor rows and every
function is a constructor, the functional dependency *is* congruence.

This is what `PLAN.md` M9 asks for, and the reason `MCong` has no `congr` constructor:
congruence is not lost, it is `fd` read at constructor rows.

It replaces `mcong_toM_iff`, which quantified over the embedding `Database.toM` of an
M2 database into a separate `MDatabase`. Now that the two states are one structure that
embedding is the identity, so the *hypothesis* `CtorRows` carries what the embedding
used to: it says the state is in the constructor-only fragment. The theorem's content is
unchanged and its proof is the same four `match` cases. -/
theorem mcong_iff_cong {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {a b : Term} : MCong db a b ↔ Cong db a b :=
  ⟨MCong.toCong hrows, Cong.toMCong hsig hrows⟩

/-- **The compatibility theorem, at a state a program can reach.** A program that declares
only constructors and never `set`s one runs to a database where the two relations agree.

`Proofs/Step.lean`'s `ProgramStep.ctorState` supplies both hypotheses; this is the
composition, which lives here because that is where `mcong_iff_cong` is. -/
theorem ProgramStep.mcong_iff_cong {p : Program} {db : Database}
    (hstep : ProgramStep Database.empty p db) (hdecl : p.CtorDecls)
    (hlegal : p.SetLegal Database.empty.sig) {a b : Term} : MCong db a b ↔ Cong db a b :=
  let hc := ProgramStep.ctorState Database.CtorState.empty hdecl hlegal hstep
  Egglog.mcong_iff_cong hc.sig hc.rows

/-- Congruence, recovered as a derived rule rather than a constructor. -/
theorem MCong.congr {db : Database} {f : FnName} {as bs : List Term}
    (ha : Row.mk f as [.app f as] ∈ db.rows) (hb : Row.mk f bs [.app f bs] ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.union) (hl : MCongList db as bs) :
    MCong db (.app f as) (.app f bs) :=
  .fd ha hb hsig hl (by simp)

/-! ### The two evaluators agree

`Expr.eval` (M0–M8, a function) and `Expr.MEval` (M9, a relation) coexist until M12.
These are the guard against their drifting apart.

`NoPrim` is what `hprim` below *should* say. As stated, `∀ f, Prim.ofName f = none` is
false — `Prim.ofName "ordering-min" = some .orderingMin` — so `MEval_of_eval` is
vacuous. It is proved honestly all the same (the induction never needs `hprim` at a name
other than the one in front of it), and `MEval_of_eval'` is the same statement with the
hypothesis restricted to the names `e` actually mentions, which is satisfiable.

`Expr.NoPrim` and `Expr.NoPrimList` live in `Spec/Merge.lean` beside `Prim.ofName`. -/
@[simp] theorem Expr.noPrim_app {f : FnName} {args : List Expr} :
    Expr.NoPrim (.app f args) ↔ Prim.ofName f = none ∧ Expr.NoPrimList args := Iff.rfl

@[simp] theorem Expr.noPrimList_cons {e : Expr} {es : List Expr} :
    Expr.NoPrimList (e :: es) ↔ Expr.NoPrim e ∧ Expr.NoPrimList es := Iff.rfl

/-- **`Expr.MEval_of_eval`'s hypothesis is unsatisfiable**, so that theorem is vacuous
however it is proved. `Expr.MEval_of_eval'` is the same statement with the quantifier
cut down to the names `e` mentions, which is satisfiable. -/
theorem not_forall_ofName_eq_none : ¬ ∀ f : FnName, Prim.ofName f = none := by
  intro h
  have hmin := h "ordering-min"
  simp [Prim.ofName] at hmin

mutual

/-- The connecting theorem between the two evaluators, which coexist until stage 3
(`PLAN.md`, M12). `Expr.eval` is the M0–M8 function; `Expr.MEval` is M9's relation. On a
constructor-only signature the first refines the second, which is the guard against the
two drifting apart while both exist.

**The hypothesis as stated is unsatisfiable**, so this theorem is vacuous; see
`Expr.MEval_of_eval'` for the version that is not. The proof below is the real one —
only the quantifier on `hprim` is too strong. -/
theorem Expr.MEval_of_eval {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    {e : Expr} {t : Term} (hprim : ∀ f, Prim.ofName f = none) (h : e.eval σ = some t) :
    Expr.MEval db σ e t := by
  match e, h with
  | .lit l, h => rw [Expr.eval_lit, Option.some.injEq] at h; exact h ▸ .lit
  | .var v, h => exact .var h
  | .app f args, h =>
    rw [Expr.eval_app, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    exact .ctor (hprim f) (Signature.mergeOf_eq_union hsig f)
      (Expr.MEvalList_of_evalList hsig hprim hts)

theorem Expr.MEvalList_of_evalList {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} {es : List Expr} {ts : List Term} (hprim : ∀ f, Prim.ofName f = none)
    (h : Expr.evalList es σ = some ts) : Expr.MEvalList db σ es ts := by
  match es, h with
  | [], h => rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ .nil
  | e :: es, h =>
    rw [Expr.evalList_cons] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .cons (Expr.MEval_of_eval hsig hprim ht)
      (Expr.MEvalList_of_evalList hsig hprim hus)

end

mutual

/-- `Expr.MEval_of_eval` with a satisfiable hypothesis: only the names `e` mentions have
to be non-primitive. -/
theorem Expr.MEval_of_eval' {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    (e : Expr) {t : Term} : e.NoPrim → e.eval σ = some t → Expr.MEval db σ e t := by
  match e with
  | .lit l => intro _ h; rw [Expr.eval_lit, Option.some.injEq] at h; exact h ▸ .lit
  | .var v => intro _ h; exact .var h
  | .app f args =>
    intro hp h
    rw [Expr.eval_app, Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    exact .ctor hp.1 (Signature.mergeOf_eq_union hsig f)
      (Expr.MEvalList_of_evalList' hsig args hp.2 hts)

theorem Expr.MEvalList_of_evalList' {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} (es : List Expr) {ts : List Term} :
    Expr.NoPrimList es → Expr.evalList es σ = some ts → Expr.MEvalList db σ es ts := by
  match es with
  | [] => intro _ h; rw [Expr.evalList_nil, Option.some.injEq] at h; exact h ▸ .nil
  | e :: es =>
    intro hp h
    rw [Expr.evalList_cons] at h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .cons (Expr.MEval_of_eval' hsig e hp.1 ht)
      (Expr.MEvalList_of_evalList' hsig es hp.2 hus)

end

mutual

/-- **The converse, which is what M11 needs.** On a constructor-only signature and a
primitive-free expression, `MEval` is no more than `eval`: `ctor` is the only rule that can
fire, because `mergeOf` is always `.union` and no name resolves as a primitive. This is
what transports a fact about the relational side back to the function side.

`AllConstructors` is still needed and `db.CtorRows` still is not. The two evaluators
differ on exactly two things — a primitive name, and a non-constructor application, which
`MEval` (having no `lookup`) leaves stuck where `eval` builds a term. -/
theorem Expr.eval_of_MEval {db : Database} (hsig : db.sig.AllConstructors) {σ : Env}
    {e : Expr} {t : Term} (h : Expr.MEval db σ e t) : e.NoPrim → e.eval σ = some t := by
  match h with
  | .lit => intro _; rfl
  | .var hv => intro _; exact hv
  | .ctor _ _ hl =>
    intro hp
    rw [Expr.eval_app, Expr.evalList_of_MEvalList hsig hl hp.2, Option.map_some]
  | .prim hf _ _ => intro hp; exact absurd hf (by rw [hp.1]; simp)

theorem Expr.evalList_of_MEvalList {db : Database} (hsig : db.sig.AllConstructors)
    {σ : Env} {es : List Expr} {ts : List Term} (h : Expr.MEvalList db σ es ts) :
    Expr.NoPrimList es → Expr.evalList es σ = some ts := by
  match h with
  | .nil => intro _; rfl
  | .cons he hl =>
    intro hp
    rw [Expr.evalList_cons, Expr.eval_of_MEval hsig he hp.1, Option.bind_some,
      Expr.evalList_of_MEvalList hsig hl hp.2, Option.map_some]

end

mutual

/-- **`MEval` is deterministic**, on any signature and any expression.

This used to hold only on the constructor fragment (`AllConstructors`, `NoPrim`), because
`lookup` read `Out`, which a key class can satisfy several times over. With reading
confined to the query there is one rule per syntactic form — `ctor` and `prim` are split
on `Prim.ofName f` — so the derivation is determined by the expression.

It is what makes M12's recovery plan (`PLAN.md`) work, and more: a relation that is a
function *unconditionally* can simply be replaced by one. -/
theorem Expr.MEval_unique {db : Database} {σ : Env} {e : Expr} {t₁ t₂ : Term}
    (h₁ : Expr.MEval db σ e t₁) (h₂ : Expr.MEval db σ e t₂) : t₁ = t₂ := by
  match h₁, h₂ with
  | .lit, .lit => rfl
  | .var hv₁, .var hv₂ => exact Option.some.inj (hv₁.symm.trans hv₂)
  | .ctor _ _ hl₁, .ctor _ _ hl₂ => rw [Expr.MEvalList_unique hl₁ hl₂]
  | .ctor hp _ _, .prim hf _ _ => exact absurd (hp.symm.trans hf) (by simp)
  | .prim hf _ _, .ctor hp _ _ => exact absurd (hf.symm.trans hp) (by simp)
  | .prim hf₁ hl₁ hv₁, .prim hf₂ hl₂ hv₂ =>
    rw [Expr.MEvalList_unique hl₁ hl₂] at hv₁
    rw [Option.some.inj (hf₁.symm.trans hf₂)] at hv₁
    exact Option.some.inj (hv₁.symm.trans hv₂)

/-- `Expr.MEval_unique` over an argument list. -/
theorem Expr.MEvalList_unique {db : Database} {σ : Env} {es : List Expr}
    {ts₁ ts₂ : List Term} (h₁ : Expr.MEvalList db σ es ts₁)
    (h₂ : Expr.MEvalList db σ es ts₂) : ts₁ = ts₂ := by
  match h₁, h₂ with
  | .nil, .nil => rfl
  | .cons he₁ hl₁, .cons he₂ hl₂ =>
    rw [Expr.MEval_unique he₁ he₂, Expr.MEvalList_unique hl₁ hl₂]

end

/-- **An action step is deterministic.** Every premise of every case is an evaluation, and
those are unique, so the resulting database is.

This is the input to M12's remaining question (`PLAN.md`): `ActionStep` and `ActionsStep`
can go back to being *functions*. What cannot is anything above them — `MergeStep` chooses
which pair of rows collides and in which order, and `MergeClosure` how many steps to take,
so `RunStep`, `CmdStep` and `ProgramStep` stay relations. -/
theorem Database.ActionStep_unique {db d₁ d₂ : Database} {a : Action}
    (h₁ : Database.ActionStep db a d₁) (h₂ : Database.ActionStep db a d₂) : d₁ = d₂ := by
  cases h₁ with
  | expr he₁ => cases h₂ with | expr he₂ => rw [Expr.MEval_unique he₁ he₂]
  | letBind he₁ => cases h₂ with | letBind he₂ => rw [Expr.MEval_unique he₁ he₂]
  | union ha₁ hb₁ =>
    cases h₂ with
    | union ha₂ hb₂ => rw [Expr.MEval_unique ha₁ ha₂, Expr.MEval_unique hb₁ hb₂]
  | set ha₁ hb₁ =>
    cases h₂ with
    | set ha₂ hb₂ => rw [Expr.MEvalList_unique ha₁ ha₂, Expr.MEvalList_unique hb₁ hb₂]

/-- `Database.ActionStep_unique` over an action list. -/
theorem Database.ActionsStep_unique {db d₁ d₂ : Database} {as : List Action}
    (h₁ : Database.ActionsStep db as d₁) (h₂ : Database.ActionsStep db as d₂) : d₁ = d₂ := by
  induction h₁ with
  | nil => cases h₂ with | nil => rfl
  | cons ha₁ _ ih =>
    cases h₂ with
    | cons ha₂ hs₂ => exact ih (Database.ActionStep_unique ha₁ ha₂ ▸ hs₂)

/-- The rest of M9 collapses too: with no `.merge` function there is no collision to
resolve, so a round is `RunRules` and nothing else. Companion to `mcong_iff_cong` on
the *step* side — together they say M9 restricted to constructors is M0–M8 unchanged. -/
theorem MergeStep.saturated_of_allConstructors {db : Database}
    (hsig : db.sig.AllConstructors) : MergeSaturated db := by
  intro db' h
  cases h with
  | collide _ _ _ hm _ _ =>
    rw [Signature.mergeOf_eq_union hsig] at hm
    exact absurd hm (by simp)

/-! ### The least-congruence principle

How every negative fact about the closure gets proved, and the shape the M11
checker-soundness argument takes. `Cong.le` with the `congr` hypothesis replaced by an
`fd` one. -/
mutual

/-- `MCong db` is the least relation closed under `db`'s assertions, reflexivity on its
terms, symmetry, transitivity and the functional dependency. -/
theorem MCong.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {a b : Term} (h : MCong db a b) : R a b := by
  match h with
  | .assert hm => exact hassert _ _ hm
  | .refl hm => exact hrefl _ hm
  | .symm h => exact hsymm _ _ (MCong.le hassert hrefl hsymm htrans hfd h)
  | .trans h₁ h₂ =>
    exact htrans _ _ _ (MCong.le hassert hrefl hsymm htrans hfd h₁)
      (MCong.le hassert hrefl hsymm htrans hfd h₂)
  | .fd hra hrb hu hl hxy =>
    exact hfd _ _ _ _ _ _ _ hra hrb hu (MCongList.le hassert hrefl hsymm htrans hfd hl) hxy

/-- `MCong.le` over key tuples; the companion `MCong.le`'s `fd` case recurses into. -/
theorem MCongList.le {db : Database} {R : Term → Term → Prop}
    (hassert : ∀ a b, (a, b) ∈ db.eqs → R a b) (hrefl : ∀ a ∈ db.terms, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hfd : ∀ f as bs (a b : List Term) x y, Row.mk f as a ∈ db.rows →
      Row.mk f bs b ∈ db.rows → db.sig.mergeOf f = MergeSpec.union →
      List.Forall₂ R as bs → (x, y) ∈ a.zip b → R x y)
    {as bs : List Term} (h : MCongList db as bs) : List.Forall₂ R as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.le hassert hrefl hsymm htrans hfd hab)
      (MCongList.le hassert hrefl hsymm htrans hfd hl)

end

/-! ### `MCongList` is an equivalence

`MCong.setoid` pointwise. `Out.union_cong` needs it: two lookups at one key class reach
their rows through *different* congruent keys, and `fd` compares those two directly. -/
theorem MCongList.symm {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    MCongList db bs as := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab.symm (MCongList.symm hl)

theorem MCongList.trans {db : Database} {as bs cs : List Term} (h₁ : MCongList db as bs)
    (h₂ : MCongList db bs cs) : MCongList db as cs := by
  match h₁, h₂ with
  | .nil, .nil => exact .nil
  | .cons hab hl₁, .cons hbc hl₂ => exact .cons (hab.trans hbc) (MCongList.trans hl₁ hl₂)

theorem MCongList.forall₂ {db : Database} {as bs : List Term} (h : MCongList db as bs) :
    List.Forall₂ (MCong db) as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl => exact .cons hab (MCongList.forall₂ hl)

theorem MCongList.ofForall₂ {db : Database} {as bs : List Term}
    (h : List.Forall₂ (MCong db) as bs) : MCongList db as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

/-! ### Monotonicity

Constraint (3). That a merge *adds* the combined row instead of replacing the two it
combined is exactly what these need.

All three carry an **added hypothesis** `d₁.sig = d₂.sig`, and it is not decoration:
`Database.Contained` ignores `sig`, while `MCong.fd` fires only where
`mergeOf f = .union`, so redeclaring `f` as `:no-merge` destroys a derivation without
removing anything. `mcong_mono_needs_sig` below is the counterexample. Every use in this
file has it — `MergeStep.sig` and `MergeClosure.sig` — because only `Cmd.decl` writes
`sig`. -/
mutual

/-- Adding terms, rows and equalities only adds derivations. `Cong.mono`, with the
`fd` case in place of `congr`. -/
theorem MCong.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {a b : Term} (hc : MCong d₁ a b) : MCong d₂ a b := by
  match hc with
  | .assert hm => exact .assert (h.eqs hm)
  | .refl hm => exact .refl (h.terms hm)
  | .symm hc => exact .symm (MCong.mono h hsig hc)
  | .trans h₁ h₂ => exact .trans (MCong.mono h hsig h₁) (MCong.mono h hsig h₂)
  | .fd hra hrb hu hl hxy =>
    exact .fd (h.rows hra) (h.rows hrb) (hsig ▸ hu) (MCongList.mono h hsig hl) hxy

theorem MCongList.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {as bs : List Term} (hc : MCongList d₁ as bs) : MCongList d₂ as bs := by
  match hc with
  | .nil => exact .nil
  | .cons hab hl => exact .cons (MCong.mono h hsig hab) (MCongList.mono h hsig hl)

end

/-- **Why `MCong.mono` needs the signature hypothesis.** Two rows of `f` recording
different outputs at one key make those outputs `fd`-equal while `f` is a constructor.
Declaring `f` `:no-merge` adds no term, row or equality — so `Contained` still holds —
and takes the derivation away. -/
theorem mcong_mono_needs_sig : ∃ d₁ d₂ : Database, ∃ a b : Term,
    d₁.Contained d₂ ∧ MCong d₁ a b ∧ ¬ MCong d₂ a b := by
  classical
  let x : Term := .lit (.int 0)
  let y : Term := .lit (.int 1)
  let rows : Set Row := {Row.mk "f" [] [x], Row.mk "f" [] [y]}
  let d₁ : Database := ⟨fun _ => none, ∅, rows, ∅, [], ∅⟩
  let d₂ : Database := ⟨fun _ => some ⟨0, 1, .noMerge⟩, ∅, rows, ∅, [], ∅⟩
  refine ⟨d₁, d₂, x, y, ⟨subset_rfl, subset_rfl, subset_rfl⟩, ?_, ?_⟩
  · exact MCong.fd (f := "f") (as := []) (bs := []) (a := [x]) (b := [y])
      (by simp [d₁, rows]) (by simp [d₁, rows]) rfl .nil (by simp)
  · intro h
    have hxy : x = y :=
      MCong.le (R := fun a b => a = b) (by simp [d₂]) (by simp [d₂]) (fun _ _ h => h.symm)
        (fun _ _ _ h₁ h₂ => h₁.trans h₂)
        (fun _ _ _ _ _ _ _ _ _ hu _ _ => absurd hu (by simp [d₂, Signature.mergeOf])) h
    simp [x, y] at hxy

/-- `Out` is monotone, because both of its conjuncts are. A rule body reading a table
never *loses* a match — the property an overwriting merge would destroy, and the one
seminaive evaluation rests on. -/
theorem Database.Out.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {f : FnName} {as vs : List Term} (ho : d₁.Out f as vs) : d₂.Out f as vs := by
  obtain ⟨bs, hl, hrow⟩ := ho
  exact ⟨bs, MCongList.mono h hsig hl, h.rows hrow⟩

/-- Row actions only add, exactly as `evalAction_contained` does for `Action`. -/
theorem Database.ActionStep.contained {db d : Database} {a : Action}
    (h : Database.ActionStep db a d) : db.Contained d := by
  cases h with
  | expr => exact Database.Contained.addTerm _ _
  | letBind => exact ⟨Set.subset_union_left, Set.subset_union_left, subset_rfl⟩
  | union => exact Database.Contained.addEq _ _ _
  | set => exact Database.Contained.addRow _ _ _ _

theorem Database.ActionsStep.contained {db d : Database} {as : List Action}
    (h : Database.ActionsStep db as d) : db.Contained d := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons ha _ ih => exact (Database.ActionStep.contained ha).trans ih

/-- **A merge never shrinks the database.**

Constraint (3), discharged by the representation rather than by an argument: the step
adds the combined row beside the two it merged, so there is nothing to overwrite. This
is what lets `MCong.mono`, `Out.mono` and every `WF`-preservation lemma survive into
M9 unchanged. -/
theorem MergeStep.contained {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₁.Contained d₂ := by
  cases h with
  | @collide d f as _ _ _ vs _ _ _ _ _ _ hbody _ =>
    have hb : d₁.Contained d :=
      ⟨(Database.ActionsStep.contained hbody).terms,
        (Database.ActionsStep.contained hbody).rows,
        (Database.ActionsStep.contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hc.terms, hc.rows, hc.eqs⟩

theorem MergeClosure.contained {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₁.Contained d₂ := by
  induction h with
  | refl => exact Database.Contained.refl _
  | tail _ hstep ih => exact ih.trans (MergeStep.contained hstep)

set_option linter.unusedVariables false in
/-- **A vacuous self-collision is the identity step.**

Three hypotheses beyond the original statement, all forced and all discharged by the
invariants `addTerm` maintains: `addRow` re-inserts the row's key and value terms, so
those insertions have to be no-ops. See `Database.addTerm_eq_self`.

`hsig` and `hres` are not used by the equation — they are what makes the conclusion an
instance of `MergeStep`, so removing them would change what the theorem says. -/
theorem MergeStep.self_id {db d : Database} {f : FnName} {as a : List Term}
    {body : List Action} {res : List Expr} (hw : db.WF) (hrw : db.RowsWF)
    (hctor : Database.ctorRowsOf db.terms ⊆ db.rows) (hrow : Row.mk f as a ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.merge body res)
    (hbody : Database.ActionsStep { db with env := mergeEnv a a } body d)
    (hfix : d.terms = db.terms ∧ d.rows = db.rows ∧ d.eqs = db.eqs)
    (hres : Expr.MEvalList d d.env res a) :
    ({ d.addRow f as a with env := db.env, rules := db.rules } : Database) = db := by
  obtain ⟨hft, hfr, hfe⟩ := hfix
  have hbase : (db.addTerms as).addTerms a = db := by
    rw [Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).1 t ht]
    exact Database.addTerms_eq_self hw hctor fun t ht => (hrw _ hrow).2 t ht
  obtain ⟨h1t, h1r⟩ := Database.addTerms_terms_rows hft hfr as
  obtain ⟨h2t, h2r⟩ := Database.addTerms_terms_rows h1t h1r a
  rw [hbase] at h2t h2r
  have hsg := Database.ActionsStep.sig hbody
  refine Database.ext ?_ ?_ ?_ ?_ rfl rfl
  · exact (Database.addRow_sig (db := d) (f := f) (as := as) (vs := a)).trans hsg
  · exact h2t
  · change insert (Row.mk f as a) ((d.addTerms as).addTerms a).rows = db.rows
    rw [h2r]
    exact Set.insert_eq_self.mpr hrow
  · exact (Database.addRow_eqs (db := d) (f := f) (as := as) (vs := a)).trans hfe

/-! ### The observable value

Constraint (3)'s second half. `PLAN.md` proposes a merge-fold and asks for it to be
well defined; `Current` is that value defined as a maximum instead, which needs only
antisymmetry. It is not what `Expr.MEval` reads. -/
/-- The observable value is unique. This is "the fold is well defined", with a fold's
commutativity and associativity obligations replaced by antisymmetry of the order —
see `MERGE.md`, "Why a maximum and not a fold". -/
theorem Database.current_unique {db : Database} {le : List Term → List Term → Prop}
    (hanti : ∀ x y, le x y → le y x → x = y) {f : FnName} {as v w : List Term}
    (hv : db.Current le f as v) (hw : db.Current le f as w) : v = w :=
  hanti _ _ (hw.2 v hv.1) (hv.2 w hw.1)

/-! ### The term order

`Term.blt` unfolds definitionally in every case, so the equation lemmas below are `rfl`
and the three order laws are ordinary case analyses over the (length, name, lex) key.
`Term.bltList` is only used at equal lengths, which is why *totality* is the one law
that needs a length hypothesis on the list level — `bltList [] (b :: bs)` and
`bltList (b :: bs) []` are both `false`. -/
namespace Term
@[simp] theorem blt_lit_lit {m n : Int} :
    Term.blt (.lit (.int m)) (.lit (.int n)) = decide (m < n) := rfl

@[simp] theorem blt_lit_app {l : Lit} {f : FnName} {as : List Term} :
    Term.blt (.lit l) (.app f as) = true := by cases l; rfl

@[simp] theorem blt_app_lit {f : FnName} {as : List Term} {l : Lit} :
    Term.blt (.app f as) (.lit l) = false := rfl

theorem blt_app_app {f g : FnName} {as bs : List Term} :
    Term.blt (.app f as) (.app g bs) =
      (if as.length ≠ bs.length then decide (as.length < bs.length)
       else if f ≠ g then decide (f < g) else Term.bltList as bs) := rfl

@[simp] theorem bltList_nil {bs : List Term} : Term.bltList [] bs = false := rfl

@[simp] theorem bltList_cons_nil {a : Term} {as : List Term} :
    Term.bltList (a :: as) [] = false := rfl

theorem bltList_cons_cons {a b : Term} {as bs : List Term} :
    Term.bltList (a :: as) (b :: bs) =
      if a = b then Term.bltList as bs else Term.blt a b := rfl

end Term
mutual

/-- Asymmetry. On the list level this needs no length hypothesis: a `bltList` between
lists of different lengths is `false` in both directions. -/
theorem Term.blt_asymm (s t : Term) (h : Term.blt s t = true) : Term.blt t s = false := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    rw [Term.blt_lit_lit] at h
    rw [Term.blt_lit_lit, decide_eq_false_iff_not]
    simp only [decide_eq_true_eq] at h
    omega
  | .lit _, .app _ _ => rfl
  | .app _ _, .lit _ => simp at h
  | .app f as, .app g bs =>
    rw [Term.blt_app_app] at h
    rw [Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl)] at h
      rw [if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf)] at h
        rw [if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_asymm as bs h
      · rw [if_pos hf] at h
        rw [if_pos (Ne.symm hf), decide_eq_false_iff_not]
        simp only [decide_eq_true_eq] at h
        exact String.lt_asymm h
    · rw [if_pos hl] at h
      rw [if_pos (Ne.symm hl), decide_eq_false_iff_not]
      simp only [decide_eq_true_eq] at h
      omega

theorem Term.bltList_asymm (as bs : List Term) (h : Term.bltList as bs = true) :
    Term.bltList bs as = false := by
  match as, bs with
  | [], _ => simp at h
  | _ :: _, [] => simp at h
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons] at h
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h
      rw [if_pos hab.symm]
      exact Term.bltList_asymm as bs h
    · rw [if_neg hab] at h
      rw [if_neg (Ne.symm hab)]
      exact Term.blt_asymm a b h

end

mutual

/-- Totality. `bltList` gets the length hypothesis `blt` guarantees at every call. -/
theorem Term.blt_total (s t : Term) (h : s ≠ t) :
    Term.blt s t = true ∨ Term.blt t s = true := by
  match s, t with
  | .lit (.int m), .lit (.int n) =>
    have hmn : m ≠ n := fun hmn => h (by rw [hmn])
    have : m < n ∨ n < m := by omega
    rcases this with hh | hh
    · exact Or.inl (by simp [hh])
    · exact Or.inr (by simp [hh])
  | .lit _, .app _ _ => exact Or.inl (by simp)
  | .app _ _, .lit _ => exact Or.inr (by simp)
  | .app f as, .app g bs =>
    rw [Term.blt_app_app, Term.blt_app_app]
    by_cases hl : as.length = bs.length
    · rw [if_neg (not_not_intro hl), if_neg (not_not_intro hl.symm)]
      by_cases hf : f = g
      · rw [if_neg (not_not_intro hf), if_neg (not_not_intro hf.symm)]
        subst hf
        exact Term.bltList_total as bs hl fun hab => h (by rw [hab])
      · rw [if_pos hf, if_pos (Ne.symm hf)]
        simp only [decide_eq_true_eq]
        by_cases hfg : f < g
        · exact Or.inl hfg
        · refine Or.inr ?_
          by_contra hgf
          exact hf (String.le_antisymm (String.not_lt.mp hgf) (String.not_lt.mp hfg))
    · rw [if_pos hl, if_pos (Ne.symm hl)]
      simp only [decide_eq_true_eq]
      omega

theorem Term.bltList_total (as bs : List Term) (hlen : as.length = bs.length)
    (h : as ≠ bs) : Term.bltList as bs = true ∨ Term.bltList bs as = true := by
  match as, bs with
  | [], [] => exact absurd rfl h
  | [], _ :: _ => simp at hlen
  | _ :: _, [] => simp at hlen
  | a :: as, b :: bs =>
    rw [Term.bltList_cons_cons, Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab.symm]
      subst hab
      exact Term.bltList_total as bs (by simpa using hlen) fun hh => h (by rw [hh])
    · rw [if_neg hab, if_neg (Ne.symm hab)]
      exact Term.blt_total a b hab

end

mutual

/-- Transitivity. The only case that needs asymmetry is the list one: `a ≠ c` has to be
derived from `blt a b` and `blt b c` before the lexicographic step can fire. -/
theorem Term.blt_trans (s t u : Term) (h₁ : Term.blt s t = true)
    (h₂ : Term.blt t u = true) : Term.blt s u = true := by
  match s, t, u with
  | .lit (.int m), .lit (.int n), .lit (.int p) =>
    rw [Term.blt_lit_lit] at h₁ h₂ ⊢
    simp only [decide_eq_true_eq] at h₁ h₂ ⊢
    omega
  | .lit _, .lit _, .app _ _ => simp
  | .lit _, .app _ _, .lit _ => simp at h₂
  | .lit _, .app _ _, .app _ _ => simp
  | .app _ _, .lit _, _ => simp at h₁
  | .app _ _, .app _ _, .lit _ => simp at h₂
  | .app f as, .app g bs, .app e cs =>
    rw [Term.blt_app_app] at h₁ h₂
    rw [Term.blt_app_app]
    by_cases hab : as.length = bs.length
    · rw [if_neg (not_not_intro hab)] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        rw [if_neg (not_not_intro (hab.trans hbc))]
        by_cases hfg : f = g
        · rw [if_neg (not_not_intro hfg)] at h₁
          by_cases hge : g = e
          · rw [if_neg (not_not_intro hge)] at h₂
            rw [if_neg (not_not_intro (hfg.trans hge))]
            subst hfg; subst hge
            exact Term.bltList_trans as bs cs h₁ h₂
          · rw [if_pos hge] at h₂
            have hfe : f ≠ e := by rintro rfl; exact hge hfg.symm
            rw [if_pos hfe]
            subst hfg
            exact h₂
        · rw [if_pos hfg] at h₁
          by_cases hge : g = e
          · have hfe : f ≠ e := by rintro rfl; exact hfg hge.symm
            rw [if_pos hfe]
            subst hge
            exact h₁
          · rw [if_pos hge] at h₂
            simp only [decide_eq_true_eq] at h₁ h₂
            have hlt : f < e := String.lt_trans h₁ h₂
            have hfe : f ≠ e := by rintro rfl; exact String.lt_irrefl f hlt
            rw [if_pos hfe, decide_eq_true_eq]
            exact hlt
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
    · rw [if_pos hab] at h₁
      simp only [decide_eq_true_eq] at h₁
      by_cases hbc : bs.length = cs.length
      · rw [if_neg (not_not_intro hbc)] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega
      · rw [if_pos hbc] at h₂
        simp only [decide_eq_true_eq] at h₂
        have hac : as.length ≠ cs.length := by omega
        rw [if_pos hac, decide_eq_true_eq]
        omega

theorem Term.bltList_trans (as bs cs : List Term) (h₁ : Term.bltList as bs = true)
    (h₂ : Term.bltList bs cs = true) : Term.bltList as cs = true := by
  match as, bs, cs with
  | [], _, _ => simp at h₁
  | _ :: _, [], _ => simp at h₁
  | _ :: _, _ :: _, [] => simp at h₂
  | a :: as, b :: bs, c :: cs =>
    rw [Term.bltList_cons_cons] at h₁ h₂
    rw [Term.bltList_cons_cons]
    by_cases hab : a = b
    · rw [if_pos hab] at h₁
      by_cases hbc : b = c
      · rw [if_pos hbc] at h₂
        rw [if_pos (hab.trans hbc)]
        exact Term.bltList_trans as bs cs h₁ h₂
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by rintro rfl; exact hbc hab.symm
        rw [if_neg hac, hab]
        exact h₂
    · rw [if_neg hab] at h₁
      by_cases hbc : b = c
      · have hac : a ≠ c := by rintro rfl; exact hab hbc.symm
        rw [if_neg hac, ← hbc]
        exact h₁
      · rw [if_neg hbc] at h₂
        have hac : a ≠ c := by
          rintro rfl
          rw [Term.blt_asymm a b h₁] at h₂
          simp at h₂
        rw [if_neg hac]
        exact Term.blt_trans a b c h₁ h₂

end

/-- `Term.blt` is a strict linear order. Needed for `ordering-min`/`ordering-max` to be
a deterministic choice, and for "keep the smaller side" to descend. -/
theorem Term.blt_linear : (∀ s t : Term, Term.blt s t = true → Term.blt t s = false) ∧
    (∀ s t : Term, s ≠ t → Term.blt s t = true ∨ Term.blt t s = true) ∧
    (∀ s t u : Term, Term.blt s t = true → Term.blt t u = true → Term.blt s u = true) :=
  ⟨Term.blt_asymm, Term.blt_total, Term.blt_trans⟩

/-- **A `.union` function's outputs are all congruent.**

The functional dependency, stated as what it buys: however many rows a `.union`
function accumulates at one key class, they are one e-class. For `@UF_<Sort>` this is
"every parent a term ever had is equal to it"; for `@<C>View` it is congruence. -/
theorem Database.Out.union_cong {db : Database} {f : FnName} {as v w : List Term}
    {x y : Term} (hsig : db.sig.mergeOf f = MergeSpec.union) (hv : db.Out f as v)
    (hw : db.Out f as w) (hxy : (x, y) ∈ v.zip w) : MCong db x y := by
  obtain ⟨bs, hlb, hrb⟩ := hv
  obtain ⟨cs, hlc, hrc⟩ := hw
  exact .fd hrb hrc hsig (hlb.symm.trans hlc) hxy

/-! ### Invariants over the step relation

The shape every M11 safety theorem takes, and the reason termination and confluence are
*not* in the spec: an invariant holds at every reachable state, so a run that diverges
satisfies it throughout and a run that merges in a different order satisfies it too.
"Every proof row the encoding writes is checker-valid" is one of these. -/
/-- Reachable states satisfy any invariant preserved by one command. -/
theorem invariant_of_step {I : Database → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    {db db' : Database} {p : Program} (hinit : I db) (h : ProgramStep db p db') :
    I db' := by
  induction h with
  | nil => exact hinit
  | cons hc _ ih => exact ih (hstep _ _ _ hinit hc)

/-- **Every command only adds.**

The formal content of "never delete a term row or a proof row", which the encoding
depends on and which the invariant argument needs: anything the checker reads is
positive in the state, so once true it stays true. `.rule` and `.decl` touch only
fields `Contained` ignores. -/
theorem CmdStep.contained {db db' : Database} {c : Cmd} (h : CmdStep db c db') :
    db.Contained db' := by
  cases h with
  | action ha hm =>
    exact (Database.ActionStep.contained ha).trans (MergeClosure.contained hm)
  | rule => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩
  | run hrun =>
    have hu : db.Contained (RunRules db) := Database.Contained.sUnion _ _
    exact hu.trans (MergeClosure.contained hrun)
  | decl => exact ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem ProgramStep.contained {db db' : Database} {p : Program}
    (h : ProgramStep db p db') : db.Contained db' := by
  induction h with
  | nil => exact Database.Contained.refl _
  | cons hc _ ih => exact (CmdStep.contained hc).trans ih

/-! ### Determinism

Demoted. Confluence is not needed by any safety theorem — see `invariant_of_step`. It
buys one thing only: strengthening M10's refinement from "the interpreter's result is
spec-reachable" to an equality. -/
/-! **Evaluation reads the database only through its signature.** With `lookup` gone, no
rule mentions `terms`, `rows` or `eqs`, and `sig` is consulted only to tell a constructor
from a name the program should not have applied. Monotonicity in `Contained` — half of
what a diamond proof for `MergeStep` needs, see `MergeStep.diamond_of_join` — is the
corollary, and it no longer uses its containment hypothesis at all. -/
mutual

/-- Two databases with the same signature admit the same evaluations. -/
theorem Expr.MEval.ofSig {d₁ d₂ : Database} (hsig : d₁.sig = d₂.sig)
    {σ : Env} {e : Expr} {t : Term} (h : Expr.MEval d₁ σ e t) : Expr.MEval d₂ σ e t := by
  match h with
  | .lit => exact .lit
  | .var hv => exact .var hv
  | .ctor hp hu hl => exact .ctor hp (hsig ▸ hu) (Expr.MEvalList.ofSig hsig hl)
  | .prim hp hl hv => exact .prim hp (Expr.MEvalList.ofSig hsig hl) hv

/-- `Expr.MEval.ofSig` over an argument list. -/
theorem Expr.MEvalList.ofSig {d₁ d₂ : Database} (hsig : d₁.sig = d₂.sig)
    {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.MEvalList d₁ σ es ts) : Expr.MEvalList d₂ σ es ts := by
  match h with
  | .nil => exact .nil
  | .cons he hl => exact .cons (Expr.MEval.ofSig hsig he) (Expr.MEvalList.ofSig hsig hl)

end

/-- A larger database admits every evaluation a smaller one does. Kept for the call sites
that thread `Contained` and `sig` together; the containment is not used. -/
theorem Expr.MEval.mono {d₁ d₂ : Database} (_hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    {σ : Env} {e : Expr} {t : Term} (h : Expr.MEval d₁ σ e t) : Expr.MEval d₂ σ e t :=
  h.ofSig hsig

/-- `Expr.MEval.mono` over an argument list. -/
theorem Expr.MEvalList.mono {d₁ d₂ : Database} (_hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.MEvalList d₁ σ es ts) : Expr.MEvalList d₂ σ es ts :=
  h.ofSig hsig

/-- A saturated state is a fixpoint of the whole closure, not only of one step. -/
theorem MergeSaturated.closure_eq {db d : Database} (hs : MergeSaturated db)
    (h : MergeClosure db d) : d = db := by
  induction h with
  | refl => rfl
  | @tail _ _ _ hstep ih => subst ih; exact hs _ hstep

/-- A merge that is a `le`-join is locally confluent: two collisions available at once
can be fired in either order and rejoined. **Unproved, and the statement is worse than
"not known to hold" — `hjoin` is vacuous.** Instantiate `le := fun _ _ => False`:
then `db.Current le f as v` unfolds to `db.Out f as v ∧ ∀ ws, db.Out f as ws → False`,
which is self-contradictory, so `hjoin` holds for *every* `db` and the statement is
unconditional local confluence of `MergeStep`. Any repair has to make the join
condition bite on the merge *body*, not on `Current`.

Unconditional local confluence nevertheless looks **true**, and in the stronger
one-step-on-one-side form `Relation.church_rosser` wants, for a reason `MERGE.md`'s
"open question 2" does not consider: a step's *effect* does not depend on the ambient
state. `addTerm`/`addEq`/`addRow` each add a set determined by the terms involved, and
those terms are fixed by the evaluation witnesses, which `Expr.MEval.mono` says stay
available in a larger database. So firing collision 2 at `d₁` and collision 1 at `d₂`
should land on the same state — the third table's merge that `MERGE.md` worries about
is a *later* step, and it too remains available because nothing is removed.

What is missing is exactness, and only exactness. The *existential* form of that
transport — `ActionsStep db body d → db.Contained e → e.sig = db.sig → e.env = db.env →
∃ d', ActionsStep e body d' ∧ d.Contained d'` — is `Database.ActionsStep.mono` below,
and it is enough for the containment contract. The diamond needs the same statement with
`d'` pinned to the componentwise join `e ⊔ d`, which is one case per action against the
set algebra of `addTerm`/`addTerms`/`addRow`; that part is still open. -/
theorem MergeStep.diamond_of_join {db d₁ d₂ : Database}
    {le : List Term → List Term → Prop}
    (hjoin : ∀ f as v w, db.Current le f as v → db.Out f as w → le w v)
    (h₁ : MergeStep db d₁) (h₂ : MergeStep db d₂) :
    ∃ d, MergeClosure d₁ d ∧ MergeClosure d₂ d := by
  sorry

/-- **`hconf` is too weak to use.** Local confluence plus "both are normal forms" gives
uniqueness only via Newman's lemma, which needs the relation to be *terminating* — and
`MergeStep` deliberately is not (`MERGE.md`, constraint (6)). Without termination the
implication genuinely fails in general rewriting: `a ⇄ b`, `a → c`, `b → d` with `c`,
`d` normal is locally confluent and has two normal forms. That shape cannot arise here,
because `MergeStep.contained` forbids cycles — so the *conclusion* is very likely true
— but it is true for a reason `hconf` does not supply, and the only route to it is the
strong diamond, which is `MergeStep.diamond_of_join` restated. Hence
`RunStep.unique_of_diamond` below, which is this theorem with a hypothesis a proof can
actually consume. -/
theorem RunStep.unique_of_confluent {db d₁ d₂ : Database}
    (hconf : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', MergeClosure e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  sorry

/-- With a confluent merge the *saturated* states of a round coincide, so an
interpreter that runs merges to a fixpoint computes the one answer `RunStep` allows
that egglog also allows. `RunStep` itself stays a relation.

The hypothesis is `Relation.church_rosser`'s: one of the two joining paths has to be at
most a *single* step. That is exactly the form the monotonicity argument in
`MergeStep.diamond_of_join` would give, and unlike plain local confluence it needs no
termination. -/
theorem RunStep.unique_of_diamond {db d₁ d₂ : Database}
    (hdiamond : ∀ e e₁ e₂, MergeStep e e₁ → MergeStep e e₂ →
      ∃ e', Relation.ReflGen MergeStep e₁ e' ∧ MergeClosure e₂ e')
    (hs₁ : MergeSaturated d₁) (hs₂ : MergeSaturated d₂)
    (h₁ : RunStep db d₁) (h₂ : RunStep db d₂) : d₁ = d₂ := by
  obtain ⟨e, he₁, he₂⟩ := Relation.church_rosser hdiamond h₁ h₂
  exact (hs₁.closure_eq he₁).symm.trans (hs₂.closure_eq he₂)

/-! ### Fewer rows mean fewer matches

The other half of the containment contract. `mergeRound_confined` says the implementation
deletes only what it may; this says that deleting can only *lose* results, never invent
them — there is no negation anywhere in the fragment, so every premise of a match is
positive in the state. Together they are "the implementation may find fewer results, never
more", which is the safe direction for M11: a safety property is positive in the state, so
it transfers downward. `Database.Contained`'s `addTerm_mono` family, in
`Proofs/Database.lean`, is what carries a match along. -/
theorem ValidEnv.mono {d₁ d₂ : Database} (h : d₁.Contained d₂) {vars : List Var}
    {σ : Env} (hv : ValidEnv vars d₁ σ) : ValidEnv vars d₂ σ :=
  ⟨hv.1, fun b hb => h.terms (hv.2 b hb)⟩

/-- **A larger database admits every match a smaller one does.** Read contrapositively —
which is how the containment contract uses it — a database missing rows finds at most the
matches the full one finds. -/
theorem MValidSubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂) (hsig : d₁.sig = d₂.sig)
    (henv : d₂.env = d₁.env) {p : Pattern} {σ : Env} (h : MValidSubst d₁ p σ) :
    MValidSubst d₂ p σ := by
  have hsig₁ : ∀ t : Term, (d₁.addTerm t).sig = (d₂.addTerm t).sig := fun _ => hsig
  cases h with
  | expr hv hw he hcong =>
    refine .expr ?_ (hc.terms hw) ?_ (MCong.mono (hc.addTerm_mono _) (hsig₁ _) hcong)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEval.mono hc hsig he
  | eq hv hw he₁ he₂ hc₁ hc₂ =>
    refine .eq ?_ (hc.terms hw) ?_ ?_
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₁)
      (MCong.mono ((hc.addTerm_mono _).addTerm_mono _) hsig hc₂)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEval.mono hc hsig he₁
    · rw [henv]; exact Expr.MEval.mono hc hsig he₂
  | values hv hu ht hk hw hrow =>
    refine .values ?_ ?_ ?_ (MCongList.mono hc hsig hk) (MCongList.mono hc hsig hw)
      (hc.rows hrow)
    · rw [henv]; exact hv.mono hc
    · rw [henv]; exact Expr.MEvalList.mono hc hsig hu
    · rw [henv]; exact Expr.MEvalList.mono hc hsig ht

theorem MValidQuerySubst.mono {d₁ d₂ : Database} (hc : d₁.Contained d₂)
    (hsig : d₁.sig = d₂.sig) (henv : d₂.env = d₁.env) {q : Query} {σ : Env}
    (h : MValidQuerySubst d₁ q σ) : MValidQuerySubst d₂ q σ := by
  obtain ⟨σs, hall, hu⟩ := h
  exact ⟨σs, hall.imp fun _ _ hv => MValidSubst.mono hc hsig henv hv, hu⟩

/-! ### Transporting a step

A step's *effect* is fixed by the evaluation witnesses it carries, and those witnesses
depend on the state only through `Expr.MEval.mono` and on the environment only through
`Env.lookup`. Two transports follow, and the containment contract spends both.

Along `Contained`: the same block re-run on a larger state lands on a state containing
the smaller run's result. That is `Database.ActionsStep.mono`, and it is the weak — but
sufficient — form of what `MergeStep.diamond_of_join` wants.

Along `Env.Agree`: two environments no `lookup` can tell apart give runs differing only
in the `env` field, which `Database.EnvAgree.eq_of_env_rules` then collapses once the
caller's environment is restored. This is `Proofs/Eval.lean`'s `evalActions_envAgree`
for the relational semantics, and it is what lets a rule fire under the substitution the
specification admits rather than the one the enumerator emitted. -/

/-- Agreement survives a shared innermost binding, which is the `letBind` case of
`Database.ActionStep.envAgree`. -/
theorem Env.Agree.cons {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) (w : Var) (t : Term) :
    Env.Agree ((w, t) :: σ₁) ((w, t) :: σ₂) := by
  intro v
  simp only [Env.lookup_cons]
  split
  · rfl
  · exact h v

/-- `EnvAgree` fixes `terms`, `rows` and `eqs`, so it is `Contained` in both directions.
This is how the `Contained`-indexed monotonicity lemmas apply to it. -/
theorem Database.EnvAgree.contained {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) :
    d₁.Contained d₂ :=
  ⟨fun _ hx => h.terms ▸ hx, fun _ hx => h.rows ▸ hx, fun _ hx => h.eqs ▸ hx⟩

/-- The `union` case of `Database.ActionStep.envAgree`; companion of
`Database.EnvAgree.addTerm` and `.addRow` in `Proofs/Database.lean`. -/
theorem Database.EnvAgree.addEq {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (a b : Term) :
    (d₁.addEq a b).EnvAgree (d₂.addEq a b) :=
  let h' := (h.addTerm a).addTerm b
  ⟨h'.sig, h'.terms, h'.rows, by simp [Database.addEq, h.eqs], h'.rules, h'.env⟩

mutual

/-- `MEval` reads the environment only through `Env.lookup`, so agreeing environments
give the same values. -/
theorem Expr.MEval.agree {db : Database} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂) {e : Expr}
    {t : Term} (hv : Expr.MEval db σ₁ e t) : Expr.MEval db σ₂ e t := by
  match hv with
  | .lit => exact .lit
  | .var hl => exact .var ((h _).symm.trans hl)
  | .ctor hp hu hl => exact .ctor hp hu (Expr.MEvalList.agree h hl)
  | .prim hp hl hval => exact .prim hp (Expr.MEvalList.agree h hl) hval

/-- `Expr.MEval.agree` over an argument list. -/
theorem Expr.MEvalList.agree {db : Database} {σ₁ σ₂ : Env} (h : Env.Agree σ₁ σ₂)
    {es : List Expr} {ts : List Term} (hv : Expr.MEvalList db σ₁ es ts) :
    Expr.MEvalList db σ₂ es ts := by
  match hv with
  | .nil => exact .nil
  | .cons he hl => exact .cons (Expr.MEval.agree h he) (Expr.MEvalList.agree h hl)

end

/-- `mono` and `agree` composed, at the environment an `ActionStep` evaluates in. -/
theorem Expr.MEval.envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) {e : Expr} {t : Term}
    (hv : Expr.MEval d₁ d₁.env e t) : Expr.MEval d₂ d₂.env e t :=
  (Expr.MEval.mono h.contained h.sig hv).agree h.env

/-- `Expr.MEval.envAgree` over an argument list. -/
theorem Expr.MEvalList.envAgree {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) {es : List Expr}
    {ts : List Term} (hv : Expr.MEvalList d₁ d₁.env es ts) :
    Expr.MEvalList d₂ d₂.env es ts :=
  (Expr.MEvalList.mono h.contained h.sig hv).agree h.env

/-- **A step is blind to which of two agreeing environments it runs in.** The results
agree too, and `letBind` — the one action that writes `env` — writes the same binding on
both sides. -/
theorem Database.ActionStep.envAgree {d₁ d₂ c : Database} (h : d₁.EnvAgree d₂)
    {a : Action} (hs : Database.ActionStep d₁ a c) :
    ∃ c', Database.ActionStep d₂ a c' ∧ c.EnvAgree c' := by
  cases hs with
  | @expr e t he => exact ⟨d₂.addTerm t, .expr (Expr.MEval.envAgree h he), h.addTerm t⟩
  | @letBind v e t he =>
    refine ⟨{ d₂.addTerm t with env := (v, t) :: d₂.env },
      .letBind (Expr.MEval.envAgree h he), ?_⟩
    exact ⟨(h.addTerm t).sig, (h.addTerm t).terms, (h.addTerm t).rows, (h.addTerm t).eqs,
      (h.addTerm t).rules, h.env.cons v t⟩
  | @union e₁ e₂ t₁ t₂ h₁ h₂ =>
    exact ⟨d₂.addEq t₁ t₂,
      .union (Expr.MEval.envAgree h h₁) (Expr.MEval.envAgree h h₂), h.addEq t₁ t₂⟩
  | @set f args out ts vs h₁ h₂ =>
    exact ⟨d₂.addRow f ts vs,
      .set (Expr.MEvalList.envAgree h h₁) (Expr.MEvalList.envAgree h h₂), h.addRow f ts vs⟩

/-- `Database.ActionStep.envAgree` over a block. -/
theorem Database.ActionsStep.envAgree {d₁ d₂ c : Database} (h : d₁.EnvAgree d₂)
    {as : List Action} (hs : Database.ActionsStep d₁ as c) :
    ∃ c', Database.ActionsStep d₂ as c' ∧ c.EnvAgree c' := by
  induction hs generalizing d₂ with
  | nil => exact ⟨d₂, .nil, h⟩
  | @cons db x x' a as ha _ ih =>
    obtain ⟨y₁, hy₁, hag₁⟩ := Database.ActionStep.envAgree h ha
    obtain ⟨y₂, hy₂, hag₂⟩ := ih hag₁
    exact ⟨y₂, .cons hy₁ hy₂, hag₂⟩

/-- **A step available at `db` is available at any `D` containing it, with the same
effect.** The result is an existential over a database containing the smaller one, not
the exact join `MergeStep.diamond_of_join` asks for; `Expr.MEval.mono` is what makes the
witnesses survive. -/
theorem Database.ActionStep.mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {a : Action}
    (h : Database.ActionStep db a d) :
    ∃ D', Database.ActionStep D a D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  cases h with
  | @expr e t he =>
    refine ⟨D.addTerm t, .expr (Expr.MEval.mono hc hsig (henv ▸ he)),
      hc.addTerm_mono t, ?_, ?_⟩ <;> simp [hsig, henv]
  | @letBind v e t he =>
    refine ⟨{ D.addTerm t with env := (v, t) :: D.env },
      .letBind (Expr.MEval.mono hc hsig (henv ▸ he)), ?_, ?_, ?_⟩
    · exact ⟨(hc.addTerm_mono t).terms, (hc.addTerm_mono t).rows, (hc.addTerm_mono t).eqs⟩
    · simpa using hsig
    · simp [henv]
  | @union e₁ e₂ t₁ t₂ h₁ h₂ =>
    refine ⟨D.addEq t₁ t₂, .union (Expr.MEval.mono hc hsig (henv ▸ h₁))
      (Expr.MEval.mono hc hsig (henv ▸ h₂)), hc.addEq_mono t₁ t₂, ?_, ?_⟩ <;>
      simp [hsig, henv]
  | @set f args out ts vs hargs hout =>
    refine ⟨D.addRow f ts vs, .set (Expr.MEvalList.mono hc hsig (henv ▸ hargs))
      (Expr.MEvalList.mono hc hsig (henv ▸ hout)), hc.addRow_mono f ts vs, ?_, ?_⟩ <;>
      simp [hsig, henv]

/-- `Database.ActionStep.mono` over a block: each step re-bases onto the previous one's
larger result. -/
theorem Database.ActionsStep.mono {db D d : Database} (hc : db.Contained D)
    (hsig : db.sig = D.sig) (henv : db.env = D.env) {as : List Action}
    (h : Database.ActionsStep db as d) :
    ∃ D', Database.ActionsStep D as D' ∧ d.Contained D' ∧ d.sig = D'.sig ∧
      d.env = D'.env := by
  induction h generalizing D with
  | nil => exact ⟨D, .nil, hc, hsig, henv⟩
  | @cons db₀ d₀ d₁ a as ha _ ih =>
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀⟩ := ha.mono hc hsig henv
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁⟩ := ih hc₀ hs₀ he₀
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁⟩

/-- **A merge collision available at `A` is available at any `C` containing it.**

No `env`/`rules` hypothesis is needed: a `MergeStep` overwrites the environment with
`mergeEnv a b` before running the body and restores the caller's `env`/`rules`
afterwards, so neither field is ever read. `sig` is needed, because `MCongList.mono` is.
-/
theorem MergeStep.transport {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (h : MergeStep A B) : ∃ D, MergeStep C D ∧ B.Contained D ∧ B.sig = D.sig := by
  cases h with
  | @collide dA f as bs a b vs body res hra hrb hcong hm hbody hres =>
    have hc0 : ({ A with env := mergeEnv a b } : Database).Contained
        { C with env := mergeEnv a b } := ⟨hc.terms, hc.rows, hc.eqs⟩
    obtain ⟨dC, hstepC, hcont, hsig', henv'⟩ := hbody.mono hc0 hsig rfl
    refine ⟨{ dC.addRow f as vs with env := C.env, rules := C.rules },
      .collide (hc.rows hra) (hc.rows hrb) (MCongList.mono hc hsig hcong)
        (by rw [← hsig]; exact hm) hstepC
        (Expr.MEvalList.mono hcont hsig' (henv' ▸ hres)), ?_, ?_⟩
    · exact ⟨(hcont.addRow_mono f as vs).terms, (hcont.addRow_mono f as vs).rows,
        (hcont.addRow_mono f as vs).eqs⟩
    · simpa using hsig'

/-- `MergeStep.transport` iterated: a closure from `A` re-bases onto one from any `C`
containing `A`. This is the composition step of `mergeSaturateF_contained`. -/
theorem MergeClosure.transport {A C B : Database} (hc : A.Contained C)
    (hsig : A.sig = C.sig) (h : MergeClosure A B) :
    ∃ D, MergeClosure C D ∧ B.Contained D ∧ B.sig = D.sig := by
  induction h with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, hc, hsig⟩
  | tail _ hstep ih =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ := ih
    obtain ⟨D', hstepD', hcont', hsig'⟩ := hstep.transport hcontD hsigD
    exact ⟨D', hclD.tail hstepD', hcont', hsig'⟩

/-! ### The interpreter

`Impl/Merge.lean` runs the M9 semantics. The refinement is weaker than M10's on purpose:
the spec admits several results, so the interpreter's is one of them rather than *the*
one. -/
/-- **The M9 refinement: reachability, not equality.**

`exec_toDatabase` says the constructor interpreter computes exactly `run p`. Here the
spec is a relation, so the statement is that the interpreter lands on a state the spec
reaches. Nothing stronger is available, and nothing stronger is wanted — pinning a
single result would mean pinning the merge order, which is the thing `MERGE.md` argues
the semantics should decline to pin.

**False as stated**, for the reason `Expr.MEval_of_eval'` exists: `exec` is
`Impl/Interp.lean`'s constructor interpreter and evaluates with `Expr.eval`, which
builds an application for *every* name.

* `p = [.action (.expr (.app "ordering-min" [1, 2]))]` — `exec` adds the term
  `ordering-min 1 2`; `MEval.prim` gives `1`, so `ActionStep` adds `1` instead and the
  two states differ.
* `p = [.decl "g" ⟨1, 1, .noMerge⟩, .action (.expr (.app "g" [1]))]` — `exec` adds the
  term `g 1`; `MEval` has only `lookup` for `g`, which needs a row, so no `ActionStep`
  exists at all and no `ProgramStep` relates the two.

Both are repaired by hypotheses: the program declares nothing but constructors, and no
`Expr` in it names a primitive (`Expr.NoPrim`). Under those, the proof is the whole
`runProgram → ProgramStep` bridge — `evalAction → ActionStep` via
`Expr.MEval_of_eval'`, `ValidSubst → MValidSubst` via `mcong_iff_cong`, then
`stepCmd`/`runProgram`. The e-matching step needs `db.CtorRows` at every intermediate
state, i.e. the `CtorRows` preservation lemmas being added to `Proofs/Database.lean` and
`Proofs/Step.lean`, so this is blocked on those rather than merely long. -/
theorem execM_reachable {p : Program} {d : FDatabase} (h : exec p = some d) :
    ProgramStep FDatabase.empty.toDatabase p d.toDatabase := by
  sorry

/-! ### The contract for `execM`: containment, not reachability

`execM_reachable`'s shape is unavailable for `execM`, and not because it is hard —
because it is **false**. The implementation's merge phase deletes the rows it merged and
the specification never deletes, so no `ProgramStep` state equals the implementation's:
a spec run that performed the same merges still holds the two originals, and a spec run
that performed none holds no combined row. `execM_reachable` above survives only because
`exec` is `Impl/Interp.lean`'s constructor interpreter, which has no merge phase at all
(`FDatabase.mergeRound_eq_self` and `hasMergeRow_eq_false`) — the layering is intact.

What replaces it is that the implementation's state is *contained* in one the spec
reaches: the implementation may find **fewer** results, never more. That is the safe
direction, because everything the M11 safety theorem reads is positive in the state, so
safety transfers downward. `MValidSubst.mono` is the step that makes "fewer rows" mean
"fewer matches" rather than merely "a different database".

The deletion adds one obligation on top of the plain refinement — that the witness `db`
can be chosen to have performed *at least* the merges the implementation did — which is
where `MergeClosure`'s freedom to take any number of steps is spent.

#### The refinement chain

A step-by-step account of the merge interpreter against the merge specification. It runs
from `Inv` preservation through evaluation, actions and matching to containment, and it
is proved all the way to `execM_contained`. What is left over is
`execM_current_of_lattice`, which wants more than containment.

`execCmdM_contained` was once false, and the defect was in the *specification*:
`CmdStep.action` had no merge phase and `execCmdM` runs one, so the interpreter reached a
state holding a merge result no `CmdStep` state held. `CmdStep.action` now carries a
`MergeClosure`, which is what egglog does — a bare top-level action is compiled into a
one-rule run and every rule-set run ends in `merge_all`.

The chain has one prerequisite that is not obvious, and it is why `Cong.toMCong'` exists.
`FDatabase.patternHoldsM` compares keys with `congrKeys d.closureF`, and `closureF`
computes **`Cong`** — it closes over `eqsF` and `congrPair`, with no notion of a row. The
specification's row atom compares them with **`MCong`**. So every read the interpreter
performs has to be re-read as a specification read, and that is exactly `Cong.toMCong'`:
`CtorTerms` and `RowsComplete` are what license it, and unlike `CtorRows` they survive a
`:merge` declaration.

Hence `Inv`, which is what the induction actually carries. Prove its preservation lemmas
first; the rest of the chain is structural recursion once they are available. -/

/-- A term built only from constructor applications.

`CtorTerms` says the database holds only such terms; this is the same condition on one
term, which is what the operations that *insert* a term have to be given. -/
def Term.CtorTerm (sig : Signature) (t : Term) : Prop :=
  ∀ f as, Term.app f as ∈ t.subterms → sig.mergeOf f = MergeSpec.union

/-- The invariant the refinement chain carries.

`wf` is what `mem_closureF_iff_of_wf` needs; `ctorTerms` and `rowsComplete` are what
`Cong.toMCong'` needs; `rowsWF` says a row talks only about terms the database holds, and
`ctorRows` is `closureF_ok`'s `hrow`. All five hold of `FDatabase.empty`.

The last two are not decoration. `ctorRows` is the reverse inclusion `RowsComplete` omits,
restricted to the `.union` functions where it survives a `:merge` declaration, and
`Action.SetLegal` is what preserves it. `rowsWF` was what kept `execExpr`'s lookup branch
inside the constructor fragment; with reading confined to the query it is no longer load
bearing for `execAction`, and is kept because it is the row half of `WF` and
`mergeOneWith` re-establishes it. -/
structure FDatabase.Inv (d : FDatabase) : Prop where
  wf : d.WF
  ctorTerms : d.toDatabase.CtorTerms
  rowsComplete : d.toDatabase.RowsComplete
  rowsWF : d.toDatabase.RowsWF
  ctorRows : ∀ r ∈ d.toDatabase.rows, d.sig.mergeOf r.fn = MergeSpec.union →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.toDatabase.terms

/-- The `sig`/`terms`/`rows` half of `FDatabase.Inv`, on a spec database. Everything but
`wf` constrains only those three fields, so it is proved once here and transported through
the `toDatabase_*` bridges. -/
structure Database.Inv0 (db : Database) : Prop where
  ctorTerms : db.CtorTerms
  rowsComplete : db.RowsComplete
  rowsWF : db.RowsWF
  ctorRows : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
    r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms

namespace Database

/-- Every listed term is held by `addTerms`. -/
theorem mem_terms_addTerms {db : Database} {ts : List Term} {t : Term} (h : t ∈ ts) :
    t ∈ (db.addTerms ts).terms := by
  induction ts generalizing db with
  | nil => simp at h
  | cons s ts ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact (Contained.addTerms ts (db.addTerm t)).terms (Or.inr t.self_mem_subterms)
    · exact ih h'

namespace Inv0

theorem addTerm {db : Database} (h : db.Inv0) {t : Term}
    (ht : Term.CtorTerm db.sig t) : (db.addTerm t).Inv0 where
  ctorTerms := by
    rintro f as (hm | hm)
    · exact h.ctorTerms f as hm
    · exact ht f as hm
  rowsComplete := by
    rintro r ⟨hout, hm | hm⟩
    · exact Or.inl (h.rowsComplete ⟨hout, hm⟩)
    · exact Or.inr ⟨hout, hm⟩
  rowsWF := by
    rintro r (hr | ⟨hout, hm⟩)
    · exact ⟨fun a ha => Or.inl ((h.rowsWF r hr).1 a ha),
        fun v hv => Or.inl ((h.rowsWF r hr).2 v hv)⟩
    · refine ⟨fun a ha => Or.inr ?_, ?_⟩
      · exact Term.subterms_subset_of_mem hm (Term.IsSubterm.arg ha (Term.IsSubterm.refl a))
      · intro v hv
        rw [hout] at hv
        rcases List.mem_singleton.mp hv with rfl
        exact Or.inr hm
  ctorRows := by
    rintro r (hr | ⟨hout, hm⟩) hf
    · exact ⟨(h.ctorRows r hr hf).1, Or.inl (h.ctorRows r hr hf).2⟩
    · exact ⟨hout, Or.inr hm⟩

theorem addTerms {db : Database} (h : db.Inv0) {ts : List Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm db.sig t) : (db.addTerms ts).Inv0 := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih =>
    exact ih (h.addTerm (hts t (by simp))) fun s hs => hts s (by simp [hs])

theorem addEq {db : Database} (h : db.Inv0) {a b : Term}
    (ha : Term.CtorTerm db.sig a) (hb : Term.CtorTerm db.sig b) : (db.addEq a b).Inv0 :=
  let h' := (h.addTerm ha).addTerm hb
  ⟨h'.ctorTerms, h'.rowsComplete, h'.rowsWF, h'.ctorRows⟩

theorem addRow {db : Database} (h : db.Inv0) {f : FnName} {as vs : List Term}
    (hf : db.sig.mergeOf f ≠ MergeSpec.union)
    (has : ∀ a ∈ as, Term.CtorTerm db.sig a) (hvs : ∀ v ∈ vs, Term.CtorTerm db.sig v) :
    (db.addRow f as vs).Inv0 := by
  have h' : ((db.addTerms as).addTerms vs).Inv0 :=
    (h.addTerms has).addTerms (by simpa using hvs)
  refine ⟨h'.ctorTerms, h'.rowsComplete.trans (Set.subset_insert _ _), ?_, ?_⟩
  · rintro r (rfl | hr)
    · exact ⟨fun a ha => Contained.addTerms vs _ |>.terms (mem_terms_addTerms ha),
        fun v hv => mem_terms_addTerms hv⟩
    · exact h'.rowsWF r hr
  · rintro r (rfl | hr) hmf
    · exact absurd (by simpa using hmf) hf
    · exact h'.ctorRows r hr hmf

end Inv0
end Database

namespace FDatabase

theorem Inv.toInv0 {d : FDatabase} (h : d.Inv) : d.toDatabase.Inv0 :=
  ⟨h.ctorTerms, h.rowsComplete, h.rowsWF, h.ctorRows⟩

theorem Inv.of_inv0 {d : FDatabase} (hw : d.WF) (h : d.toDatabase.Inv0) : d.Inv :=
  ⟨hw, h.ctorTerms, h.rowsComplete, h.rowsWF, h.ctorRows⟩

/-- The `addRow` companion to `WF.addTerm` and `WF.addEq`. -/
theorem WF.addRow {d : FDatabase} (h : d.WF) (f : FnName) (as vs : List Term) :
    (d.addRow f as vs).WF := by
  show (d.addRow f as vs).toDatabase.WF
  rw [toDatabase_addRow]
  exact Database.WF.addRow h f as vs

end FDatabase

theorem FDatabase.Inv.empty : FDatabase.empty.Inv := by
  refine ⟨FDatabase.empty_wf, ?_, ?_, ?_, ?_⟩ <;>
    simp [FDatabase.empty, FDatabase.toDatabase, Database.CtorTerms, Database.RowsComplete,
      Database.RowsWF, Database.ctorRowsOf]

/-- `addTerm` takes an arbitrary `Term`, so it needs `ht`: inserting an application of a
`:merge` function would put a non-constructor into `terms` and break `ctorTerms`. -/
theorem FDatabase.Inv.addTerm {d : FDatabase} (h : d.Inv) {t : Term}
    (ht : Term.CtorTerm d.sig t) : (d.addTerm t).Inv := by
  refine Inv.of_inv0 (h.wf.addTerm t) ?_
  rw [toDatabase_addTerm]
  exact h.toInv0.addTerm ht

theorem FDatabase.Inv.addEq {d : FDatabase} (h : d.Inv) {a b : Term}
    (ha : Term.CtorTerm d.sig a) (hb : Term.CtorTerm d.sig b) : (d.addEq a b).Inv := by
  refine Inv.of_inv0 (h.wf.addEq a b) ?_
  rw [toDatabase_addEq]
  exact h.toInv0.addEq ha hb

/-- `hf` is what keeps `ctorRows` true — a `set` on a constructor would add a row of a
`.union` function that is not that function's constructor row, which is exactly what
`Action.SetLegal` rules out. `has`/`hvs` are `addTerm`'s condition on the operands. -/
theorem FDatabase.Inv.addRow {d : FDatabase} (h : d.Inv) {f : FnName} {as vs : List Term}
    (hf : d.sig.mergeOf f ≠ MergeSpec.union)
    (has : ∀ x ∈ as, Term.CtorTerm d.sig x) (hvs : ∀ x ∈ vs, Term.CtorTerm d.sig x) :
    (d.addRow f as vs).Inv := by
  refine Inv.of_inv0 (h.wf.addRow f as vs) ?_
  rw [toDatabase_addRow]
  exact h.toInv0.addRow hf has hvs

/-- Every term the database holds is constructor-built: `subtermClosed` pushes the
application into `terms`, where `ctorTerms` reads it off. -/
theorem FDatabase.Inv.ctorTerm_of_mem {d : FDatabase} (h : d.Inv) {t : Term}
    (ht : t ∈ d.toDatabase.terms) : Term.CtorTerm d.sig t :=
  fun _ _ hsub => h.ctorTerms _ _ (h.wf.subtermClosed t ht hsub)

/-- The environment holds only constructor terms, since `WF.envInTerms` puts its values in
`terms`. -/
theorem FDatabase.Inv.env_ctorTerm {d : FDatabase} (h : d.Inv) :
    ∀ b ∈ d.env, Term.CtorTerm d.sig b.2 :=
  fun b hb => h.ctorTerm_of_mem (h.wf.envInTerms b hb)

/-- A literal mentions no application. -/
theorem Term.ctorTerm_lit {sig : Signature} {l : Lit} : Term.CtorTerm sig (.lit l) := by
  intro f as hsub
  rw [Term.subterms_lit] at hsub
  exact absurd hsub (by simp)

/-- A primitive returns one of its operands or a fresh literal, so it cannot introduce a
non-constructor application. -/
theorem Prim.apply_ctorTerm {sig : Signature} {p : Prim} {ts : List Term} {v : Term}
    (hts : ∀ t ∈ ts, Term.CtorTerm sig t) (h : p.apply ts = some v) :
    Term.CtorTerm sig v := by
  unfold Prim.apply at h
  split at h
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMin
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h
    subst h
    unfold Term.orderingMax
    split
    · exact hts _ (by simp)
    · exact hts _ (by simp)
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · simp only [Option.some_inj] at h; subst h; exact Term.ctorTerm_lit
  · exact absurd h (by simp)

mutual

/-- **The merge interpreter only ever builds constructor terms.**

Each branch that produces a term stays inside the constructor fragment: the `.union`
branch's head is a constructor by the guard it just tested, and a primitive returns an
operand or a literal. Nothing reads a row, so no case has to place a recorded output back
in `terms`. This is what `Inv.execAction` needs. -/
theorem FDatabase.execExpr_ctorTerm {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm d.sig b.2) {e : Expr} {t : Term}
    (hs : d.execExpr σ e = some t) : Term.CtorTerm d.sig t := by
  match e with
  | .lit l =>
    simp only [FDatabase.execExpr, Option.some_inj] at hs
    subst hs; exact Term.ctorTerm_lit
  | .var v =>
    simp only [FDatabase.execExpr] at hs
    exact hσ (v, t) (Env.mem_of_lookup hs)
  | .app f args =>
    simp only [FDatabase.execExpr, Option.bind_eq_some_iff] at hs
    obtain ⟨ts, hts, hrest⟩ := hs
    have hts' : ∀ x ∈ ts, Term.CtorTerm d.sig x :=
      FDatabase.execExprList_ctorTerm h hσ hts
    split at hrest
    · exact Prim.apply_ctorTerm hts' hrest
    · rename_i hprim
      split at hrest
      · rename_i hu
        simp only [Option.some_inj] at hrest
        subst hrest
        intro g bs hsub
        rw [Term.subterms_app] at hsub
        rcases Set.mem_insert_iff.mp hsub with heq | hmem
        · obtain ⟨rfl, rfl⟩ := Term.app.injEq .. ▸ heq
          exact hu
        · obtain ⟨x, hx, hxs⟩ := Set.mem_iUnion₂.mp hmem
          exact hts' x hx g bs hxs
      · exact absurd hrest (by simp)

theorem FDatabase.execExprList_ctorTerm {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, Term.CtorTerm d.sig b.2) {es : List Expr} {ts : List Term}
    (hs : d.execExprList σ es = some ts) : ∀ t ∈ ts, Term.CtorTerm d.sig t := by
  match es with
  | [] =>
    simp only [FDatabase.execExprList, Option.some_inj] at hs
    subst hs; simp
  | e :: es =>
    simp only [FDatabase.execExprList, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rest, hrest, rfl⟩ := hs
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact FDatabase.execExpr_ctorTerm h hσ ht
    · exact FDatabase.execExprList_ctorTerm h hσ hrest x hx

end

theorem FDatabase.Inv.execAction {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hlegal : a.SetLegal d.sig) (hs : d.execAction a = some d') : d'.Inv := by
  match a with
  | .expr e =>
    simp only [FDatabase.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact h.addTerm (FDatabase.execExpr_ctorTerm h h.env_ctorTerm ht)
  | .letBind v e =>
    simp only [FDatabase.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hbase := h.addTerm (FDatabase.execExpr_ctorTerm h h.env_ctorTerm ht)
    refine ⟨⟨hbase.wf.subtermClosed, hbase.wf.eqsInTerms, ?_⟩, hbase.ctorTerms,
      hbase.rowsComplete, hbase.rowsWF, hbase.ctorRows⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · have hmem : t ∈ (d.addTerm t).terms := by
        simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
        exact Or.inl ((Term.mem_subtermList t).mpr (Term.IsSubterm.refl t))
      exact hmem
    · exact hbase.wf.envInTerms b hb
  | .union e₁ e₂ =>
    simp only [FDatabase.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hs
    exact h.addEq (FDatabase.execExpr_ctorTerm h h.env_ctorTerm ht₁)
      (FDatabase.execExpr_ctorTerm h h.env_ctorTerm ht₂)
  | .set f args out =>
    simp only [FDatabase.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨ts, hts, vs, hvs, rfl⟩ := hs
    exact h.addRow hlegal (FDatabase.execExprList_ctorTerm h h.env_ctorTerm hts)
      (FDatabase.execExprList_ctorTerm h h.env_ctorTerm hvs)


/-! #### Evaluation -/

mutual

/-- **The interpreter computes the evaluation the specification allows.** One rule per
syntactic form on each side, and no choice on either: `MEval_unique` says the relation is
a function, and this says `execExpr` is that function wherever it is defined. -/
theorem FDatabase.execExpr_MEval {d : FDatabase} (h : d.Inv) {σ : Env} {e : Expr}
    {t : Term} (hs : d.execExpr σ e = some t) : Expr.MEval d.toDatabase σ e t := by
  match e, hs with
  | .lit l, hs =>
    rw [FDatabase.execExpr, Option.some.injEq] at hs
    exact hs ▸ .lit
  | .var v, hs =>
    rw [FDatabase.execExpr] at hs
    exact .var hs
  | .app f args, hs =>
    rw [FDatabase.execExpr] at hs
    obtain ⟨ts, hts, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hl := FDatabase.execExprList_MEvalList h hts
    split at hs
    · next p hp => exact .prim hp hl hs
    · next hp =>
      split at hs
      · next hu =>
        rw [Option.some.injEq] at hs
        exact hs ▸ .ctor hp hu hl
      · exact absurd hs (by simp)

theorem FDatabase.execExprList_MEvalList {d : FDatabase} (h : d.Inv) {σ : Env}
    {es : List Expr} {ts : List Term} (hs : d.execExprList σ es = some ts) :
    Expr.MEvalList d.toDatabase σ es ts := by
  match es, hs with
  | [], hs =>
    rw [FDatabase.execExprList, Option.some.injEq] at hs
    exact hs ▸ .nil
  | e :: es, hs =>
    rw [FDatabase.execExprList] at hs
    obtain ⟨t, ht, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact .cons (FDatabase.execExpr_MEval h ht) (FDatabase.execExprList_MEvalList h hus)

end

/-! #### Actions -/

/-- **`execAction` refines `ActionStep`.** One case per action, each of them
`execExpr_MEval` under the `toDatabase_*` bridge. -/
theorem FDatabase.execAction_ActionStep {d d' : FDatabase} (h : d.Inv) {a : Action}
    (hs : d.execAction a = some d') :
    Database.ActionStep d.toDatabase a d'.toDatabase := by
  match a with
  | .expr e =>
    simp only [FDatabase.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [toDatabase_addTerm]
    exact .expr (FDatabase.execExpr_MEval h ht)
  | .letBind v e =>
    simp only [FDatabase.execAction, Option.map_eq_some_iff] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [toDatabase_setEnv (d := d.addTerm t) (σ := (v, t) :: d.env), toDatabase_addTerm]
    exact .letBind (FDatabase.execExpr_MEval h ht)
  | .union e₁ e₂ =>
    simp only [FDatabase.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hs
    rw [toDatabase_addEq]
    exact .union (FDatabase.execExpr_MEval h ht₁) (FDatabase.execExpr_MEval h ht₂)
  | .set f args out =>
    simp only [FDatabase.execAction, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨ts, hts, vs, hvs, rfl⟩ := hs
    rw [toDatabase_addRow]
    exact .set (FDatabase.execExprList_MEvalList h hts)
      (FDatabase.execExprList_MEvalList h hvs)

/-! `FDatabase.execActions_ActionsStep` is proved at the end of the file, under
"Containment for the merge interpreter": its induction carries `Actions.SetLegal` past
the head of the block with `execAction_sig`, which is stated below. -/

/-! #### Matching -/

/-- Every value visible to `execExpr` under `d.env ++ σ` is a constructor term, given
that `σ`'s values are terms `d` holds. `execExpr_ctorTerm`'s hypothesis, at the
environment `patternHoldsM` evaluates in. -/
theorem FDatabase.envAppend_ctorTerm {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ∀ b ∈ d.env ++ σ, Term.CtorTerm d.sig b.2 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact h.env_ctorTerm b hb
  · exact h.ctorTerm_of_mem (hσ b hb)

/-- **`patternHoldsM` is sound for `MValidSubst`.**

`ValidEnv (p.freeVars d.env) d.toDatabase σ` is load-bearing, not decoration.
`patternHoldsM` reads `σ` only through `d.env ++ σ`, so a `σ` carrying bindings the
pattern never mentions still passes the test, while every `MValidSubst` constructor pins
`Env.dom σ` to a permutation of the pattern's free variables —
`Falsity.patternHoldsM_MValidSubst_false` is the witness. Nothing is lost by requiring
it: it is a *consequence* of the conclusion (`MValidSubst.validEnv`), so this is the
strongest statement whose conclusion can hold, and it is the hypothesis
`Proofs/Interp.lean`'s `patternHolds_iff` already carries.

`Interp.lean`'s `patternHolds_iff`, forward direction, with `execExpr` for `Expr.eval`
and `MValidSubst` for `ValidSubst`. Three gaps to bridge beyond that proof:

* the `.values` case compares with `congrKeys d.closureF`, which computes `Cong`, while
  `MValidSubst.values` wants `MCongList` — `CongList.toMCongList'` closes it, and its
  `CtorTerms`/`RowsComplete` hypotheses are `Inv` fields;
* the `.expr`/`.eq` cases close over the *extended* database `d.addTerm t`, so
  `Cong.toMCong'` is applied at `(d.addTerm t).Inv`, from `Inv.addTerm`;
* `Inv.addTerm` needs the instance to be a constructor term, which is
  `execExpr_ctorTerm`, which in turn needs the `ValidEnv`. -/
theorem FDatabase.patternHoldsM_MValidSubst {d : FDatabase} (h : d.Inv) {p : Pattern}
    {σ : Env} (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ)
    (hs : d.patternHoldsM p σ = true) : MValidSubst d.toDatabase p σ := by
  have hσ := FDatabase.envAppend_ctorTerm h hv.2
  cases p with
  | expr e =>
    rw [FDatabase.patternHoldsM] at hs
    split at hs
    · exact absurd hs (by simp)
    · next t hev =>
      rw [decide_eq_true_eq] at hs
      obtain ⟨w, hwm, hcl⟩ := hs
      have ht : Term.CtorTerm d.sig t := FDatabase.execExpr_ctorTerm h hσ hev
      have hInv := h.addTerm ht
      have hct := hInv.ctorTerms
      have hrc := hInv.rowsComplete
      rw [FDatabase.toDatabase_addTerm] at hct hrc
      exact .expr hv hwm (FDatabase.execExpr_MEval h hev)
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm h.wf).mp hcl))
  | eq e₁ e₂ =>
    rw [FDatabase.patternHoldsM] at hs
    split at hs
    · next t₁ t₂ hev₁ hev₂ =>
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hs
      obtain ⟨heq, w, hwm, hcl⟩ := hs
      have ht₁ : Term.CtorTerm d.sig t₁ := FDatabase.execExpr_ctorTerm h hσ hev₁
      have ht₂ : Term.CtorTerm d.sig t₂ := FDatabase.execExpr_ctorTerm h hσ hev₂
      have hInv := (h.addTerm ht₁).addTerm ht₂
      have hct := hInv.ctorTerms
      have hrc := hInv.rowsComplete
      rw [FDatabase.toDatabase_addTerm, FDatabase.toDatabase_addTerm] at hct hrc
      exact .eq hv hwm (FDatabase.execExpr_MEval h hev₁) (FDatabase.execExpr_MEval h hev₂)
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm₂ h.wf).mp hcl))
        (Cong.toMCong' hct hrc ((FDatabase.mem_closureF_addTerm₂ h.wf).mp heq))
    · exact absurd hs (by simp)
  | values vs f as =>
    rw [FDatabase.patternHoldsM] at hs
    split at hs
    · next us ts hu ht =>
      rw [List.any_eq_true] at hs
      obtain ⟨r, hr, hcond⟩ := hs
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hfn, hkey⟩, hval⟩ := hcond
      subst hfn
      exact .values hv (FDatabase.execExprList_MEvalList h hu)
        (FDatabase.execExprList_MEvalList h ht)
        (CongList.toMCongList' h.ctorTerms h.rowsComplete
          ((FDatabase.congrTuple_iff h.wf).mp hkey))
        (CongList.toMCongList' h.ctorTerms h.rowsComplete
          ((FDatabase.congrTuple_iff h.wf).mp hval))
        hr
    · exact absurd hs (by simp)

/-- The hypothesis `patternHoldsM_MValidSubst` adds is a consequence of its conclusion,
which is why requiring it costs nothing. -/
theorem MValidSubst.validEnv {db : Database} {p : Pattern} {σ : Env}
    (h : MValidSubst db p σ) : ValidEnv (p.freeVars db.env) db σ := by
  cases h with
  | expr hv _ _ _ => exact hv
  | eq hv _ _ _ _ _ => exact hv
  | values hv _ _ _ _ _ => exact hv

/-- **Every substitution the enumerator produces is, up to `Env.Agree`, one
`MValidQuerySubst` admits.**

The `Env.Agree` is forced, and not by the `ValidEnv` defect above. `Query.freeVars`
deduplicates, so `matchQueryM` binds a variable two patterns share exactly **once**;
`MValidQuerySubst` instead demands `Env.UnionAll σs σ`, which is literal
*concatenation* of one substitution per pattern, each binding its own pattern's free
variables. A query with a repeated variable therefore admits no `σ` on the nose — the
lengths cannot match — and `Falsity.matchQueryM_MValidQuerySubst_false` is the witness.
`Proofs/Interp.lean`'s `validQuerySubst_of_mem_matchQuery` already concludes up to
`Env.Agree` for the same reason. -/
theorem FDatabase.matchQueryM_MValidQuerySubst {d : FDatabase} (h : d.Inv) {q : Query}
    {σ : Env} (hs : σ ∈ d.matchQueryM q) :
    ∃ τ, MValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  rw [FDatabase.matchQueryM, List.mem_filter, mem_assignments, List.all_eq_true] at hs
  obtain ⟨⟨hdom, hval⟩, hall⟩ := hs
  have hall' : ∀ p ∈ q, MValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) :=
    fun p hp =>
      FDatabase.patternHoldsM_MValidSubst h (validEnv_canon hp hdom hval) (hall p hp)
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars d.env) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self hall', hu⟩, Env.agree_of_refines hr ?_⟩
  -- `σ` binds only the query's free variables, and each is bound by some restriction
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars d.env) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp

/-! #### The merge phase and the round

These are the two containment steps, and the only places the *witness* has to be chosen
rather than computed. A merge pass deletes, so its result is not a `MergeClosure` state;
the specification state to compare against is one that took at least the same merges, and
`MergeClosure`'s freedom to take any number of steps is what pays for that.

`FDatabase.mergeRound_contained`, `mergeSaturateF_contained` and
`execRunRulesM_contained` are proved at the end of the file, under "Containment for the
merge interpreter": they read `mergeOneWith_inv`, `mergeOneWith_confined`,
`mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv` and `Inv.mergeRound_of_legalMerges`,
all of which are stated below. -/

/-! #### Commands and programs

`FDatabase.execCmdM_contained`, `FDatabase.execProgramM_contained` and `execM_contained`
are proved at the end of the file, under "Containment for a whole program", because they
read the whole chain. What is worth reading here is their **side conditions**, which are
this section's real output:

* a merge body is an action block nothing type-checks — `Cmd.SetLegal (.decl _ _)` is
  `True`, so `Program.SetLegal` says nothing about one, and without
  `Signature.MergesLegal` the accumulator's `Inv` fails at the first body that writes an
  illegal `set` (`Falsity.mergeRound_inv_false`);
* `FDatabase.Inv` does **not** survive an arbitrary declaration — `Falsity.claim1`
  machine-checks that declaring `g` `:merge` after `g ()` is already a term breaks
  `CtorTerms` — so a declaration has to name something the state does not yet mention
  (`FDatabase.Unused`), which is egglog's own "declare before use".

`FDatabase.ProgramLegal` bundles those two with `Cmd.SetLegal` and checks them at the
state each command actually runs in. -/

/-- **Completeness, so containment is not vacuous.**

A do-nothing implementation satisfies `execM_contained`, so containment needs a companion
saying the implementation keeps the *right* row and not merely a subset of the rows. For a
**lattice** merge that is exactly `Database.Current`, which is what `Current` was defined
for — "the single value it has when the merge is a join, used only where a result must
match egglog exactly".

`le` is a parameter rather than an instance because the order is per function and orders
whole rows. `hjoin` says the merge really is a `le`-join: whatever the body computes from
two colliding outputs is an upper bound of both. `hanti` is what makes the greatest
element unique (`Database.current_unique`). For a merge that is *not* a lattice there is no
`Current` to be complete against and nothing is claimed — `MERGE.md`'s "order-dependent
merges are the user's fault".

Unproved. Beyond the refinement `execM_contained` needs, this wants an induction over the
merge phase carrying "every output the specification records at this key class is `le` the
one the implementation holds", whose step is that `mergeOneWith` replaces two rows by
their join and its saturation removes the rest. Deleting the merged rows is what makes
that invariant maintainable at all: while the implementation was append-only it held every
superseded output and the statement was simply false. Estimated 200–300 lines on top of
the refinement, which is why it is stated rather than proved. -/
theorem execM_current_of_lattice {p : Program} {d : FDatabase}
    {le : List Term → List Term → Prop} (hexec : execM p = some d)
    (hanti : ∀ x y, le x y → le y x → x = y)
    (hjoin : ∀ (f : FnName) (body : List Action) (res : List Expr) (a b vs : List Term),
      d.sig.mergeOf f = MergeSpec.merge body res →
      (∃ e, Database.ActionsStep { d.toDatabase with env := mergeEnv a b } body e ∧
        Expr.MEvalList e e.env res vs) → le a vs ∧ le b vs)
    {f : FnName} {as vs : List Term} {body : List Action} {res : List Expr}
    (hmerge : d.sig.mergeOf f = MergeSpec.merge body res)
    (hrow : Row.mk f as vs ∈ d.rows) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ db.Current le f as vs := by
  sorry

/-- The interpreter's merge phase against the specification's.

**False as stated, once the implementation deletes.** `MergeClosure` is
`Relation.ReflTransGen MergeStep` and `MergeStep.contained` says every step only grows the
state, so no `MergeClosure` can reach a database with *fewer* rows — which is exactly what
a pass now produces. The containment form below is what survives, and it is the merge-phase
instance of `execM_contained`.

Stated here with **no** hypothesis, which is why it is still open:
`FDatabase.mergeRound_contained` is this statement under `d.Inv` and `hlegal`, and both
are forced. `mergeOne` gates on `congrKeys d.closureF`, and `closureF` decides `Cong`
only for a well-formed database (`mem_closureF_iff_of_wf`), while `MergeStep` gates on
`MCongList`; and without `hlegal` the accumulator's `Inv` fails at the first merge body
that writes an illegal `set` (`Falsity.mergeRound_inv_false`). What `mergeRound_confined`
gives unconditionally is only that the rows the pass drops are merge rows and nothing
else. -/
theorem mergeRound_closure {d : FDatabase} :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  sorry

/-! #### `mcong_iff_cong` without `CtorRows`

`CtorRows` is an equality of row *sets*, which the interpreter's databases do not
satisfy once a `:merge` function has a row. The two halves it is used for are separated
here so `closureF_ok` can have only the halves that hold. -/
/-- `hrow` in reduced form. Stating it separately is the same trick
`Database.mem_rows_iff` plays: applied to a row *literal* the projections
`{fn := f, args := as, out := vs}.out` do not reduce on their own, and `obtain ⟨rfl, _⟩`
then sees `vs` occurring in its own definition. -/
theorem Database.ctor_row {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {f : FnName} {as vs : List Term} (h : Row.mk f as vs ∈ db.rows)
    (hu : db.sig.mergeOf f = MergeSpec.union) :
    vs = [.app f as] ∧ Term.app f as ∈ db.terms := hrow _ h hu

mutual

/-- `MCong.toCong` needing only that a `.union` function's rows are constructor rows. -/
theorem MCong.toCong_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {a b : Term} (h : MCong db a b) : Cong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (MCong.toCong_of_rows hrow h)
  | .trans h₁ h₂ =>
    exact .trans (MCong.toCong_of_rows hrow h₁) (MCong.toCong_of_rows hrow h₂)
  | .fd hra hrb hu hl hxy =>
    obtain ⟨rfl, hma⟩ := Database.ctor_row hrow hra hu
    obtain ⟨rfl, hmb⟩ := Database.ctor_row hrow hrb hu
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact .congr hma hmb (MCongList.toCongList_of_rows hrow hl)

theorem MCongList.toCongList_of_rows {db : Database}
    (hrow : ∀ r ∈ db.rows, db.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms)
    {as bs : List Term} (h : MCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (MCong.toCong_of_rows hrow hab) (MCongList.toCongList_of_rows hrow hl)

end

mutual

/-- `Cong.toMCong` needing only that every application the database holds is a `.union`
function's and has its constructor row. -/
theorem Cong.toMCong_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {a b : Term} (h : Cong db a b) : MCong db a b := by
  match h with
  | .assert hm => exact .assert hm
  | .refl hm => exact .refl hm
  | .symm h => exact .symm (Cong.toMCong_of_terms hterm hunion h)
  | .trans h₁ h₂ =>
    exact .trans (Cong.toMCong_of_terms hterm hunion h₁)
      (Cong.toMCong_of_terms hterm hunion h₂)
  | .congr (f := f) (as := as) (bs := bs) hma hmb hl =>
    exact .fd (a := [Term.app f as]) (b := [Term.app f bs]) (hterm f as hma)
      (hterm f bs hmb) (hunion f as hma)
      (CongList.toMCongList_of_terms hterm hunion hl) (by simp)

theorem CongList.toMCongList_of_terms {db : Database}
    (hterm : ∀ f as, Term.app f as ∈ db.terms → Row.mk f as [.app f as] ∈ db.rows)
    (hunion : ∀ f as, Term.app f as ∈ db.terms → db.sig.mergeOf f = MergeSpec.union)
    {as bs : List Term} (h : CongList db as bs) : MCongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons hab hl =>
    exact .cons (Cong.toMCong_of_terms hterm hunion hab)
      (CongList.toMCongList_of_terms hterm hunion hl)

end

/-- **The congruence closure needs no `fd` disjunct.**

`MCong.fd` fires only at a `.union` function, and in a database the interpreter builds a
`.union` function's rows are exactly the constructor rows of its terms — the two
hypotheses. So `MCong` coincides with `Cong` on the row-free projection, and
`Impl/Closure.lean`'s `closure` decides it unchanged. This is what licenses
`FDatabase.closureF` reusing `closureTotal`.

`hunion` is an **added hypothesis** and the `←` direction is false without it: with
`sig g = .merge …`, terms `g x`, `g y` and an asserted `x = y`, `Cong` relates
`g x` and `g y` by `congr` while `MCong` has no rule that can — `fd` fires only at
`.union`. It says what `Impl/Merge.lean`'s comment means by "every declared function is
`.merge` or `.noMerge`": a `:merge` function's application is never itself a term,
because `execExpr` resolves it to its recorded output. -/
theorem FDatabase.closureF_ok {d : FDatabase}
    (hrow : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union →
      r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ d.terms)
    (hterm : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union →
      Row.mk f as [.app f as] ∈ d.rows)
    (hunion : ∀ f as, Term.app f as ∈ d.terms → d.sig.mergeOf f = MergeSpec.union)
    {a b : Term} : MCong d.toDatabase a b ↔ Cong d.toDatabase a b :=
  ⟨MCong.toCong_of_rows hrow,
    Cong.toMCong_of_terms (fun f as h => hterm f as h (hunion f as h)) hunion⟩

/-! ### The implementation deletes, the specification does not

`Spec/` is append-only and stays so: the M11 safety theorem is an invariant over
`MergeStep`, which needs neither termination nor confluence exactly because nothing is
removed, and the encoding depends on the same property to let proofs refer to terms after
they leave the e-graph. `Impl/Merge.lean`'s merge phase does **not** stay append-only,
because egglog's merge replaces the row: an append-only reference implementation is
faithful to our spec and unfaithful to the system the spec models.

So the contract between them weakens from an equality to a **containment**, which is the
safe direction — everything M11 reads is positive in the state, so an implementation that
finds fewer results cannot make a safety claim false. Two theorems carry that:
`FDatabase.mergeRound_confined`, that deletion touches nothing it must not, and
`MValidSubst.mono`, that fewer rows really do mean fewer matches. -/
namespace FDatabase

@[simp] theorem addTerms_sig {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).sig = d.sig := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_sig {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).sig = d.sig := by
  show ((d.addTerms as).addTerms vs).sig = d.sig
  rw [addTerms_sig, addTerms_sig]

/-- The interpreter's actions only add, so the only thing that ever removes a row is the
merge phase. `Database.ActionStep.contained` read through `toDatabase`. -/
theorem execAction_contained {d e : FDatabase} {a : Action}
    (h : d.execAction a = some e) : d.toDatabase.Contained e.toDatabase := by
  cases a with
  | expr e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      rw [toDatabase_addTerm]
      exact Database.Contained.addTerm t d.toDatabase
  | letBind v e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => hx⟩
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
      · exact List.mem_dedup.mpr (List.mem_append_right _ hx)
  | union e₁ e₂ =>
    cases hv₁ : d.execExpr d.env e₁ with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : d.execExpr d.env e₂ with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addEq]
        exact Database.Contained.addEq t₁ t₂ d.toDatabase
  | set f args out =>
    cases hv₁ : d.execExprList d.env args with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : d.execExprList d.env out with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        subst h
        rw [toDatabase_addRow]
        exact Database.Contained.addRow f ts vs d.toDatabase

/-- The interpreter's actions do not touch the signature either, so which functions are
`.merge` functions is stable across a merge pass. -/
theorem execAction_sig {d e : FDatabase} {a : Action} (h : d.execAction a = some e) :
    e.sig = d.sig := by
  cases a with
  | expr e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | letBind v e₀ =>
    cases hv : d.execExpr d.env e₀ with
    | none => rw [FDatabase.execAction, hv] at h; simp at h
    | some t =>
      rw [FDatabase.execAction, hv, Option.map_some, Option.some.injEq] at h
      exact h ▸ rfl
  | union e₁ e₂ =>
    cases hv₁ : d.execExpr d.env e₁ with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some t₁ =>
      cases hv₂ : d.execExpr d.env e₂ with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some t₂ =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ rfl
  | set f args out =>
    cases hv₁ : d.execExprList d.env args with
    | none => rw [FDatabase.execAction, hv₁] at h; simp at h
    | some ts =>
      cases hv₂ : d.execExprList d.env out with
      | none => rw [FDatabase.execAction, hv₁, hv₂] at h; simp at h
      | some vs =>
        rw [FDatabase.execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact h ▸ addRow_sig

theorem execActions_contained {d e : FDatabase} {as : List Action}
    (h : d.execActions as = some e) : d.toDatabase.Contained e.toDatabase := by
  induction as generalizing d with
  | nil =>
    rw [FDatabase.execActions, Option.some.injEq] at h
    exact h ▸ Database.Contained.refl _
  | cons a as ih =>
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at h; simp at h
    | some d' =>
      rw [FDatabase.execActions, hv, Option.bind_some] at h
      exact (execAction_contained hv).trans (ih h)

theorem execActions_sig {d e : FDatabase} {as : List Action}
    (h : d.execActions as = some e) : e.sig = d.sig := by
  induction as generalizing d with
  | nil => rw [FDatabase.execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at h; simp at h
    | some d' =>
      rw [FDatabase.execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_sig hv)

/-- `addRow` only adds, at the interpreter level. -/
theorem contained_addRow {d : FDatabase} {f : FnName} {as vs : List Term} :
    d.toDatabase.Contained (d.addRow f as vs).toDatabase := by
  rw [toDatabase_addRow]; exact Database.Contained.addRow f as vs d.toDatabase

/-- **One merge firing removes nothing it must not.**

The three prohibitions of the design, discharged: a merge deletes no term, no equality,
and no row of a function that is not the `.merge` function being merged. The last covers
both `.union` — constructor rows, which `Database.CtorRows` and the whole congruence
argument rest on — and `.noMerge`, which is how the proof encoding declares its proof
nodes, so deleting one would delete a proof.

The reason it holds is one line: the only rows filtered are `r₁` and `r₂` themselves,
whose function is `r₁.fn`, and the branch was taken only because
`d.sig.mergeOf r₁.fn = .merge body res`. A row of any other kind of function is therefore
distinct from both. -/
theorem mergeOneWith_confined {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) :
    d.toDatabase.terms ⊆ e.toDatabase.terms ∧ d.toDatabase.eqs ⊆ e.toDatabase.eqs ∧
      e.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ e.rows := by
  unfold FDatabase.mergeOneWith at h
  cases hm : d.sig.mergeOf r₁.fn with
  | union => rw [hm] at h; simp at h
  | noMerge => rw [hm] at h; simp at h
  | merge body res =>
    rw [hm] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue hcond =>
      cases hb : FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body with
      | none => rw [hb] at h; simp at h
      | some eb =>
        rw [hb, Option.bind_some] at h
        cases hv : eb.execExprList eb.env res with
        | none => rw [hv] at h; simp at h
        | some vs =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          subst h
          have hcb := execActions_contained hb
          have hsb := execActions_sig hb
          set e' : FDatabase :=
            { eb with rows := eb.rows.filter fun r => r ≠ r₁ && r ≠ r₂ } with he'
          have hadd := contained_addRow (d := e') (f := r₁.fn) (as := r₁.args) (vs := vs)
          refine ⟨fun x hx => hadd.terms (hcb.terms hx), fun q hq => hadd.eqs (hcb.eqs hq),
            ?_, fun r hr hnm => hadd.rows ?_⟩
          · show ((e'.addTerms r₁.args).addTerms vs).sig = d.sig
            rw [addTerms_sig, addTerms_sig]; exact hsb
          · have hrb : r ∈ eb.rows := hcb.rows hr
            have hfn : r₁.fn = r₂.fn := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              exact hcond.1.1.1
            have hne : r ≠ r₁ ∧ r ≠ r₂ := by
              refine ⟨fun hq => hnm body res ?_, fun hq => hnm body res ?_⟩
              · rw [hq]; exact hm
              · rw [hq, ← hfn]; exact hm
            show r ∈ e'.rows
            rw [he']
            exact List.mem_filter.mpr ⟨hrb, by simp [hne.1, hne.2]⟩

/-- **A merge pass removes nothing it must not.** `mergeOneWith_confined` through the two
folds. This is the formal content of "`Impl/` deletes merge rows only". -/
theorem mergeRound_confined {d : FDatabase} :
    d.toDatabase.terms ⊆ d.mergeRound.toDatabase.terms ∧
      d.toDatabase.eqs ⊆ d.mergeRound.toDatabase.eqs ∧ d.mergeRound.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) →
        r ∈ d.mergeRound.rows := by
  -- The invariant is exactly the conclusion, relative to the fixed starting database.
  let P : FDatabase → Prop := fun x =>
    d.toDatabase.terms ⊆ x.toDatabase.terms ∧ d.toDatabase.eqs ⊆ x.toDatabase.eqs ∧
      x.sig = d.sig ∧
      ∀ r ∈ d.rows, (∀ body res, d.sig.mergeOf r.fn ≠ MergeSpec.merge body res) → r ∈ x.rows
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      obtain ⟨ht, hq, hs, hr⟩ := mergeOneWith_confined hy
      refine ⟨hx.1.trans ht, hx.2.1.trans hq, hs.trans hx.2.2.1, fun r hrd hnm => ?_⟩
      exact hr r (hx.2.2.2 r hrd hnm) (by rw [hx.2.2.1]; exact hnm)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hb : r₁ == r₂
      · simpa [hb] using hx
      · simpa [hb] using hstep x r₁ r₂ hx
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d := ⟨subset_rfl, subset_rfl, rfl, fun r hr _ => hr⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter d.rows d hinit

/-- **On the constructor fragment nothing is deleted, because nothing merges.** With every
function a constructor no row belongs to a `.merge` function, `hasMergeRow` is false and
the pass is the identity — which is why `Impl/Interp.lean`'s `exec` and the equality
`exec_toDatabase` are untouched by any of this. -/
theorem hasMergeRow_eq_false {d : FDatabase} (hsig : d.sig.AllConstructors) :
    d.hasMergeRow = false := by
  simp only [FDatabase.hasMergeRow, List.any_eq_false]
  intro r _
  rw [Signature.mergeOf_eq_union hsig]
  simp

theorem mergeRound_eq_self {d : FDatabase} (h : d.hasMergeRow = false) :
    d.mergeRound = d := by
  unfold FDatabase.mergeRound
  simp [h]

theorem mergeSaturateF_eq_self {d : FDatabase} (h : d.hasMergeRow = false) {n : Nat} :
    FDatabase.mergeSaturateF n d = some d := by
  have hs : d.settled = true := by
    simp [FDatabase.settled, mergeRound_eq_self h]
  cases n <;> simp [FDatabase.mergeSaturateF, hs]

end FDatabase

/-- **Row counts do not observe the merge phase.**

`rowCount` counts congruence classes of *keys*. A merge step writes its combined row at a
key already present, and a merge with an empty action block writes nothing else, so a
merge pass leaves every count alone.

This is what lets the differential test compare row counts while the interpreter runs
only one merge pass instead of saturating — and it is also why keeping every superseded
output, the over-approximation the design rests on, does not inflate the number: three
recorded values at one key are still one row. Both halves of `PLAN.md`'s row-count oracle
survive into M9 because of it.

**False as stated.** `hpure` bounds the merge's *action block* but not its *result*, and
`FDatabase.addRow` inserts the result's terms together with their constructor rows —
so a merge whose result builds an application adds a key class to a *different*
function's table. Counterexample, with `k` any term:

```
d.sig  = fun n => if n = "f" then some ⟨1, 1, .merge [] [.app "F" [.var "old"]]⟩ else none
d.terms = [k],  d.rows = [⟨"f", [k], [k]⟩],  d.eqs = []
```

`hpure` holds (the only block is `[]`). The row collides with itself — `MCongList` is
reflexive and `closureF` has `(k, k)` — so `mergeRound` fires, the result evaluates to
`F k`, and `addRow "f" [k] [F k]` writes the constructor row `⟨F, [k], [F k]⟩`. Then
`d.mergeRound.keyRowCount "F" = 1` while `d.keyRowCount "F" = 0`.

The theorem the difftest actually relies on is the same statement with `hpure`
strengthened to "the merge result is a term the database already holds" — under which
`addRow` adds no key class anywhere, which is the argument the docstring gives. Every
generated merge case satisfies it (results are `i64` literals). -/
theorem FDatabase.mergeRound_rowCount {d : FDatabase} (f : FnName)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
    d.mergeRound.keyRowCount f = d.keyRowCount f := by
  sorry

/-! ### Well-formedness -/
/-- Every binding a merge body's environment provides is one of the two colliding rows'
outputs. This is what `MergeStep.wf` needs `RowsWF` for: `WF.envInTerms` has to hold of
`mergeEnv a b` before the body runs. -/
theorem mem_mergeEnvIdx {i : Nat} {os ns : List Term} {p : Var × Term}
    (h : p ∈ mergeEnvIdx i os ns) : p.2 ∈ os ∨ p.2 ∈ ns := by
  induction os generalizing i ns with
  | nil => simp [mergeEnvIdx] at h
  | cons o os ih =>
    cases ns with
    | nil => simp [mergeEnvIdx] at h
    | cons n ns =>
      simp only [mergeEnvIdx, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih h).imp (fun hm => by simp [hm]) fun hm => by simp [hm]

theorem mem_mergeEnv {os ns : List Term} {p : Var × Term} (h : p ∈ mergeEnv os ns) :
    p.2 ∈ os ∨ p.2 ∈ ns := by
  unfold mergeEnv at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · exact mem_mergeEnvIdx h

/-! #### The merge phase

`mergeRound` does **not** preserve `Inv` unconditionally. A merge body is an arbitrary
`List Action` carrying no `Action.SetLegal` obligation, so a `(set (F) ...)` inside one, on
a constructor `F`, writes a `.union` function's row whose output is not `[.app F args]` —
which is exactly what `ctorRows` forbids. `mergeRound_inv_false` in the counterexample
section machine-checks it. `CtorTerms` *is* preserved, as the `Inv` docstring claims:
`execExpr` builds an application only under a `.union` guard, and every other branch
returns an operand, a literal, or a recorded row output that `rowsWF` already places in
`terms`.

The hypothesis below is the repair: every declared merge's body obeys the same `set`
discipline every other action block obeys. The gap it patches is in the specification —
`Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about merge
bodies. -/

namespace FDatabase

theorem Inv.setEnv {d : FDatabase} (h : d.Inv) {σ : Env}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ } : FDatabase).Inv :=
  ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, hσ⟩, h.ctorTerms, h.rowsComplete, h.rowsWF,
    h.ctorRows⟩

theorem Inv.setEnvRules {d : FDatabase} (h : d.Inv) {σ : Env} {rs : List Rule}
    (hσ : ∀ b ∈ σ, b.2 ∈ d.toDatabase.terms) :
    ({ d with env := σ, rules := rs } : FDatabase).Inv :=
  ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, hσ⟩, h.ctorTerms, h.rowsComplete, h.rowsWF,
    h.ctorRows⟩

theorem Inv.filterRows {d : FDatabase} (h : d.Inv) {p : Row → Bool}
    (hkeep : ∀ r ∈ d.rows, d.sig.mergeOf r.fn = MergeSpec.union → p r = true) :
    ({ d with rows := d.rows.filter p } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := h.ctorTerms
  rowsComplete := by
    intro r hr
    have hmem : r ∈ d.rows := h.rowsComplete hr
    have hu : d.sig.mergeOf r.fn = MergeSpec.union := h.ctorTerms r.fn r.args hr.2
    show r ∈ d.rows.filter p
    exact List.mem_filter.mpr ⟨hmem, hkeep r hmem hu⟩
  rowsWF := by
    intro r hr
    exact h.rowsWF r (List.mem_filter.mp (show r ∈ d.rows.filter p from hr)).1
  ctorRows := by
    intro r hr
    exact h.ctorRows r (List.mem_filter.mp (show r ∈ d.rows.filter p from hr)).1

/-- `Inv` through a whole action block, given every `set` in it is legal. `Inv.execAction`
iterated; `execAction_sig` is what keeps `SetLegal` — a condition on the signature —
applicable at each step. -/
theorem Inv.execActions {as : List Action} : ∀ {d d' : FDatabase}, d.Inv →
    Actions.SetLegal as d.sig → d.execActions as = some d' → d'.Inv := by
  induction as with
  | nil =>
    intro d d' h _ hs
    rw [FDatabase.execActions, Option.some.injEq] at hs
    exact hs ▸ h
  | cons a as ih =>
    intro d d' h hlegal hs
    obtain ⟨hl₁, hl₂⟩ := hlegal
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at hs; simp at hs
    | some d₁ =>
      rw [FDatabase.execActions, hv, Option.bind_some] at hs
      refine ih (h.execAction hl₁ hv) ?_ hs
      rw [execAction_sig hv]
      exact hl₂

set_option maxHeartbeats 1000000 in
/-- **One merge firing preserves `Inv`, provided the merge body's `set`s are legal.**

Four steps, each a lemma above. Rebinding `env` to `mergeEnv r₁.out r₂.out` is harmless
because `rowsWF` puts both rows' outputs in `terms`. Running the body preserves `Inv` by
`Inv.execActions`, which is exactly where `hlegal` is spent. Deleting `r₁` and `r₂` is
harmless because their function is a `.merge` function, so `ctorTerms` keeps their
application out of `terms` and `ctorRowsOf` therefore does not demand them. And the
combined row is written at that same `.merge` function, so `Inv.addRow`'s side condition
holds and its operands are constructor terms by `execExprList_ctorTerm`. -/
theorem mergeOneWith_inv {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hm : d.mergeOneWith cl r₁ r₂ = some e) : e.Inv := by
  unfold FDatabase.mergeOneWith at hm
  cases hmo : d.sig.mergeOf r₁.fn with
  | union => rw [hmo] at hm; simp at hm
  | noMerge => rw [hmo] at hm; simp at hm
  | merge body res =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, -⟩, hr₁⟩, hr₂⟩ := hcond
      have hσ : ∀ b ∈ mergeEnv r₁.out r₂.out, b.2 ∈ d.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact (h.rowsWF r₁ hr₁).2 b.2 hb'
        · exact (h.rowsWF r₂ hr₂).2 b.2 hb'
      have h₀ : ({ d with env := mergeEnv r₁.out r₂.out } : FDatabase).Inv := h.setEnv hσ
      cases hb : FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        have hsig : eb.sig = d.sig :=
          execActions_sig (d := { d with env := mergeEnv r₁.out r₂.out }) hb
        have hebInv : eb.Inv := h₀.execActions (hlegal r₁.fn body res hmo) hb
        have hcont : d.toDatabase.terms ⊆ eb.toDatabase.terms :=
          (execActions_contained (d := { d with env := mergeEnv r₁.out r₂.out }) hb).terms
        have hfne : eb.sig.mergeOf r₁.fn ≠ MergeSpec.union := by rw [hsig, hmo]; simp
        have hkeep : ∀ r ∈ eb.rows, eb.sig.mergeOf r.fn = MergeSpec.union →
            (decide (r ≠ r₁) && decide (r ≠ r₂)) = true := by
          intro r _ hu
          have h₁ : r ≠ r₁ := by rintro rfl; exact hfne hu
          have h₂ : r ≠ r₂ := by
            rintro rfl
            rw [hfn] at hfne
            exact hfne hu
          simp [h₁, h₂]
        have hfInv :=
          hebInv.filterRows (p := fun r => decide (r ≠ r₁) && decide (r ≠ r₂)) hkeep
        have hvsCtor : ∀ x ∈ vs, Term.CtorTerm eb.sig x :=
          FDatabase.execExprList_ctorTerm hebInv hebInv.env_ctorTerm hv
        have hasCtor : ∀ x ∈ r₁.args, Term.CtorTerm eb.sig x := fun x hx =>
          hebInv.ctorTerm_of_mem (hcont ((h.rowsWF r₁ hr₁).1 x hx))
        have haddInv :=
          hfInv.addRow (f := r₁.fn) (as := r₁.args) (vs := vs) hfne hasCtor hvsCtor
        refine haddInv.setEnvRules ?_
        intro b hb'
        exact FDatabase.contained_addRow.terms (hcont (h.wf.envInTerms b hb'))

/-- **A merge pass preserves the refinement-chain invariant, provided every declared
merge's action block writes only legal `set`s.** `mergeOneWith_inv` through the two folds
of `mergeRound`, exactly as `mergeRound_confined` threads `mergeOneWith_confined`. The
accumulator also carries `sig = d.sig`, which is what lets `hlegal` — a statement about
the *pre-pass* signature — apply at every intermediate state. -/
theorem Inv.mergeRound_of_legalMerges {d : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) :
    d.mergeRound.Inv := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y =>
      have hs : y.sig = x.sig := (mergeOneWith_confined hy).2.2.1
      refine ⟨mergeOneWith_inv hx.1 (fun g body res hg => ?_) hy, hs.trans hx.2⟩
      exact hx.2 ▸ hlegal g body res (hx.2 ▸ hg)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d := ⟨h, rfl⟩
  unfold FDatabase.mergeRound
  split
  · exact hinit.1
  · exact (houter d.rows d hinit).1

/-- The special case the task names: merge bodies are `[]`, which is `SetLegal` outright. -/
theorem Inv.mergeRound_of_pureMerges {d : FDatabase} (h : d.Inv)
    (hpure : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res → body = []) :
    d.mergeRound.Inv :=
  h.mergeRound_of_legalMerges fun g body res hg => by
    rw [hpure g body res hg]
    exact trivial

end FDatabase

theorem Database.ActionStep.wf {db d : Database} {a : Action} (hw : db.WF)
    (h : Database.ActionStep db a d) : d.WF := by
  cases h with
  | @expr _ t _ => exact hw.addTerm t
  | @letBind v _ t _ =>
    refine ⟨(hw.addTerm t).subtermClosed, (hw.addTerm t).eqsInTerms, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact Database.mem_addTerm t db
    · exact (hw.addTerm t).envInTerms b hb'
  | @union _ _ t₁ t₂ _ _ => exact hw.addEq t₁ t₂
  | @set f _ _ ts vs _ _ => exact hw.addRow f ts vs

theorem Database.ActionsStep.wf {db d : Database} {as : List Action} (hw : db.WF)
    (h : Database.ActionsStep db as d) : d.WF := by
  induction h with
  | nil => exact hw
  | cons ha _ ih => exact ih (Database.ActionStep.wf hw ha)

/-- A merge preserves the invariants. `RowsWF` is an added hypothesis and is forced: the
body runs with `mergeEnv a b` in scope, so `WF.envInTerms` needs the colliding rows'
outputs to be terms, which only `RowsWF` says. -/
theorem MergeStep.wf {d₁ d₂ : Database} (hw : d₁.WF) (hrw : d₁.RowsWF)
    (h : MergeStep d₁ d₂) : d₂.WF := by
  cases h with
  | @collide d f as _ a b vs _ _ hra hrb _ _ hbody _ =>
    have hw0 : ({ d₁ with env := mergeEnv a b } : Database).WF := by
      refine ⟨hw.subtermClosed, hw.eqsInTerms, fun p hp => ?_⟩
      rcases mem_mergeEnv hp with hpa | hpb
      · exact (hrw _ hra).2 _ hpa
      · exact (hrw _ hrb).2 _ hpb
    have hd : d.WF := Database.ActionsStep.wf hw0 hbody
    have hr : (d.addRow f as vs).WF := hd.addRow f as vs
    have hb : d₁.Contained d :=
      ⟨(Database.ActionsStep.contained hbody).terms,
        (Database.ActionsStep.contained hbody).rows,
        (Database.ActionsStep.contained hbody).eqs⟩
    have hc := hb.trans (Database.Contained.addRow f as vs d)
    exact ⟨hr.subtermClosed, hr.eqsInTerms, fun p hp => hc.terms (hw.envInTerms p hp)⟩

/-! ### Containment for the merge interpreter

Stage 4 of the refinement chain, together with the `execActions` refinement it rests on.
It sits here rather than beside the statements it discharges because every part of it
reads something stated above: `execAction_sig`, `mergeOneWith_inv`,
`mergeOneWith_confined`, `mergeRound_confined`, `mem_mergeEnv`, `Inv.setEnv`,
`Inv.execActions` and `Inv.mergeRound_of_legalMerges`.

`hlegal` — every declared merge's body writes only legal `set`s — recurs throughout, for
`Inv.mergeRound_of_legalMerges`'s reason: without it the accumulator's `Inv` fails, and
`Inv` is what turns the interpreter's evaluation into an `Expr.MEval` witness. -/

namespace FDatabase

/-- **`execActions` refines `ActionsStep`.**

`Actions.SetLegal as d.sig` is what carries `Inv` across the block: without it a `set` on
a constructor function breaks `ctorRows`, which is `Inv.execAction`'s hypothesis, and
`Inv` is what `execExpr_MEval` needs at every step. `execAction_sig` moves the tail's
legality past the head. -/
theorem execActions_ActionsStep {as : List Action} :
    ∀ {d d' : FDatabase}, d.Inv → Actions.SetLegal as d.sig →
    d.execActions as = some d' → Database.ActionsStep d.toDatabase as d'.toDatabase := by
  induction as with
  | nil =>
    intro d d' _ _ hs
    rw [FDatabase.execActions, Option.some.injEq] at hs
    exact hs ▸ .nil
  | cons a as ih =>
    intro d d' h hlegal hs
    obtain ⟨hl₁, hl₂⟩ := hlegal
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at hs; simp at hs
    | some d₁ =>
      rw [FDatabase.execActions, hv, Option.bind_some] at hs
      refine .cons (FDatabase.execAction_ActionStep h hv) (ih (h.execAction hl₁ hv) ?_ hs)
      rw [execAction_sig hv]
      exact hl₂

/-- Dropping rows only shrinks the denotation. -/
theorem contained_filterRows {e : FDatabase} {p : Row → Bool} {D : Database}
    (hc : e.toDatabase.Contained D) :
    ({ e with rows := e.rows.filter p } : FDatabase).toDatabase.Contained D :=
  ⟨hc.terms, fun r hr => hc.rows (List.mem_filter.mp (show r ∈ e.rows.filter p from hr)).1,
    hc.eqs⟩

/-- **One firing of the pass is one `MergeStep` of the specification.**

`x` is the accumulator, `D` a specification state the closure has already reached that
contains it. The firing's congruence test is against the *pre-pass* closure `d.closureF`,
which is why `d`'s invariant appears alongside `x`'s. `Database.ActionsStep.mono` is what
re-runs the merge body at `D`. -/
theorem mergeOneWith_mergeStep {d x y : FDatabase} {r₁ r₂ : Row} {D : Database}
    (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hx : x.Inv) (hxs : x.sig = d.sig)
    (hcl : MergeClosure d.toDatabase D) (hxc : x.toDatabase.Contained D)
    (hm : FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y) :
    ∃ D', MergeStep D D' ∧ y.toDatabase.Contained D' := by
  have hDsig : D.sig = d.sig := MergeClosure.sig hcl
  unfold FDatabase.mergeOneWith at hm
  cases hmo : x.sig.mergeOf r₁.fn with
  | union => rw [hmo] at hm; simp at hm
  | noMerge => rw [hmo] at hm; simp at hm
  | merge body res =>
    rw [hmo] at hm
    simp only at hm
    split at hm
    case isFalse => simp at hm
    case isTrue hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcond
      obtain ⟨⟨⟨hfn, hck⟩, hr₁⟩, hr₂⟩ := hcond
      have hσ : ∀ b ∈ mergeEnv r₁.out r₂.out, b.2 ∈ x.toDatabase.terms := by
        intro b hb
        rcases mem_mergeEnv hb with hb' | hb'
        · exact (hx.rowsWF r₁ hr₁).2 b.2 hb'
        · exact (hx.rowsWF r₂ hr₂).2 b.2 hb'
      have h₀ : ({ x with env := mergeEnv r₁.out r₂.out } : FDatabase).Inv := hx.setEnv hσ
      have hlx : Actions.SetLegal body x.sig := by
        rw [hxs]; exact hlegal r₁.fn body res (hxs ▸ hmo)
      cases hb : FDatabase.execActions { x with env := mergeEnv r₁.out r₂.out } body with
      | none => rw [hb] at hm; simp at hm
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at hm
        obtain ⟨vs, hv, rfl⟩ := hm
        have hbodyStep : Database.ActionsStep
            ({ x with env := mergeEnv r₁.out r₂.out } : FDatabase).toDatabase body
            eb.toDatabase := execActions_ActionsStep h₀ hlx hb
        obtain ⟨D₁, hD₁step, hD₁c, hD₁sig, hD₁env⟩ :=
          Database.ActionsStep.mono
            (db := ({ x with env := mergeEnv r₁.out r₂.out } : FDatabase).toDatabase)
            (D := { D with env := mergeEnv r₁.out r₂.out })
            ⟨hxc.terms, hxc.rows, hxc.eqs⟩ (hxs.trans hDsig.symm) rfl hbodyStep
        have hebInv : eb.Inv := h₀.execActions hlx hb
        have hml : Expr.MEvalList eb.toDatabase eb.env res vs :=
          FDatabase.execExprList_MEvalList hebInv hv
        have hmlD : Expr.MEvalList D₁ D₁.env res vs := by
          rw [← hD₁env]
          exact Expr.MEvalList.mono hD₁c hD₁sig hml
        have hr₁D : Row.mk r₁.fn r₁.args r₁.out ∈ D.rows := hxc.rows hr₁
        have hr₂D : Row.mk r₁.fn r₂.args r₂.out ∈ D.rows := by
          rw [hfn]; exact hxc.rows hr₂
        have hcongD : MCongList D r₁.args r₂.args :=
          MCongList.mono (MergeClosure.contained hcl) hDsig.symm
            (CongList.toMCongList' h.ctorTerms h.rowsComplete
              ((FDatabase.congrTuple_iff h.wf).mp hck))
        have hmoD : D.sig.mergeOf r₁.fn = MergeSpec.merge body res := by
          rw [hDsig, ← hxs]; exact hmo
        refine ⟨{ D₁.addRow r₁.fn r₁.args vs with env := D.env, rules := D.rules },
          MergeStep.collide hr₁D hr₂D hcongD hmoD hD₁step hmlD, ?_⟩
        have h3 := Database.Contained.addRow_mono
          (contained_filterRows (p := fun r => decide (r ≠ r₁) && decide (r ≠ r₂)) hD₁c)
          r₁.fn r₁.args vs
        rw [← FDatabase.toDatabase_addRow] at h3
        exact ⟨h3.terms, h3.rows, h3.eqs⟩

/-- **The merge pass lands inside a state the merge closure reaches.**

The pass deletes the two rows it merged, so its result is not itself a `MergeClosure`
state; the witness is a specification state that took the same collisions and kept the
originals. The fold invariant is "the accumulator is `Inv`, has the pre-pass signature,
and is contained in some state the closure has reached"; each firing extends the closure
by one `MergeStep.collide`. -/
theorem mergeRound_contained {d : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) :
    ∃ db, MergeClosure d.toDatabase db ∧ d.mergeRound.toDatabase.Contained db := by
  let P : FDatabase → Prop := fun x => x.Inv ∧ x.sig = d.sig ∧
    ∃ D, MergeClosure d.toDatabase D ∧ x.toDatabase.Contained D
  have hstep : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    obtain ⟨hxInv, hxs, D, hcl, hxc⟩ := hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => exact ⟨hxInv, hxs, D, hcl, hxc⟩
    | some y =>
      obtain ⟨D', hstepD, hyc⟩ :=
        mergeOneWith_mergeStep h hlegal hxInv hxs hcl hxc hy
      refine ⟨mergeOneWith_inv hxInv (fun g body res hg => ?_) hy,
        ((mergeOneWith_confined hy).2.2.1).trans hxs, D',
        Relation.ReflTransGen.tail hcl hstepD, hyc⟩
      exact hxs ▸ hlegal g body res (hxs ▸ hg)
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep x r₁ r₂ hx
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  have hinit : P d :=
    ⟨h, rfl, d.toDatabase, Relation.ReflTransGen.refl, Database.Contained.refl _⟩
  unfold FDatabase.mergeRound
  split
  · exact ⟨d.toDatabase, Relation.ReflTransGen.refl, Database.Contained.refl _⟩
  · obtain ⟨-, -, D, hcl, hc⟩ := houter d.rows d hinit
    exact ⟨D, hcl, hc⟩

/-- `mergeSaturateF_contained`, with the fuel first so the induction can generalize the
database. -/
theorem mergeSaturateF_contained_aux {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    (∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) →
    d.mergeSaturateF n = some e →
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Contained db := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Contained.refl _⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs
      exact ⟨d.toDatabase, .refl, hs ▸ Database.Contained.refl _⟩
    · have hsigR : d.mergeRound.sig = d.sig := FDatabase.mergeRound_confined.2.2.1
      have hlegal' : ∀ g body res, d.mergeRound.sig.mergeOf g = MergeSpec.merge body res →
          Actions.SetLegal body d.mergeRound.sig := by
        rw [hsigR]; exact hlegal
      obtain ⟨db₂, hcl₂, hcont₂⟩ := ih (h.mergeRound_of_legalMerges hlegal) hlegal' hs
      obtain ⟨db₁, hcl₁, hcont₁⟩ := mergeRound_contained h hlegal
      have hsig₁ : d.mergeRound.toDatabase.sig = db₁.sig := by
        show d.mergeRound.sig = db₁.sig
        rw [hsigR]
        exact (MergeClosure.sig hcl₁).symm
      obtain ⟨db₃, hcl₃, hcont₃, _⟩ := MergeClosure.transport hcont₁ hsig₁ hcl₂
      exact ⟨db₃, hcl₁.trans hcl₃, hcont₂.trans hcont₃⟩

/-- **The merge phase run to a fixpoint stays inside the merge closure.**

`mergeRound_contained` once per round, with `MergeClosure.transport` re-basing the tail's
closure onto the head's witness. `mergeRound_confined` is what keeps `hlegal` applicable
at the next round: a pass does not touch `sig`. -/
theorem mergeSaturateF_contained {d e : FDatabase} (h : d.Inv)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    {n : Nat} (hs : d.mergeSaturateF n = some e) :
    ∃ db, MergeClosure d.toDatabase db ∧ e.toDatabase.Contained db :=
  mergeSaturateF_contained_aux h hlegal hs

/-- **A round's rule firings stay inside `RunRules`.**

The witness is `RunRules d.toDatabase` itself and the merge closure is the reflexive one:
`execRunRulesM` runs no merge phase (`Impl/Merge.lean` defers it to `execCmdM`), so
nothing has to be re-based here.

`hrules` is `execActions_ActionsStep`'s premise, per rule: a rule head is an action block
like any other, and without legality `Inv` does not survive it. It is `Rule.SetLegal` at
`d.sig`, which is what `Program.SetLegal` gives for every rule a program installs.

The enumerator's substitution is transported to the specification's by
`Database.ActionsStep.envAgree`: `matchQueryM_MValidQuerySubst` only produces one that
`Env.Agree`s, and `Database.EnvAgree.eq_of_env_rules` turns that back into equality once
`fireIntoM` restores the caller's environment. -/
theorem execRunRulesM_contained {d : FDatabase} (h : d.Inv)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) :
    ∃ db, RunStep d.toDatabase db ∧ d.execRunRulesM.toDatabase.Contained db := by
  refine ⟨RunRules d.toDatabase, Relation.ReflTransGen.refl, ?_⟩
  set R : Database := RunRules d.toDatabase
  -- Values a match assigns are terms the database already holds, so extending `d.env`
  -- by one keeps `Inv`.
  have henvInv : ∀ {q : Query} {σ : Env}, σ ∈ d.matchQueryM q →
      ({ d with env := d.env ++ σ } : FDatabase).Inv := by
    intro q σ hσ
    refine h.setEnv ?_
    intro b hb
    rcases List.mem_append.mp hb with hb' | hb'
    · exact h.wf.envInTerms b hb'
    · have : σ ∈ assignments d.terms (Query.freeVars q d.env) :=
        (List.mem_filter.mp (by rwa [FDatabase.matchQueryM] at hσ)).1
      exact (mem_assignments.mp this).2 b hb'
  -- One firing lands inside `RunRules`.
  have hone : ∀ (r : Rule), r ∈ d.rules → ∀ (σ : Env), σ ∈ d.matchQueryM r.query →
      ∀ acc : FDatabase, acc.toDatabase.Contained R →
      (d.fireIntoM r acc σ).toDatabase.Contained R := by
    intro r hr σ hσ acc hacc
    rw [FDatabase.fireIntoM]
    cases hv : FDatabase.execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using hacc
    | some e =>
      have hmemS : ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase ∈
          {D | ∃ r' ∈ d.toDatabase.rules, D ∈ RuleResults d.toDatabase r'} := by
        obtain ⟨τ, hτ, hag⟩ := matchQueryM_MValidQuerySubst h hσ
        have hstep : Database.ActionsStep
            ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database) r.actions
            e.toDatabase := by
          have := execActions_ActionsStep (henvInv hσ) (hrules r hr) hv
          simpa using this
        have hEA : ({ d.toDatabase with env := d.toDatabase.env ++ σ } : Database).EnvAgree
            { d.toDatabase with env := d.toDatabase.env ++ τ } :=
          ⟨rfl, rfl, rfl, rfl, rfl, Env.Agree.append_left _ hag.symm⟩
        exact
          let ⟨e', hstep', hag'⟩ := hstep.envAgree hEA
          ⟨r, hr, τ, e', hτ, hstep',
            hag'.eq_of_env_rules d.toDatabase.env d.toDatabase.rules⟩
      have hsub :
          ({ e with env := d.env, rules := d.rules } : FDatabase).toDatabase.Contained R :=
        Database.Contained.mem_sUnion hmemS
      simp only [Option.map_some]
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · rcases mem_terms_union.mp hx with hx' | hx'
        · exact hacc.terms hx'
        · exact hsub.terms hx'
      · rcases mem_rows_union.mp hx with hx' | hx'
        · exact hacc.rows hx'
        · exact hsub.rows hx'
      · rcases mem_eqs_union.mp hx with hx' | hx'
        · exact hacc.eqs hx'
        · exact hsub.eqs hx'
  -- The two folds.
  have hinner : ∀ (r : Rule), r ∈ d.rules → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ d.matchQueryM r.query) → ∀ acc : FDatabase,
      acc.toDatabase.Contained R →
      (σs.foldl (d.fireIntoM r) acc).toDatabase.Contained R := by
    intro r hr σs
    induction σs with
    | nil => intro _ acc hacc; exact hacc
    | cons σ σs ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _
        (hone r hr σ (hall σ List.mem_cons_self) acc hacc)
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules) → ∀ acc : FDatabase,
      acc.toDatabase.Contained R → (l.foldl d.fireRuleM acc).toDatabase.Contained R := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons r l ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_
      rw [FDatabase.fireRuleM]
      exact hinner r (hall r List.mem_cons_self) _ (fun _ hσ => hσ) acc hacc
  rw [FDatabase.execRunRulesM]
  exact houter d.rules (fun _ hr => hr) d (Database.Contained.sUnion _ _)

/-- **`execCmdM_contained`'s `.action` case**, with `CmdStep.action`'s two premises spelled
out rather than packaged.

It needs no transport at all: `execAction_ActionStep` lands on the specification's
`ActionStep` result exactly, and `mergeSaturateF_contained` continues from there. That
pairing *is* `CmdStep.action` — the specification's merge phase is what pays for the
interpreter's, and without it this statement is false. -/
theorem execCmdM_action_contained {d e : FDatabase} (h : d.Inv) {a : Action}
    (halegal : a.SetLegal d.sig)
    (hlegal : ∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig)
    (hs : d.execCmdM (.action a) = some e) :
    ∃ d₁ db, Database.ActionStep d.toDatabase a d₁ ∧ MergeClosure d₁ db ∧
      e.toDatabase.Contained db := by
  rw [FDatabase.execCmdM] at hs
  obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
  have hsig₁ : d₁.sig = d.sig := execAction_sig hd₁
  have hlegal₁ : ∀ g body res, d₁.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d₁.sig := by rw [hsig₁]; exact hlegal
  obtain ⟨db, hcl, hcont⟩ :=
    mergeSaturateF_contained (h.execAction halegal hd₁) hlegal₁ hsat
  exact ⟨d₁.toDatabase, db, execAction_ActionStep h hd₁, hcl, hcont⟩

end FDatabase

/-! ### Containment for a whole program

`execRunRulesM_contained` and `mergeSaturateF_contained` cover the two phases of a round.
What is left is the bookkeeping that turns them into a statement about `execCmdM`,
`execProgramM` and `execM`, and it is bookkeeping of exactly two kinds.

**Transport.** The specification witness for a command is a state *containing* the
interpreter's, so the next command's witness has to be re-based onto it. `CmdStep.mono`
and `ProgramStep.mono` are that, and they are `MValidQuerySubst.mono` (a larger state
admits every match), `Database.ActionsStep.mono` (a block re-run on a larger state lands
on a larger result) and `MergeClosure.transport` composed. They carry `sig`, `env` and
`rules` equalities alongside the containment because all three are read: `mono` needs the
signature, a rule fires in `d.env ++ σ`, and `RunRules` ranges over `rules`.

**Preservation.** The induction carries `FDatabase.Inv`, so every command has to
re-establish it. `.action` and `.run` are the lemmas above run to a fixpoint; `.rule`
touches no field `Inv` reads; `.decl` is the one that needs a hypothesis of its own, and
`Falsity.claim1` is why. -/

/-- A merge writes its combined row and then restores the caller's environment and rule
list, so neither field ever moves. `MergeStep.sig` is the third of these; it is in
`Proofs/Step.lean`, next to `MergeClosure.sig`. -/
theorem MergeStep.envRules {d₁ d₂ : Database} (h : MergeStep d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  cases h with
  | collide _ _ _ _ _ _ => exact ⟨rfl, rfl⟩

theorem MergeClosure.envRules {d₁ d₂ : Database} (h : MergeClosure d₁ d₂) :
    d₂.env = d₁.env ∧ d₂.rules = d₁.rules := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih => exact ⟨hstep.envRules.1.trans ih.1, hstep.envRules.2.trans ih.2⟩

/-- **A firing available at `A` is available at any `C` containing it.**
`MValidQuerySubst.mono` finds the same match and `Database.ActionsStep.mono` re-runs the
head on the larger state. The result is an existential, not the join: that is all
containment needs, and it is all `ActionsStep.mono` gives. -/
theorem RuleResults.mono {A C : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) {r : Rule} {d : Database} (hd : d ∈ RuleResults A r) :
    ∃ D ∈ RuleResults C r, d.Contained D := by
  obtain ⟨σ, d', hq, hstep, rfl⟩ := hd
  have hc0 : ({ A with env := A.env ++ σ } : Database).Contained
      { C with env := C.env ++ σ } := ⟨hc.terms, hc.rows, hc.eqs⟩
  obtain ⟨D', hD', hcont, -, -⟩ := hstep.mono hc0 hsig (by simp [henv])
  exact ⟨{ D' with env := C.env, rules := C.rules },
    ⟨σ, D', MValidQuerySubst.mono hc hsig henv.symm hq, hD', rfl⟩,
    ⟨hcont.terms, hcont.rows, hcont.eqs⟩⟩

/-- **A round's rule phase is monotone.** Every database one rule contributes at `A` is
contained in one the same rule contributes at `C`, so the two unions are ordered. -/
theorem RunRules.mono {A C : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) :
    (RunRules A).Contained (RunRules C) := by
  have key : ∀ d ∈ {d | ∃ r ∈ A.rules, d ∈ RuleResults A r}, d.Contained (RunRules C) := by
    rintro d ⟨r, hr, hdr⟩
    obtain ⟨D, hD, hcd⟩ := RuleResults.mono hc hsig henv hdr
    exact hcd.trans (Database.Contained.mem_sUnion ⟨r, hrules ▸ hr, hD⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).terms (hc.terms hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).terms hx'
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).rows (hc.rows hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).rows hx'
  · rintro x (hx | hx)
    · exact (Database.Contained.sUnion C _).eqs (hc.eqs hx)
    · obtain ⟨d, hd, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact (key d hd).eqs hx'

/-- **A command available at `A` is available at any `C` containing it, and its result
still contains the smaller run's.** The four cases are `Database.ActionStep.mono`,
nothing, `RunRules.mono`, and nothing; `MergeClosure.transport` re-bases the merge phase
in the two that have one. -/
theorem CmdStep.mono {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) {c : Cmd} (h : CmdStep A c B) :
    ∃ D, CmdStep C c D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  cases h with
  | action ha hm =>
    obtain ⟨D₀, hD₀, hcont₀, hsig₀, henv₀⟩ := ha.mono hc hsig henv
    obtain ⟨D, hclD, hcontD, hsigD⟩ := MergeClosure.transport hcont₀ hsig₀ hm
    refine ⟨D, .action hD₀ hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hm).1, (MergeClosure.envRules hclD).1, henv₀]
    · rw [(MergeClosure.envRules hm).2, (MergeClosure.envRules hclD).2, ha.rules,
        hD₀.rules, hrules]
  | rule =>
    refine ⟨_, .rule, ⟨hc.terms, hc.rows, hc.eqs⟩, hsig, henv, ?_⟩
    show insert _ A.rules = insert _ C.rules
    rw [hrules]
  | run hrun =>
    obtain ⟨D, hclD, hcontD, hsigD⟩ :=
      MergeClosure.transport (RunRules.mono hc hsig henv hrules) hsig hrun
    refine ⟨D, .run hclD, hcontD, hsigD, ?_, ?_⟩
    · rw [(MergeClosure.envRules hrun).1, (MergeClosure.envRules hclD).1]; exact henv
    · rw [(MergeClosure.envRules hrun).2, (MergeClosure.envRules hclD).2]; exact hrules
  | decl =>
    refine ⟨_, .decl, ⟨hc.terms, hc.rows, hc.eqs⟩, ?_, henv, hrules⟩
    show Function.update A.sig _ _ = Function.update C.sig _ _
    rw [hsig]

/-- `CmdStep.mono` iterated. This is what makes the containment contract compose: the
specification witness for the tail of a program starts from the witness the head
produced, which contains — but need not equal — the interpreter's state. -/
theorem ProgramStep.mono {A C B : Database} (hc : A.Contained C) (hsig : A.sig = C.sig)
    (henv : A.env = C.env) (hrules : A.rules = C.rules) {p : Program}
    (h : ProgramStep A p B) :
    ∃ D, ProgramStep C p D ∧ B.Contained D ∧ B.sig = D.sig ∧ B.env = D.env ∧
      B.rules = D.rules := by
  induction h generalizing C with
  | nil => exact ⟨C, .nil, hc, hsig, henv, hrules⟩
  | cons hcmd _ ih =>
    obtain ⟨D₀, hD₀, hc₀, hs₀, he₀, hr₀⟩ := hcmd.mono hc hsig henv hrules
    obtain ⟨D₁, hD₁, hc₁, hs₁, he₁, hr₁⟩ := ih hc₀ hs₀ he₀ hr₀
    exact ⟨D₁, .cons hD₀ hD₁, hc₁, hs₁, he₁, hr₁⟩

/-! #### Declaring a fresh name

The three facts a `.decl` needs, all of them about `Signature.mergeOf` sending an
undeclared name to `.union`. -/

/-- `Signature.mergeOf` is read pointwise, so a declaration at `f` is invisible at every
other name. -/
theorem Signature.mergeOf_update_of_ne {sig : Signature} {f g : FnName} {dc : FnDecl}
    (h : g ≠ f) :
    Signature.mergeOf (Function.update sig f (some dc)) g = Signature.mergeOf sig g := by
  unfold Signature.mergeOf
  rw [Function.update_of_ne h]

/-- An undeclared name is a constructor. -/
theorem Signature.mergeOf_eq_union_of_none {sig : Signature} {f : FnName}
    (h : sig f = none) : Signature.mergeOf sig f = MergeSpec.union := by
  unfold Signature.mergeOf
  rw [h]

/-- Declaring a name the signature does not yet mention can only make a `set` *more*
legal: `Action.SetLegal` forbids exactly one value of `mergeOf`, `.union`, and that is
the value an undeclared name already has — so no legal `set` names `f`. -/
theorem Action.SetLegal.update {a : Action} {sig : Signature} {f : FnName} {dc : FnDecl}
    (hf : sig f = none) (h : a.SetLegal sig) :
    a.SetLegal (Function.update sig f (some dc)) := by
  cases a with
  | expr _ => trivial
  | letBind _ _ => trivial
  | union _ _ => trivial
  | set g _ _ =>
    have hg : g ≠ f := by
      rintro rfl
      exact h (Signature.mergeOf_eq_union_of_none hf)
    show Signature.mergeOf (Function.update sig f (some dc)) g ≠ MergeSpec.union
    rw [Signature.mergeOf_update_of_ne hg]
    exact h

theorem Actions.SetLegal.update {as : List Action} {sig : Signature} {f : FnName}
    {dc : FnDecl} (hf : sig f = none) (h : Actions.SetLegal as sig) :
    Actions.SetLegal as (Function.update sig f (some dc)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨Action.SetLegal.update hf h.1, ih h.2⟩

namespace FDatabase

/-! #### The interpreter's phases, field by field

`mergeRound_confined` records what a merge pass does to `terms`, `rows`, `eqs` and `sig`.
The transport lemmas above additionally read `env` and `rules`, and the same is needed of
`execRunRulesM`, so both folds are factored into an induction principle and instantiated
twice — once for the fields, once for `Inv`. -/

/-- Anything true of `d` and preserved by one `mergeOneWith` firing is true after a whole
pass. The two folds of `mergeRound`, factored out. -/
theorem mergeRound_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
    (hstep : ∀ x y : FDatabase, ∀ r₁ r₂ : Row, P x →
      FDatabase.mergeOneWith d.closureF x r₁ r₂ = some y → P y) :
    P d.mergeRound := by
  have hstep' : ∀ (x : FDatabase) (r₁ r₂ : Row), P x →
      P (match FDatabase.mergeOneWith d.closureF x r₁ r₂ with
         | some y => y
         | none => x) := by
    intro x r₁ r₂ hx
    cases hy : FDatabase.mergeOneWith d.closureF x r₁ r₂ with
    | none => simpa [hy] using hx
    | some y => simpa [hy] using hstep x y r₁ r₂ hx hy
  have hfold : ∀ (l : List Row) (r₁ : Row) (x : FDatabase), P x →
      P (l.foldl (fun acc' r₂ =>
          if r₁ == r₂ then acc'
          else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
            | some acc'' => acc''
            | none => acc') x) := by
    intro l
    induction l with
    | nil => intro _ x hx; exact hx
    | cons r₂ l ih =>
      intro r₁ x hx
      refine ih r₁ _ ?_
      by_cases hbe : r₁ == r₂
      · simpa [hbe] using hx
      · simpa [hbe] using hstep' x r₁ r₂ hx
  have houter : ∀ (l : List Row) (x : FDatabase), P x →
      P (l.foldl (fun acc r₁ =>
          d.rows.foldl (fun acc' r₂ =>
            if r₁ == r₂ then acc'
            else match FDatabase.mergeOneWith d.closureF acc' r₁ r₂ with
              | some acc'' => acc''
              | none => acc') acc) x) := by
    intro l
    induction l with
    | nil => intro _ hx; exact hx
    | cons r₁ l ih => intro x hx; exact ih _ (hfold d.rows r₁ x hx)
  unfold FDatabase.mergeRound
  split
  · exact hinit
  · exact houter d.rows d hinit

/-- A firing restores the caller's environment and rule list. -/
theorem mergeOneWith_envRules {cl : Finset (Term × Term)} {d e : FDatabase} {r₁ r₂ : Row}
    (h : d.mergeOneWith cl r₁ r₂ = some e) : e.env = d.env ∧ e.rules = d.rules := by
  unfold FDatabase.mergeOneWith at h
  cases hmo : d.sig.mergeOf r₁.fn with
  | union => rw [hmo] at h; simp at h
  | noMerge => rw [hmo] at h; simp at h
  | merge body res =>
    rw [hmo] at h
    simp only at h
    split at h
    case isFalse => simp at h
    case isTrue =>
      cases hb : FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body with
      | none => rw [hb] at h; simp at h
      | some eb =>
        rw [hb, Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨vs, hv, rfl⟩ := h
        exact ⟨rfl, rfl⟩

/-- A merge pass touches neither the environment nor the rule list. -/
theorem mergeRound_envRules {d : FDatabase} :
    d.mergeRound.env = d.env ∧ d.mergeRound.rules = d.rules :=
  mergeRound_induction (P := fun x => x.env = d.env ∧ x.rules = d.rules) ⟨rfl, rfl⟩
    fun _ _ _ _ hx hy =>
      ⟨(mergeOneWith_envRules hy).1.trans hx.1, (mergeOneWith_envRules hy).2.trans hx.2⟩

/-- The merge phase leaves `sig`, `env` and `rules` alone. -/
theorem mergeSaturateF_fields {n : Nat} : ∀ {d e : FDatabase},
    d.mergeSaturateF n = some e → e.sig = d.sig ∧ e.env = d.env ∧ e.rules = d.rules := by
  induction n with
  | zero =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ ⟨rfl, rfl, rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hs
      exact ⟨h₁.trans mergeRound_confined.2.2.1, h₂.trans mergeRound_envRules.1,
        h₃.trans mergeRound_envRules.2⟩

/-- `Inv.mergeRound_of_legalMerges` run to a fixpoint. `mergeRound_confined` is what keeps
`hlegal` — a statement about the pre-phase signature — applicable at the next round. -/
theorem Inv.mergeSaturateF {n : Nat} : ∀ {d e : FDatabase}, d.Inv →
    (∀ g body res, d.sig.mergeOf g = MergeSpec.merge body res →
      Actions.SetLegal body d.sig) →
    d.mergeSaturateF n = some e → e.Inv := by
  induction n with
  | zero =>
    intro d e h _ hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · exact absurd hs (by simp)
  | succ n ih =>
    intro d e h hlegal hs
    rw [FDatabase.mergeSaturateF] at hs
    split at hs
    · rw [Option.some.injEq] at hs; exact hs ▸ h
    · refine ih (h.mergeRound_of_legalMerges hlegal) ?_ hs
      rw [mergeRound_confined.2.2.1]; exact hlegal

/-- Unioning two states preserves the refinement-chain invariant, provided they agree on
the signature: every field of `Inv` is a positive condition on `terms`, `rows` and `eqs`
relative to `sig`, and a union takes `sig`, `env` and `rules` from the left. -/
theorem Inv.union {d e : FDatabase} (hd : d.Inv) (he : e.Inv) (hsig : e.sig = d.sig) :
    (d.union e).Inv where
  wf := by
    refine ⟨fun t ht s hs => ?_, fun p hp => ?_, fun b hb => ?_⟩
    · rcases mem_terms_union.mp ht with ht' | ht'
      · exact mem_terms_union.mpr (Or.inl (hd.wf.subtermClosed t ht' hs))
      · exact mem_terms_union.mpr (Or.inr (he.wf.subtermClosed t ht' hs))
    · rcases mem_eqs_union.mp hp with hp' | hp'
      · exact ⟨mem_terms_union.mpr (Or.inl (hd.wf.eqsInTerms p hp').1),
          mem_terms_union.mpr (Or.inl (hd.wf.eqsInTerms p hp').2)⟩
      · exact ⟨mem_terms_union.mpr (Or.inr (he.wf.eqsInTerms p hp').1),
          mem_terms_union.mpr (Or.inr (he.wf.eqsInTerms p hp').2)⟩
    · exact mem_terms_union.mpr (Or.inl (hd.wf.envInTerms b hb))
  ctorTerms := by
    intro f as ht
    rcases mem_terms_union.mp ht with ht' | ht'
    · exact hd.ctorTerms f as ht'
    · show d.sig.mergeOf f = MergeSpec.union
      rw [← hsig]
      exact he.ctorTerms f as ht'
  rowsComplete := by
    rintro r ⟨hout, hm⟩
    rcases mem_terms_union.mp hm with hm' | hm'
    · exact mem_rows_union.mpr (Or.inl (hd.rowsComplete ⟨hout, hm'⟩))
    · exact mem_rows_union.mpr (Or.inr (he.rowsComplete ⟨hout, hm'⟩))
  rowsWF := by
    intro r hr
    rcases mem_rows_union.mp hr with hr' | hr'
    · exact ⟨fun a ha => mem_terms_union.mpr (Or.inl ((hd.rowsWF r hr').1 a ha)),
        fun v hv => mem_terms_union.mpr (Or.inl ((hd.rowsWF r hr').2 v hv))⟩
    · exact ⟨fun a ha => mem_terms_union.mpr (Or.inr ((he.rowsWF r hr').1 a ha)),
        fun v hv => mem_terms_union.mpr (Or.inr ((he.rowsWF r hr').2 v hv))⟩
  ctorRows := by
    intro r hr hu
    rcases mem_rows_union.mp hr with hr' | hr'
    · exact ⟨(hd.ctorRows r hr' hu).1,
        mem_terms_union.mpr (Or.inl (hd.ctorRows r hr' hu).2)⟩
    · have hu' : e.sig.mergeOf r.fn = MergeSpec.union := by rw [hsig]; exact hu
      exact ⟨(he.ctorRows r hr' hu').1,
        mem_terms_union.mpr (Or.inr (he.ctorRows r hr' hu').2)⟩

/-- Anything true of `d` and preserved by one rule firing is true of a whole round's rule
phase. The three folds of `execRunRulesM`, factored out. -/
theorem execRunRulesM_induction {d : FDatabase} {P : FDatabase → Prop} (hinit : P d)
    (hstep : ∀ (acc e : FDatabase) (r : Rule) (σ : Env), P acc → r ∈ d.rules →
      σ ∈ d.matchQueryM r.query →
      FDatabase.execActions { d with env := d.env ++ σ } r.actions = some e →
      P (acc.union { e with env := d.env, rules := d.rules })) :
    P d.execRunRulesM := by
  have hone : ∀ (r : Rule), r ∈ d.rules → ∀ (σ : Env), σ ∈ d.matchQueryM r.query →
      ∀ acc : FDatabase, P acc → P (d.fireIntoM r acc σ) := by
    intro r hr σ hσ acc hacc
    rw [FDatabase.fireIntoM]
    cases hv : FDatabase.execActions { d with env := d.env ++ σ } r.actions with
    | none => simpa using hacc
    | some e => simpa using hstep acc e r σ hacc hr hσ hv
  have hinner : ∀ (r : Rule), r ∈ d.rules → ∀ (σs : List Env),
      (∀ σ ∈ σs, σ ∈ d.matchQueryM r.query) → ∀ acc : FDatabase, P acc →
      P (σs.foldl (d.fireIntoM r) acc) := by
    intro r hr σs
    induction σs with
    | nil => intro _ acc hacc; exact hacc
    | cons σ σs ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      exact ih (fun τ hτ => hall τ (List.mem_cons_of_mem _ hτ)) _
        (hone r hr σ (hall σ List.mem_cons_self) acc hacc)
  have houter : ∀ (l : List Rule), (∀ r ∈ l, r ∈ d.rules) → ∀ acc : FDatabase, P acc →
      P (l.foldl d.fireRuleM acc) := by
    intro l
    induction l with
    | nil => intro _ acc hacc; exact hacc
    | cons r l ih =>
      intro hall acc hacc
      rw [List.foldl_cons]
      refine ih (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) _ ?_
      rw [FDatabase.fireRuleM]
      exact hinner r (hall r List.mem_cons_self) _ (fun _ hσ => hσ) acc hacc
  rw [FDatabase.execRunRulesM]
  exact houter d.rules (fun _ hr => hr) d hinit

/-- A round's rule phase leaves `sig`, `env` and `rules` alone: every firing is unioned
into the accumulator, and a union takes those three fields from the left. -/
theorem execRunRulesM_fields {d : FDatabase} :
    d.execRunRulesM.sig = d.sig ∧ d.execRunRulesM.env = d.env ∧
      d.execRunRulesM.rules = d.rules :=
  execRunRulesM_induction (P := fun x => x.sig = d.sig ∧ x.env = d.env ∧ x.rules = d.rules)
    ⟨rfl, rfl, rfl⟩ fun _ _ _ _ hacc _ _ _ => hacc

/-- Every value a match assigns is a term the database already holds, so extending `d.env`
by one keeps `Inv`. -/
theorem Inv.setEnvMatch {d : FDatabase} (h : d.Inv) {q : Query} {σ : Env}
    (hσ : σ ∈ d.matchQueryM q) : ({ d with env := d.env ++ σ } : FDatabase).Inv := by
  refine h.setEnv ?_
  intro b hb
  rcases List.mem_append.mp hb with hb' | hb'
  · exact h.wf.envInTerms b hb'
  · have : σ ∈ assignments d.terms (Query.freeVars q d.env) :=
      (List.mem_filter.mp (by rwa [FDatabase.matchQueryM] at hσ)).1
    exact (mem_assignments.mp this).2 b hb'

/-- **A round's rule phase preserves `Inv`.** Each firing runs a rule head, which is an
action block like any other, so `hrules` is `Inv.execActions`'s premise per rule; the
result is unioned in, which `Inv.union` covers. -/
theorem Inv.execRunRulesM {d : FDatabase} (h : d.Inv)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) : d.execRunRulesM.Inv := by
  have := execRunRulesM_induction (d := d) (P := fun x => x.Inv ∧ x.sig = d.sig) ⟨h, rfl⟩
    (fun acc e r σ hacc hr hσ hv => ?_)
  · exact this.1
  refine ⟨hacc.1.union ?_ ?_, hacc.2⟩
  · refine Inv.setEnvRules ((h.setEnvMatch hσ).execActions (hrules r hr) hv) ?_
    exact fun b hb => (execActions_contained hv).terms (h.wf.envInTerms b hb)
  · show e.sig = acc.sig
    rw [execActions_sig hv, hacc.2]

@[simp] theorem addTerms_rules {d : FDatabase} {ts : List Term} :
    (d.addTerms ts).rules = d.rules := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_rules {d : FDatabase} {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).rules = d.rules := by
  show ((d.addTerms as).addTerms vs).rules = d.rules
  rw [addTerms_rules, addTerms_rules]

/-- No action touches the rule list; only `Cmd.rule` does. -/
theorem execAction_rules {d e : FDatabase} {a : Action} (h : d.execAction a = some e) :
    e.rules = d.rules := by
  cases a with
  | expr e₀ =>
    rw [FDatabase.execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | letBind v e₀ =>
    rw [FDatabase.execAction] at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  | union e₁ e₂ =>
    rw [FDatabase.execAction] at h
    obtain ⟨t₁, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    rfl
  | set f args out =>
    rw [FDatabase.execAction] at h
    obtain ⟨ts, -, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, -, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact addRow_rules

theorem execActions_rules {d e : FDatabase} {as : List Action}
    (h : d.execActions as = some e) : e.rules = d.rules := by
  induction as generalizing d with
  | nil => rw [FDatabase.execActions, Option.some.injEq] at h; exact h ▸ rfl
  | cons a as ih =>
    cases hv : d.execAction a with
    | none => rw [FDatabase.execActions, hv] at h; simp at h
    | some d' =>
      rw [FDatabase.execActions, hv, Option.bind_some] at h
      exact (ih h).trans (execAction_rules hv)

/-- **`Inv` survives a declaration of a name the state does not yet mention.**

`Falsity.claim1` shows there is no unconditional preservation lemma: `CtorTerms` reads
`sig`, so declaring `g` `:merge` after `g ()` is already a term breaks it. The two
hypotheses are what rule that out — `hterms` keeps `ctorTerms`, and `hf` keeps
`ctorRows`, since an undeclared name is already a constructor and every row of one is
already a constructor row. -/
theorem Inv.decl {d : FDatabase} (h : d.Inv) {f : FnName} {dc : FnDecl}
    (hf : d.sig f = none) (hterms : ∀ as, Term.app f as ∉ d.terms) :
    ({ d with sig := Function.update d.sig f (some dc) } : FDatabase).Inv where
  wf := ⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩
  ctorTerms := by
    intro g as hm
    have hg : g ≠ f := by rintro rfl; exact hterms as hm
    show Signature.mergeOf (Function.update d.sig f (some dc)) g = MergeSpec.union
    rw [Signature.mergeOf_update_of_ne hg]
    exact h.ctorTerms g as hm
  rowsComplete := h.rowsComplete
  rowsWF := h.rowsWF
  ctorRows := by
    intro r hr hu
    refine h.ctorRows r hr ?_
    show Signature.mergeOf d.sig r.fn = MergeSpec.union
    by_cases hfn : r.fn = f
    · rw [hfn]
      exact Signature.mergeOf_eq_union_of_none hf
    · rw [← Signature.mergeOf_update_of_ne (sig := d.sig) (dc := dc) hfn]
      exact hu

end FDatabase

/-! #### The side conditions

Two of them, and neither is avoidable. `Signature.MergesLegal` is what
`Falsity.mergeRound_inv_false` forces; `FDatabase.Unused` is what `Falsity.claim1`
forces. `FDatabase.ProgramLegal` checks both at the state each command runs in, which is
the weakest place to check them: a declaration only has to be fresh *when it happens*. -/

/-- Every declared `:merge` body obeys the `set` discipline every other action block
obeys. `Cmd.SetLegal (.decl _ _)` is `True`, so `Program.SetLegal` says nothing about
merge bodies and this has to be carried separately. -/
def Signature.MergesLegal (sig : Signature) : Prop :=
  ∀ g body res, Signature.mergeOf sig g = MergeSpec.merge body res →
    Actions.SetLegal body sig

/-- `f` is a name `d` does not mention: not declared, and not the head of any application
`d` holds. This is "declare before use", which egglog enforces in its front end. -/
def FDatabase.Unused (d : FDatabase) (f : FnName) : Prop :=
  d.sig f = none ∧ ∀ as, Term.app f as ∉ d.terms

/-- The one thing a command may not do to the state it runs in: declare a name that state
already uses. Only `.decl` is constrained. -/
def Cmd.DeclUnused : Cmd → FDatabase → Prop
  | .decl f _, d => d.Unused f
  | _, _ => True

/-- The side conditions a run has to satisfy, checked at the state each command actually
reaches: its head is a legal `set`, it declares nothing already in use, and the signature
it leaves behind has legal merge bodies. -/
def FDatabase.ProgramLegal (d : FDatabase) : Program → Prop
  | [] => True
  | c :: cs => c.SetLegal d.sig ∧ c.DeclUnused d ∧
      Signature.MergesLegal (c.sigBind d.sig) ∧
      ∀ d', d.execCmdM c = some d' → FDatabase.ProgramLegal d' cs

namespace FDatabase

/-- The signature after a command is the one `Cmd.sigBind` predicts: only `.decl` moves
it, and neither an action nor a merge phase does. -/
theorem execCmdM_sig {d d' : FDatabase} {c : Cmd} (hs : d.execCmdM c = some d') :
    d'.sig = c.sigBind d.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, execAction_sig h₁]
    rfl
  | rule r => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl
  | run =>
    rw [FDatabase.execCmdM] at hs
    rw [(mergeSaturateF_fields hs).1, execRunRulesM_fields.1]
    rfl
  | decl f dc => rw [FDatabase.execCmdM, Option.some.injEq] at hs; exact hs ▸ rfl

/-- **`Inv` through one command.** `.action` and `.run` are the phase lemmas composed with
`Inv.mergeSaturateF`; `.rule` touches no field `Inv` reads; `.decl` is `Inv.decl`, and is
the only case with a side condition of its own. -/
theorem Inv.execCmdM {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') : d'.Inv := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    refine Inv.mergeSaturateF (h.execAction hlegal h₁) ?_ h₂
    rw [execAction_sig h₁]; exact hmerges
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ ⟨⟨h.wf.subtermClosed, h.wf.eqsInTerms, h.wf.envInTerms⟩, h.ctorTerms,
      h.rowsComplete, h.rowsWF, h.ctorRows⟩
  | run =>
    rw [FDatabase.execCmdM] at hs
    refine Inv.mergeSaturateF (h.execRunRulesM hrules) ?_ hs
    rw [execRunRulesM_fields.1]; exact hmerges
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    exact hs ▸ h.decl hunused.1 hunused.2

/-- Rule-head legality is preserved: `.rule` installs a head `Cmd.SetLegal` has already
checked, and `.decl` only ever declares a name no head can legally have `set`
(`Actions.SetLegal.update`). -/
theorem execCmdM_rulesLegal {d d' : FDatabase} {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hunused : c.DeclUnused d)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∀ r ∈ d'.rules, Actions.SetLegal r.actions d'.sig := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs
    rw [(mergeSaturateF_fields h₂).1, (mergeSaturateF_fields h₂).2.2,
      execAction_sig h₁, execAction_rules h₁]
    exact hrules
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact hlegal
    · exact hrules r' hr''
  | run =>
    rw [FDatabase.execCmdM] at hs
    rw [(mergeSaturateF_fields hs).1, (mergeSaturateF_fields hs).2.2,
      execRunRulesM_fields.1, execRunRulesM_fields.2.2]
    exact hrules
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    exact fun r hr => Actions.SetLegal.update hunused.1 (hrules r hr)

/-! #### The three containment theorems -/

/-- `execCmdM_contained` with the three fields `Database.Contained` ignores. The extra
equalities are what `CmdStep.mono` consumes, so the program induction can start its tail
from the witness the head produced. -/
theorem execCmdM_contained' {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db ∧
      d'.toDatabase.sig = db.sig ∧ d'.toDatabase.env = db.env ∧
      d'.toDatabase.rules = db.rules := by
  cases c with
  | action a =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨d₁, hd₁, hsat⟩ := Option.bind_eq_some_iff.mp hs
    have hmerges₁ : Signature.MergesLegal d₁.sig := by
      rw [execAction_sig hd₁]; exact hmerges
    obtain ⟨db, hcl, hcont⟩ :=
      mergeSaturateF_contained (h.execAction hlegal hd₁) hmerges₁ hsat
    refine ⟨db, .action (execAction_ActionStep h hd₁) hcl, hcont, ?_, ?_, ?_⟩
    · show d'.sig = db.sig
      rw [MergeClosure.sig hcl]; exact (mergeSaturateF_fields hsat).1
    · show d'.env = db.env
      rw [(MergeClosure.envRules hcl).1]; exact (mergeSaturateF_fields hsat).2.1
    · show ({r | r ∈ d'.rules} : Set Rule) = db.rules
      rw [(MergeClosure.envRules hcl).2, (mergeSaturateF_fields hsat).2.2]
      rfl
  | rule r =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    refine ⟨{ d.toDatabase with rules := insert r d.toDatabase.rules }, .rule,
      ⟨subset_rfl, subset_rfl, subset_rfl⟩, rfl, rfl, ?_⟩
    show ({r' | r' ∈ r :: d.rules} : Set Rule) = insert r {r' | r' ∈ d.rules}
    ext r'
    simp
  | run =>
    rw [FDatabase.execCmdM] at hs
    obtain ⟨R, hRstep, hRcont⟩ := execRunRulesM_contained h hrules
    have hRsig : R.sig = d.sig := MergeClosure.sig hRstep
    have hRenv : R.env = d.env := (MergeClosure.envRules hRstep).1
    have hRrules : R.rules = d.toDatabase.rules := (MergeClosure.envRules hRstep).2
    have hmerges₁ : Signature.MergesLegal d.execRunRulesM.sig := by
      rw [execRunRulesM_fields.1]; exact hmerges
    obtain ⟨db₂, hcl₂, hcont₂⟩ :=
      mergeSaturateF_contained (h.execRunRulesM hrules) hmerges₁ hs
    obtain ⟨db₃, hcl₃, hcont₃, hsig₃⟩ :=
      MergeClosure.transport hRcont (by rw [hRsig]; exact execRunRulesM_fields.1) hcl₂
    refine ⟨db₃, .run (hRstep.trans hcl₃), hcont₂.trans hcont₃, ?_, ?_, ?_⟩
    · show d'.sig = db₃.sig
      rw [MergeClosure.sig hcl₃, hRsig, (mergeSaturateF_fields hs).1,
        execRunRulesM_fields.1]
    · show d'.env = db₃.env
      rw [(MergeClosure.envRules hcl₃).1, hRenv, (mergeSaturateF_fields hs).2.1,
        execRunRulesM_fields.2.1]
    · show ({r | r ∈ d'.rules} : Set Rule) = db₃.rules
      rw [(MergeClosure.envRules hcl₃).2, hRrules, (mergeSaturateF_fields hs).2.2,
        execRunRulesM_fields.2.2]
      rfl
  | decl f dc =>
    rw [FDatabase.execCmdM, Option.some.injEq] at hs
    subst hs
    exact ⟨{ d.toDatabase with sig := Function.update d.toDatabase.sig f (some dc) },
      .decl, ⟨subset_rfl, subset_rfl, subset_rfl⟩, rfl, rfl, rfl⟩

/-- **The interpreter's answer to one command is contained in one the specification
reaches.**

`.action` is `execAction_ActionStep` followed by `mergeSaturateF_contained`, which is
`CmdStep.action`'s two premises exactly — the specification's merge phase is what pays
for the interpreter's, and before `CmdStep.action` had one this theorem was **false**
(the deleted `Falsity.claim2`). `.run` is `execRunRulesM_contained` re-based by
`MergeClosure.transport`. `.rule` and `.decl` land on the specification's state on the
nose.

`hlegal` and `hrules` are `Inv.execAction`'s and `Inv.execActions`'s premises; `hmerges`
is what a merge body needs and `Program.SetLegal` does not supply. -/
theorem execCmdM_contained {d d' : FDatabase} (h : d.Inv) {c : Cmd}
    (hlegal : c.SetLegal d.sig) (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hs : d.execCmdM c = some d') :
    ∃ db, CmdStep d.toDatabase c db ∧ d'.toDatabase.Contained db := by
  obtain ⟨db, hstep, hcont, -, -, -⟩ := execCmdM_contained' h hlegal hmerges hrules hs
  exact ⟨db, hstep, hcont⟩

theorem execProgramM_contained_aux {p : Program} : ∀ {d d' : FDatabase}, d.Inv →
    Signature.MergesLegal d.sig →
    (∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig) →
    d.ProgramLegal p → d.execProgramM p = some d' →
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db := by
  induction p with
  | nil =>
    intro d d' _ _ _ _ hs
    rw [FDatabase.execProgramM, Option.some.injEq] at hs
    exact ⟨d.toDatabase, .nil, hs ▸ Database.Contained.refl _⟩
  | cons c cs ih =>
    intro d d' h hmerges hrules hp hs
    rw [FDatabase.execProgramM] at hs
    obtain ⟨d₁, hd₁, hcs⟩ := Option.bind_eq_some_iff.mp hs
    rw [FDatabase.ProgramLegal] at hp
    obtain ⟨hlegal, hunused, hmerges', hnext⟩ := hp
    obtain ⟨db₁, hstep₁, hcont₁, hsig₁, henv₁, hrules₁⟩ :=
      execCmdM_contained' h hlegal hmerges hrules hd₁
    obtain ⟨db₂, hstep₂, hcont₂⟩ :=
      ih (h.execCmdM hlegal hmerges hunused hrules hd₁)
        (by rw [execCmdM_sig hd₁]; exact hmerges')
        (execCmdM_rulesLegal hlegal hunused hrules hd₁) (hnext d₁ hd₁) hcs
    obtain ⟨db₃, hstep₃, hcont₃, -, -, -⟩ :=
      ProgramStep.mono hcont₁ hsig₁ henv₁ hrules₁ hstep₂
    exact ⟨db₃, .cons hstep₁ hstep₃, hcont₂.trans hcont₃⟩

/-- **The interpreter's answer to a whole program is contained in one the specification
reaches.**

`execCmdM_contained'` per command, with `ProgramStep.mono` re-basing the tail's witness
onto the head's — which is where `MValidSubst.mono` is spent, read forwards: a larger
specification state still admits every match, so the specification can follow along.

`hp` is the per-command bundle. It is what carries the induction across a `.decl`:
`FDatabase.Inv` is not preserved by an arbitrary declaration (`Falsity.claim1`), and
`FDatabase.Unused` is the weakest thing that restores it — the declaration names
something the state does not yet mention, which is what egglog's front end requires
anyway. It does not restrict which `:merge` functions a program may declare, so the
merge fragment is not excluded. -/
theorem execProgramM_contained {d d' : FDatabase} (h : d.Inv) {p : Program}
    (hmerges : Signature.MergesLegal d.sig)
    (hrules : ∀ r ∈ d.rules, Actions.SetLegal r.actions d.sig)
    (hp : d.ProgramLegal p) (hs : d.execProgramM p = some d') :
    ∃ db, ProgramStep d.toDatabase p db ∧ d'.toDatabase.Contained db :=
  execProgramM_contained_aux h hmerges hrules hp hs

end FDatabase

/-- **The contract for `execM`.** `execProgramM_contained` from `FDatabase.empty`, whose
two global side conditions discharge themselves: the empty signature declares no merge
body and the empty state has no rules. `hp` is what remains, and `FDatabase.ProgramLegal`
is stated so that a front end which declares before use and type-checks its merge bodies
satisfies it.

See the section header above for why the contract is containment rather than the equality
`exec_toDatabase` enjoys. -/
theorem execM_contained {p : Program} (hp : FDatabase.empty.ProgramLegal p)
    {d : FDatabase} (h : execM p = some d) :
    ∃ db, ProgramStep FDatabase.empty.toDatabase p db ∧ d.toDatabase.Contained db :=
  FDatabase.execProgramM_contained FDatabase.Inv.empty
    (fun g body res hg => by
      rw [Signature.mergeOf_eq_union_of_none
        (show FDatabase.empty.sig g = none from rfl)] at hg
      exact MergeSpec.noConfusion hg)
    (fun r hr => absurd hr (by simp [FDatabase.empty])) hp h

end Egglog
