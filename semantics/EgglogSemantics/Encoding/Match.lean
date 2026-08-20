import EgglogSemantics.Encoding.Correspond

/-!
# The rule-head match correspondence

`Encoding/Correspond.lean` reduces both halves of `encode_corresponds` to properties of the
state `execM` returned, and both residues then ask the same question about a *rule*: the
encoded rule fired, so what did the source rule do? Everything a head writes — a build or a
`union` inside `r.actions` — needs a source-side hypothesis, and the only place one can come
from is the query. This file is that step.

## What is stated, and why in this shape

The correspondence is a property of the **two states**, not of `execM`, the same discipline
`cong_sameClass_of_state` and `sameClass_cong_of_state` follow. Nothing below mentions
`encode` except the two lemmas that *establish* its hypotheses, and those are named and kept
apart.

The target-side hypothesis is `QueryRead`: the ids the flattened query bound, read off
`Database.Out` rather than off `Matches`. `out_of_matches_values` is what turns one encoded
view read into one `Database.Out`, and it needs `Database.Diag` — which is the *already
established* fact that `encode` emits no `union`, so `Cong tgt` is equality and a read is a
lookup. `encodeQuery` **flattens**, so one source pattern becomes several reads and
`@Rule_i`'s premise count is the read count; `QueryRead` is indexed by the *source*
expression and mirrors that flattening as a recursion, which is what makes the
correspondence one-pattern-to-one-derivation rather than one-atom-to-one-atom.

The source-side conclusion is `ValidQuerySubst src r.query τ` together with
`Env.lookup v (src.env ++ τ) = some (g v)` for the query's variables: the head needs to know
*which* source terms fired it, not only that something did.

## The two facts it rests on, both already in hand

* **`Database.ViewsSound`** (`Encoding/Correspond.lean`) is the whole of what the target
  contributes. `EntrySound`'s existential is exactly the source argument list a view read's
  key stands for, so a view read hands back a source application the source holds.
* **View tables are not functional**, and this never asks them to be: `Database.Out` is read
  existentially and `EntrySound` is stated per entry, so two entries at one key are two
  hypotheses rather than a contradiction.

## What it does **not** deliver

A rule head's `entrySound_build`. `encodeBuild` mints the skolem over its arguments' **ids**,
so the entry a head writes is keyed and valued at ids where the correspondence delivers the
source application over the source *terms* the query matched.
`mem_terms_of_entrySound_skolem` is that gap compiled: `Database.ViewsSound` at a freshly
built entry is *equivalent* to the minted id being a source term, which it is only where no
`union` has re-canonicalized an argument. So the head-build case of `execM_viewsSound` needs
one more fact than this file proves, and it is the same fact
`encode_corresponds_invents_enode` refutes at a key column.

## And what it is false for

`encodePattern` emits **no atom** for a source pattern whose expression is a bare literal or
a bare variable — `encodeQueryExpr` flattens an application and returns a leaf unchanged. A
dropped constraint is a rule the target fires and the source does not, and
`encodeQuery_drops_literal_pattern` is that refuted: at `satProgram`'s own source state, the
source query `[(1)]` matches under no substitution while its encoding, the empty query,
matches under the empty one. `Pattern.Grounded` is the side condition that excludes it, and
it is a restriction on the *source program's text*, decidable and checkable.
-/

namespace Egglog

/-! ### What the flattened query read

One source pattern expression, and the id the encoded query's reads bound it to. The
recursion is `encodeQueryExpr`'s: a literal and a variable emit no atom and stand for
themselves, an application emits its arguments' reads and then one view read keyed on their
ids.

`ρ` is the **combined** environment the match ran in — `d.env ++ σ` — so nothing here says
where the encoded query's bindings came from, and the generated variables `@v0`, `@v1`, … do
not appear: their values *are* the ids this relation carries. -/

mutual

/-- `i` is the id the flattened reads of the source expression `e` bound, under `ρ`.

`ViewRepr` with the leaves supplied by `ρ` instead of by a source term: the two agree at a
ground `e`, and that is the whole of what the encoded query adds. -/
inductive QueryRead (d : Database) (ρ : Env) : Expr → Term → Prop where
  | lit {l : Lit} : QueryRead d ρ (.lit l) (.lit l)
  | var {v : Var} {i : Term} : Env.lookup v ρ = some i → QueryRead d ρ (.var v) i
  | app {f : FnName} {args : List Expr} {es : List Term} {i pf : Term} :
      QueryReadList d ρ args es → d.Out (viewName f) es [i, pf] →
      QueryRead d ρ (.app f args) i

/-- `QueryRead` over an argument list. -/
inductive QueryReadList (d : Database) (ρ : Env) : List Expr → List Term → Prop where
  | nil : QueryReadList d ρ [] []
  | cons {a : Expr} {i : Term} {as : List Expr} {is : List Term} :
      QueryRead d ρ a i → QueryReadList d ρ as is → QueryReadList d ρ (a :: as) (i :: is)

end

/-- The target's reading of one source pattern. A `.eq` reads **one** id for both sides,
which is what the encoded `.eq` atom says at a diagonal target: it compares ids, and there
congruence is equality. -/
inductive PatternRead (d : Database) (ρ : Env) : Pattern → Prop where
  | expr {e : Expr} {i : Term} : QueryRead d ρ e i → PatternRead d ρ (.expr e)
  | eq {e₁ e₂ : Expr} {i : Term} :
      QueryRead d ρ e₁ i → QueryRead d ρ e₂ i → PatternRead d ρ (.eq e₁ e₂)

/-! ### The two substitutions, linked -/

/-- **Every variable of `vs` the target bound to an id, the source bound to a term congruent
to it.** The relation between the two matches, and the only thing the source side of the
correspondence is allowed to know about the target's substitution.

Restricted to `vs` because the encoded query binds the generated variables too, and those
have no source counterpart — their values are ids, which `QueryRead` carries directly. -/
def Env.ReadsAs (src : Database) (ρs ρt : Env) (vs : List Var) : Prop :=
  ∀ v ∈ vs, ∀ i, Env.lookup v ρt = some i → ∃ t, Env.lookup v ρs = some t ∧ Cong src t i

theorem Env.ReadsAs.mono {src : Database} {ρs ρt : Env} {vs ws : List Var}
    (h : Env.ReadsAs src ρs ρt vs) (hsub : ws ⊆ vs) : Env.ReadsAs src ρs ρt ws :=
  fun v hv => h v (hsub hv)

/-! ### The source-side reading, upward closed

A pattern instance is a term the source need not hold, so `Matches` relates it to a witness
in `src.withOperands`. The instance of a *subexpression* is a subterm of the instance of the
whole, so one extension covers the whole recursion — and stating the congruence over *every*
extension is what lets a parent instantiate its children's at its own. -/

/-- `t` is congruent to the id `i` in any database extending `src` that holds `t`'s
subterms. The universal quantifier is the point: `Cong src t i` is too strong (the source
need not hold `t`) and `CongOn src [t] t i` is too weak to compose. -/
def CongUp (src : Database) (t i : Term) : Prop :=
  ∀ D : Database, src.Contained D → (∀ s ∈ t.subterms, s ∈ D.terms) → Cong D t i

/-- A literal reads itself, and it is its own subterm. -/
theorem CongUp.lit {src : Database} {l : Lit} : CongUp src (.lit l) (.lit l) :=
  fun _ _ hsub => hsub _ (Term.self_mem_subterms _)

/-- A source-side congruence is one every extension keeps. This is the variable case. -/
theorem CongUp.of_cong {src : Database} {t i : Term} (h : Cong src t i) : CongUp src t i :=
  fun _ hc _ => Cong.mono hc h

/-- Pointwise, at one extension: the arguments' congruences instantiated where the parent
needs them. `arg_subterms` is what says the extension covering the parent covers each
child. -/
theorem CongUp.congList {src D : Database} (hcon : src.Contained D) {ts es : List Term}
    (h : List.Forall₂ (CongUp src) ts es)
    (hsub : ∀ t ∈ ts, ∀ s ∈ t.subterms, s ∈ D.terms) : CongList D ts es := by
  rw [CongList.forall₂]
  induction h with
  | nil => exact .nil
  | @cons a b as bs hab hl ih =>
    exact .cons (hab D hcon (hsub a (by simp))) (ih fun t ht => hsub t (by simp [ht]))

/-- The form `Matches` consumes: the instance is congruent to its id in the database the
witness clause extends by it. -/
theorem CongUp.congOn {src : Database} {t i : Term} (h : CongUp src t i) :
    CongOn src [t] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

/-- The same at a pair of operands, which is what `Matches.eq` extends by. -/
theorem CongUp.congOn_pair_left {src : Database} {t u i : Term} (h : CongUp src t i) :
    CongOn src [t, u] t i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨t, by simp, hs⟩

@[inherit_doc CongUp.congOn_pair_left]
theorem CongUp.congOn_pair_right {src : Database} {t u i : Term} (h : CongUp src u i) :
    CongOn src [t, u] u i :=
  h _ (Database.Contained.addTerms _ _) fun s hs => by
    rw [Database.withOperands, Database.addTerms_terms]
    exact Or.inr ⟨u, by simp, hs⟩

/-! ### What the source has to be for its side to evaluate

`Expr.eval` consults the primitive table and then `Signature.IsCtor`, so the source-side
reading of a pattern is stuck unless the pattern's heads build. Under
`Program.EncodeDomain` they do — `noPrim` and `ctorsOnly` — and this is that as a property
of the state, which is the form the correspondence can use. -/

/-- **Every application the source holds is a declared constructor's, applied.** -/
def Database.TermsBuild (src : Database) : Prop :=
  ∀ f as, Term.app f as ∈ src.terms → Prim.ofName f = none ∧ src.sig.IsCtor f

/-! ### The correspondence, at one pattern expression

**The core.** No `encode`, no `execM`, no `Matches` on the target: three named properties of
the two states and one `QueryRead`, and out comes the source-side instance with its
congruence to the id. -/

mutual

/-- **What the target read, the source built.** The source-side instance of `e` under `ρs`
exists and is congruent to the id the target read, in any extension holding the instance.

By recursion on the reading. `ViewsSound` is used once, at the application, and it is what
supplies the source argument list the view read's key stands for; `TermsBuild` is used once,
to know the head builds; `Env.ReadsAs` is used once, at the variable. -/
theorem congUp_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {ρs ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src ρs ρt e.vars) :
    ∃ t, e.eval src.sig ρs = some t ∧ CongUp src t i := by
  revert hlink
  induction h using QueryRead.rec
    (motive_2 := fun es is _ => Env.ReadsAs src ρs ρt (Expr.varsList es) →
      ∃ ts, Expr.evalList src.sig es ρs = some ts ∧ List.Forall₂ (CongUp src) ts is) with
  | lit => exact fun _ => ⟨_, rfl, CongUp.lit⟩
  | @var v i hlk =>
    intro hlink
    obtain ⟨t, ht, hc⟩ := hlink v (by simp [Expr.vars]) i hlk
    exact ⟨t, ht, .of_cong hc⟩
  | @app f args es i pf _ ho ih =>
    intro hlink
    obtain ⟨as, ham, hal, hae⟩ := hs f _ _ _ ho
    obtain ⟨hnp, hctor⟩ := hb f as ham
    obtain ⟨ts, hts, hup⟩ := ih (by simpa [Expr.vars] using hlink)
    refine ⟨.app f ts, by simp [Expr.eval, hnp, hctor, hts], fun D hcon hsub => ?_⟩
    have hlD : CongList D ts es :=
      CongUp.congList hcon hup fun t ht s hs' => hsub s (Term.arg_subterms ht hs')
    exact (Cong.congr (hsub _ (Term.self_mem_subterms _)) (hcon.terms ham)
      (hlD.trans (CongList.mono hcon hal).symm)).trans (Cong.mono hcon hae)
  | nil _ => exact ⟨[], rfl, .nil⟩
  | @cons a i as is _ _ ih ihl hlink =>
    obtain ⟨t, ht, hc⟩ := ih (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inl hv))
    obtain ⟨ts, hts, hcs⟩ := ihl (hlink.mono (by
      intro v hv; rw [Expr.varsList_cons, List.mem_union_iff]; exact Or.inr hv))
    exact ⟨t :: ts, by simp [Expr.evalList, ht, hts], .cons hc hcs⟩

end

/-- **The id a non-leaf read is a term the source holds.** The witness clause of `Matches`
asks for one, and this is where it comes from: `EntrySound` hands back a source application
congruent to the e-class column, and a variable's id is congruent to the source term
`Env.ReadsAs` gives it. Only a *literal* has no such witness, and that is the one case the
correspondence is refuted at. -/
theorem mem_terms_of_queryRead {src d : Database} (hs : d.ViewsSound src) {ρs ρt : Env}
    {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hlink : Env.ReadsAs src ρs ρt e.vars)
    (hnl : ∀ l, e ≠ .lit l) : i ∈ src.terms := by
  cases h with
  | lit => exact absurd rfl (hnl _)
  | var hlk =>
    obtain ⟨_, _, hc⟩ := hlink _ (by simp [Expr.vars]) _ hlk
    exact hc.mem_right
  | app _ ho =>
    obtain ⟨_, _, _, hae⟩ := hs _ _ _ _ ho
    exact hae.mem_right

/-! ### One pattern, matched

`Matches`' witness clause is where the two readings meet: the id the target read *is* a
term the source holds (`mem_terms_of_queryRead`), and the instance is congruent to it in the
database extended by the instance — which is exactly `withOperands`. This is why flattening
costs nothing: the intermediate class is found by matching rather than by having been
built. -/

/-- **A source pattern `.expr e` matches at the terms the target read.** -/
theorem matches_expr_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {τ ρt : Env} {e : Expr} {i : Term} (h : QueryRead d ρt e i)
    (hlink : Env.ReadsAs src (src.env ++ τ) ρt e.vars) (hnl : ∀ l, e ≠ .lit l) :
    Matches src (.expr e) τ := by
  obtain ⟨t, ht, hup⟩ := congUp_of_queryRead hb hs h hlink
  exact .expr (mem_terms_of_queryRead hs h hlink hnl) ht hup.congOn.symm

/-- **And a source pattern `.eq e₁ e₂` does**, because the encoded `.eq` atom compares the
two ids and the target is diagonal: one id for both sides, so the two instances are
congruent through it. Either side may be the witness, which is why only *one* of them has to
be more than a literal. -/
theorem matches_eq_of_queryRead {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {τ ρt : Env} {e₁ e₂ : Expr} {i : Term}
    (h₁ : QueryRead d ρt e₁ i) (h₂ : QueryRead d ρt e₂ i)
    (hlink : Env.ReadsAs src (src.env ++ τ) ρt (e₁.vars ∪ e₂.vars))
    (hnl : (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)) : Matches src (.eq e₁ e₂) τ := by
  have hl₁ : Env.ReadsAs src (src.env ++ τ) ρt e₁.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inl hv)
  have hl₂ : Env.ReadsAs src (src.env ++ τ) ρt e₂.vars :=
    hlink.mono fun v hv => List.mem_union_iff.mpr (Or.inr hv)
  obtain ⟨t₁, ht₁, hu₁⟩ := congUp_of_queryRead hb hs h₁ hl₁
  obtain ⟨t₂, ht₂, hu₂⟩ := congUp_of_queryRead hb hs h₂ hl₂
  have hi : i ∈ src.terms :=
    hnl.elim (fun hn => mem_terms_of_queryRead hs h₁ hl₁ hn)
      (fun hn => mem_terms_of_queryRead hs h₂ hl₂ hn)
  exact .eq hi ht₁ ht₂ hu₁.congOn_pair_left.symm
    (hu₁.congOn_pair_left.trans hu₂.congOn_pair_right.symm)

/-- **The pattern has a witness position.** `Matches` asks for a term the source *holds*
congruent to the instance, and a bare literal has none: the source may never have built it,
and `encodePattern` emits no atom that would say it did. Decidable, and a condition on the
source program's text rather than on either state. -/
def Pattern.Grounded : Pattern → Prop
  | .expr e => ∀ l, e ≠ .lit l
  | .eq e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∨ (∀ l, e₂ ≠ .lit l)
  | .values _ _ _ => True

@[inherit_doc matches_expr_of_queryRead]
theorem matches_of_patternRead {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {τ ρt : Env} {p : Pattern} (hg : p.Grounded)
    (h : PatternRead d ρt p) (hlink : Env.ReadsAs src (src.env ++ τ) ρt p.vars) :
    Matches src p τ := by
  cases h with
  | expr hr => exact matches_expr_of_queryRead hb hs hr hlink hg
  | eq h₁ h₂ => exact matches_eq_of_queryRead hb hs h₁ h₂ hlink hg

/-! ### From one reading per pattern to a query substitution

`ValidQuerySubst` wants one substitution per pattern, each binding exactly that pattern's
free variables, unioned. The source-side reading `g` is a *function* on variables, so the
per-pattern substitutions are `List.map`s of one list and `Env.exists_unionAll` does the
rest: they all refine the same total reading, so they are pairwise compatible. -/

/-- The source-side substitution one pattern gets. `List.map` over the free-variable list,
so `ValidEnv`'s permutation clause holds on the nose. -/
def sourceSubst (env : Env) (g : Var → Term) (p : Pattern) : Env :=
  (p.freeVars env).map fun v => (v, g v)

theorem dom_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} :
    Env.dom (sourceSubst env g p) = p.freeVars env := by
  simp [sourceSubst, Env.dom, List.map_map, Function.comp_def]

theorem lookup_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} {v : Var}
    (hv : v ∈ p.freeVars env) : Env.lookup v (sourceSubst env g p) = some (g v) :=
  (Env.lookup_eq_some_iff_mem (by rw [dom_sourceSubst]; exact p.freeVars_nodup env)).mpr
    (List.mem_map.mpr ⟨v, hv, rfl⟩)

/-- A variable a pattern mentions is read as `g` says, globals included: `hg` is what makes
the two agree where the source's own environment already binds it. -/
theorem lookup_append_sourceSubst {src : Database} {g : Var → Term} {p : Pattern}
    (hg : ∀ v t, Env.lookup v src.env = some t → g v = t) {v : Var} (hv : v ∈ p.vars) :
    Env.lookup v (src.env ++ sourceSubst src.env g p) = some (g v) := by
  cases hlk : Env.lookup v src.env with
  | some t =>
    rw [Env.lookup_append_of_mem (Env.lookup_isSome_iff_mem_dom.mp (by rw [hlk]; rfl)), hlk,
      hg v t hlk]
  | none =>
    rw [Env.lookup_append_of_not_mem (Env.lookup_eq_none_iff.mp hlk)]
    exact lookup_sourceSubst (p.mem_freeVars.mpr ⟨hv, Env.lookup_eq_none_iff.mp hlk⟩)

/-- `Query.vars` never repeats: it is built with `List.union`. -/
theorem Query.vars_nodup (q : Query) : (Query.vars q).Nodup := by
  induction q with
  | nil => simp [Query.vars]
  | cons p ps ih => exact List.Nodup.union _ ih

/-- **The rule-head match correspondence, as a property of the two states.**

The target read every pattern of the source query, and `g` reads its ids back as source
terms; then **the source query matches, at those very terms**. No `encode`, no `execM`, no
`Matches` on the target side — `Database.ViewsSound` and `Database.TermsBuild` are the whole
of what the two states contribute, and `Database.ViewsSound` is the invariant the
completeness half already rests on.

The second conjunct is what a rule *head* needs. `ValidQuerySubst` alone says the source rule
fired; this says it fired at `g`, so `entrySound_build`'s hypothesis — the source holds the
term the encoded head built — follows from the head's own source-side evaluation. -/
theorem validQuerySubst_of_patternReads {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {q : Query} {g : Var → Term} {ρt : Env}
    (hg : ∀ v t, Env.lookup v src.env = some t → g v = t)
    (hgt : ∀ v ∈ Query.vars q, g v ∈ src.terms)
    (hlink : ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i → Cong src (g v) i)
    (hgr : ∀ p ∈ q, p.Grounded) (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ v ∈ Query.vars q, Env.lookup v (src.env ++ τ) = some (g v) := by
  have hmem : ∀ p ∈ q, ∀ v ∈ p.vars, v ∈ Query.vars q := fun p hp v hv =>
    Query.mem_vars.mpr ⟨p, hp, hv⟩
  -- one substitution per pattern, all of them restrictions of `g`
  have hvalid : ∀ p ∈ q, ValidSubst src p (sourceSubst src.env g p) := by
    intro p hp
    refine ⟨⟨by rw [dom_sourceSubst], ?_⟩, ?_⟩
    · rintro b hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      exact hgt v (hmem p hp v (p.mem_freeVars.mp hv).1)
    · refine matches_of_patternRead hb hs (hgr p hp) (hread p hp) fun v hv i hi => ?_
      exact ⟨g v, lookup_append_sourceSubst hg hv, hlink v (hmem p hp v hv) i hi⟩
  -- they all refine one total reading, so they have a union
  have hnd : (Env.dom (Query.vars q |>.map fun v => (v, g v))).Nodup := by
    simpa [Env.dom, List.map_map, Function.comp_def] using Query.vars_nodup q
  have hrefines : ∀ ρ ∈ q.map (sourceSubst src.env g),
      Env.Refines ρ (Query.vars q |>.map fun v => (v, g v)) := by
    rintro ρ hρ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hρ
    rintro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    exact (Env.lookup_eq_some_iff_mem hnd).mpr
      (List.mem_map.mpr ⟨v, hmem p hp v (p.mem_freeVars.mp hv).1, rfl⟩)
  obtain ⟨τ, hu, -⟩ := Env.exists_unionAll _ hrefines
  have hself : ∀ ρ ∈ q.map (sourceSubst src.env g), Env.Refines ρ ρ := by
    rintro ρ hρ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
    exact Env.Refines.self_of_nodup (by rw [dom_sourceSubst]; exact p.freeVars_nodup _)
  obtain ⟨hall, -⟩ := hu.refines_of_mem hself
  refine ⟨τ, ⟨_, List.forall₂_map_self hvalid, hu⟩, fun v hv => ?_⟩
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hv
  cases hlk : Env.lookup v src.env with
  | some t =>
    rw [Env.lookup_append_of_mem (Env.lookup_isSome_iff_mem_dom.mp (by rw [hlk]; rfl)), hlk,
      hg v t hlk]
  | none =>
    rw [Env.lookup_append_of_not_mem (Env.lookup_eq_none_iff.mp hlk)]
    exact hall _ (List.mem_map.mpr ⟨p, hp, rfl⟩) (v, g v)
      (List.mem_map.mpr ⟨v, p.mem_freeVars.mpr ⟨hvp, Env.lookup_eq_none_iff.mp hlk⟩, rfl⟩)

/-! ### Where the source-side reading comes from

`validQuerySubst_of_patternReads` takes `g` as given. It exists for a variable the encoded
query reads **at a key column** and for no other: `EntrySound`'s existential *is* the source
argument list a key stands for, so the key's `j`th column hands back the source term
`g` needs. A variable that is a whole pattern, or a whole side of an equality, sits at no key
column — `encodeQueryExpr` returns a leaf unchanged and emits no atom for it — and there is
nothing to read it back from. -/

mutual

/-- The variable occurs as an **argument of an application**: a key column of one of the view
reads `encodeQueryExpr` emits. -/
def Expr.ArgVar (v : Var) : Expr → Prop
  | .lit _ => False
  | .var _ => False
  | .app _ args => Expr.var v ∈ args ∨ Expr.ArgVarList v args

/-- `Expr.ArgVar` over an argument list. -/
def Expr.ArgVarList (v : Var) : List Expr → Prop
  | [] => False
  | e :: es => Expr.ArgVar v e ∨ Expr.ArgVarList v es

end

@[inherit_doc Expr.ArgVar]
def Pattern.ArgVar (v : Var) : Pattern → Prop
  | .expr e => Expr.ArgVar v e
  | .eq e₁ e₂ => Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂
  | .values vs _ as => Expr.ArgVarList v vs ∨ Expr.ArgVarList v as

/-- **Every variable the query mentions sits at a key column.** The condition under which the
source-side reading `g` exists — a restriction on the source program's text, like
`Pattern.Grounded`, and refuted by the same patterns. -/
def Query.VarsKeyed (q : Query) : Prop := ∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p

mutual

/-- **A variable at a key column is read back as a source term.** The whole of where `g`
comes from: `ViewsSound` at the enclosing read hands back a source argument list congruent to
the key, and the variable's own column of it is the term. -/
theorem exists_source_of_argVar {src d : Database} (hs : d.ViewsSound src) {ρt : Env}
    {v : Var} {e : Expr} {i : Term} (h : QueryRead d ρt e i) (hv : Expr.ArgVar v e) :
    ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j := by
  cases h with
  | lit => exact absurd hv (by simp [Expr.ArgVar])
  | var => exact absurd hv (by simp [Expr.ArgVar])
  | @app f args es i pf hl ho =>
    obtain ⟨as, -, hal, -⟩ := hs f _ _ _ ho
    rcases hv with hv | hv
    · exact exists_source_of_memVar hl hal hv
    · exact exists_source_of_argVarList hs hl hv

/-- The variable is one of *this* read's key columns: pair off the reading with
`EntrySound`'s congruence and take the column. -/
theorem exists_source_of_memVar {src d : Database} {ρt : Env} {v : Var} :
    ∀ {args : List Expr} {es as : List Term}, QueryReadList d ρt args es →
      CongList src as es → Expr.var v ∈ args →
      ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j
  | _, _, _, .nil, _, hv => absurd hv (by simp)
  | _, _, _, .cons hr hl, hc, hv => by
    cases hc with
    | cons hc hcl =>
      rcases List.mem_cons.mp hv with rfl | hv
      · cases hr with
        | var hlk => exact ⟨_, _, hlk, hc⟩
      · exact exists_source_of_memVar hl hcl hv

@[inherit_doc exists_source_of_argVar]
theorem exists_source_of_argVarList {src d : Database} (hs : d.ViewsSound src) {ρt : Env}
    {v : Var} : ∀ {args : List Expr} {es : List Term}, QueryReadList d ρt args es →
      Expr.ArgVarList v args → ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j
  | _, _, .nil, hv => absurd hv (by simp [Expr.ArgVarList])
  | _, _, .cons hr hl, hv => by
    rcases hv with hv | hv
    · exact exists_source_of_argVar hs hr hv
    · exact exists_source_of_argVarList hs hl hv

end

@[inherit_doc exists_source_of_argVar]
theorem exists_source_of_patternArgVar {src d : Database} (hs : d.ViewsSound src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ j t, Env.lookup v ρt = some j ∧ Cong src t j := by
  cases h with
  | expr hr => exact exists_source_of_argVar hs hr hv
  | eq h₁ h₂ => exact hv.elim (exists_source_of_argVar hs h₁) (exists_source_of_argVar hs h₂)

/-- **A source global reads as an id congruent to the term it binds.** A source `let` becomes
a `let` of the built term's *id* in the target, so a query variable the source's own
environment binds is read from the target's environment rather than from the substitution.
The one clause of the correspondence that is about the two environments. -/
def Database.GlobalsRead (src : Database) (ρ : Env) : Prop :=
  ∀ v t i, Env.lookup v src.env = some t → Env.lookup v ρ = some i → Cong src t i

/-- **The source-side reading exists.** One source term per query variable, congruent to the
id the target read it as, and equal to the source's own binding wherever there is one.

`Query.VarsKeyed` is where it comes from and the only reason it is a hypothesis: a variable
at a key column is read back by `ViewsSound`, and one at no key column is read back by
nothing. -/
theorem exists_sourceReading {src d : Database} (hw : src.WF) (hs : d.ViewsSound src)
    {q : Query} {ρt : Env} (hglob : src.GlobalsRead ρt) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ g : Var → Term, (∀ v t, Env.lookup v src.env = some t → g v = t) ∧
      (∀ v ∈ Query.vars q, g v ∈ src.terms) ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i → Cong src (g v) i := by
  have hex : ∀ v : Var, ∃ t : Term,
      (∀ u, Env.lookup v src.env = some u → t = u) ∧
      (v ∈ Query.vars q → t ∈ src.terms ∧
        ∀ i, Env.lookup v ρt = some i → Cong src t i) := by
    intro v
    cases hlk : Env.lookup v src.env with
    | some u =>
      exact ⟨u, fun u' hu' => Option.some.inj (hlk ▸ hu'), fun _ =>
        ⟨hw.envInTerms _ (Env.mem_of_lookup hlk), fun i hi => hglob v u i hlk hi⟩⟩
    | none =>
      by_cases hv : v ∈ Query.vars q
      · obtain ⟨p, hp, ha⟩ := hk v hv
        obtain ⟨j, t, hj, hc⟩ := exists_source_of_patternArgVar hs (hread p hp) ha
        refine ⟨t, fun u' hu' => absurd hu' (by simp), fun _ =>
          ⟨hc.mem_left, fun i hi => ?_⟩⟩
        rw [hj] at hi
        exact Option.some.inj hi ▸ hc
      · exact ⟨.lit (.int 0), fun u' hu' => absurd hu' (by simp),
          fun hc => absurd hc hv⟩
  choose g hg hgv using hex
  exact ⟨g, fun v t ht => hg v t ht, fun v hv => (hgv v hv).1, fun v hv i hi => (hgv v hv).2 i hi⟩

/-- **The rule-head match correspondence, as a property of the two states.**

The encoded query matched in the target, therefore **the source query matches in the source
at congruent terms**: a substitution `τ` under which every pattern of `r.query` matches, and
for each variable the query binds a source term congruent to the id the encoded query bound
it to. That is what every writer in a rule head needs — `entrySound_build`'s hypothesis at a
build, `cong_of_eqs`' at a `union` — and it is the shared crux of both halves of
`encode_corresponds`.

No `encode` and no `execM`: what the target contributes is `Database.ViewsSound`, the same
invariant the completeness half already rests on, plus `Database.GlobalsRead`; what the
source contributes is `Database.WF` and `Database.TermsBuild`. `PatternRead` is the target's
reading of the flattened query, `out_of_matches_values` is what establishes it from one
encoded view read, and `Pattern.Grounded`/`Query.VarsKeyed` are the two side conditions on
the source program's text that the flattening forces — both refuted below at the pattern that
violates them. -/
theorem exists_validQuerySubst_of_patternReads {src d : Database} (hw : src.WF)
    (hb : src.TermsBuild) (hs : d.ViewsSound src) {q : Query} {ρt : Env}
    (hglob : src.GlobalsRead ρt) (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i →
        ∃ t, Env.lookup v (src.env ++ τ) = some t ∧ Cong src t i := by
  obtain ⟨g, hg, hgt, hlink⟩ := exists_sourceReading hw hs hglob hk hread
  obtain ⟨τ, hv, hτ⟩ := validQuerySubst_of_patternReads hb hs hg hgt hlink hgr hread
  exact ⟨τ, hv, fun v hv' i hi => ⟨g v, hτ v hv', hlink v hv' i hi⟩⟩

/-! ### What a head build still owes, and it is not this

The correspondence hands a rule head the source application over the source *terms* the query
matched. `encodeBuild` writes its entry over their **ids**: "the skolem is the answer, nothing
is read back", so building `(f x y)` at a head whose query bound `x`, `y` to the ids `i₁`, `i₂`
writes `@fView(i₁, i₂) ↦ (f i₁ i₂, @Fiat)` and `Database.addTerm` records the term `f(i₁, i₂)`.
`Database.ViewsSound` at that entry is then a statement about `f(i₁, i₂)` and not about
`f(τx, τy)`, and the two coincide only where no `union` has re-canonicalized an argument. -/

/-- **A fresh build's obligation is exactly that its minted id is a source term.**
`entrySound_build`'s hypothesis is necessary and not only sufficient, so the match
correspondence does not discharge the rule-head case of `Database.ViewsSound` by itself: it
gives the source application over the terms the query matched, and this asks for the one over
their ids. `encode_corresponds_invents_enode` is the same gap read at a key column instead of
an e-class one. -/
theorem mem_terms_of_entrySound_skolem {src : Database} {f : FnName} {cs : List Term}
    (h : EntrySound src f cs (.app f cs)) : Term.app f cs ∈ src.terms := by
  obtain ⟨_, _, _, hae⟩ := h
  exact Cong.mem_right hae

/-! ### Establishing the target-side hypothesis

One encoded view read becomes one `Database.Out`, and that step is where the target's
**diagonality** is spent: `Matches.values` relates the entry term to a witness *up to
congruence*, and on a state that asserts no equation but the reflexive one that means the
entry term itself. `encode` emits no `union` (`encode_unionFree`), so its targets are
diagonal — the fact `Encoding/Correspond.lean` already establishes and decides.

Nothing here assumes a view table is **functional**: `Database.Out` is read existentially and
two entries at one key give two independent `Database.Out`s. -/

/-- **At a diagonal target a view read is a table lookup.** The witness is congruent to the
entry term, congruence is equality there, so the entry term is one the target holds and
`Database.Out` reads it back syntactically. Subterm closure is what turns the key columns into
terms, which `Database.Out`'s reflexive `CongList` needs. -/
theorem out_of_matches_values {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {vs as : List Expr} {f : FnName} {σ : Env}
    (h : Matches d (.values vs f as) σ) :
    ∃ ts us, Expr.evalList d.sig as (d.env ++ σ) = some ts ∧
      Expr.evalList d.sig vs (d.env ++ σ) = some us ∧
      Term.app f (ts ++ us) ∈ d.terms ∧ d.Out f ts us := by
  cases h with
  | @values vs f as σ us ts w hw hts hus hc =>
    obtain rfl : w = Term.app f (ts ++ us) := congOn_eq_of_diag hd hc
    refine ⟨ts, us, hts, hus, hw, ts, CongList.refl fun a ha => ?_, hw⟩
    exact hsc _ hw (Term.arg_subterms (List.mem_append_left _ ha) (Term.self_mem_subterms a))

/-- **The residue: reading the encoded query back off the encoder. Not proved.**

What is missing, and nothing else: that a matched *encoded* query is a `PatternRead` of the
source query it came from. Three steps stand between `out_of_matches_values` and this.

* **The per-atom substitutions have to be merged into one.** `ValidQuerySubst` gives one
  substitution per encoded atom, each refining `σ` (`Env.UnionAll.refines_of_mem`), and
  `Matches` reads only the atom's own variables — so each atom matches under `σ` too. What is
  absent is the partial-agreement congruence for `Expr.eval`: `ValidSubst.of_agree` asks
  agreement everywhere, and here the two environments agree only on the atom's variables.
* **The atoms of one source pattern have to be located in the encoded query.**
  `encodeQuery` is a concatenation and `encodePattern` threads a counter, so
  `∀ p ∈ q, ∃ m, (encodePattern p m).1 ⊆ (encodeQuery q n).1` is an induction on `q` carrying
  the counter. Nothing subtle, but it is the *flattening*: `@Rule_i`'s premise count is the
  emitted read count, not the source pattern count, and the block belonging to one source
  pattern is what this identifies.
* **The reads of one source expression have to be folded into one `QueryRead`.** A mutual
  induction over `encodeQueryExpr`/`encodeQueryArgs`, one `out_of_matches_values` per emitted
  read, joined on the generated e-class variable — which the emitted atom binds as its first
  value column and the parent atom reads as a key column, so the join is by construction.

`Query.VarsKeyed` is needed here and not only downstream: a source pattern that is a bare
variable gets no atom, so nothing in the encoded query binds it, and `QueryRead.var` has no
premise to offer unless some *other* pattern reads it at a key column. -/
theorem patternReads_of_encodeQuery {tgt : Database} (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hnv : ∀ p ∈ q, p.NoValues) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∀ p ∈ q, PatternRead tgt (tgt.env ++ σ) p := by
  sorry

/-- **The correspondence in the form a rule head consumes.** The state-level theorem composed
with the residue above, so this is what carries `sorryAx`: the mathematics is
`exists_validQuerySubst_of_patternReads`, and what is missing is reading the encoder. -/
theorem exists_validQuerySubst_of_encodeQuery {src tgt : Database} (hw : src.WF)
    (hb : src.TermsBuild) (hs : tgt.ViewsSound src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hglob : src.GlobalsRead (tgt.env ++ σ)) (hnv : ∀ p ∈ q, p.NoValues)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v (tgt.env ++ σ) = some i →
        ∃ t, Env.lookup v (src.env ++ τ) = some t ∧ Cong src t i :=
  exists_validQuerySubst_of_patternReads hw hb hs hglob hgr hk
    (patternReads_of_encodeQuery hd hsc hnv hk h)

/-! ### The refutation: `encodeQuery` drops a leaf pattern

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, emitting no atom
for it, so `encodePattern` maps a source pattern whose expression is a bare literal to the
**empty** list of atoms. A dropped constraint is a rule the target fires and the source does
not, and the correspondence is false without `Pattern.Grounded`.

The same defect at a bare *variable* is `Query.VarsKeyed`: `.expr (.var v)` gets no atom
either, so nothing in the encoded query binds `v` and the head reads it unbound — which the
source rule, whose `ValidEnv` must bind it to a term the source holds, does not do.

Both are conditions on the source program's **text**, decidable, and neither is implied by
`Program.EncodeDomain` — `litProgram` below is in the domain. -/

/-- The source state `satProgram` reaches, read for its terms: `(A)` and nothing else. -/
theorem satSrc_terms : satSrc.terms = (Term.app "A" []).subterms := by simp [satSrc]

/-- Only `Database.addTerm` writes it, so it is diagonal — which is what makes the
refutation's witness clause collapse to equality. -/
theorem satSrc_diag : satSrc.Diag := by
  have h : Database.Diag Database.empty := fun p hp => absurd hp (by simp [Database.empty])
  exact h.addTerm _

/-- `(rule ((1)) ())`: one pattern, a bare literal. -/
def litQuery : Query := [.expr (.lit (.int 1))]

/-- The program that is nothing but that rule. -/
def litProgram : Program := [.rule { query := litQuery, actions := [], ruleset := "" }]

/-- **It is inside the encoder's declared domain.** -/
theorem litProgram_encodeDomain : litProgram.EncodeDomain where
  ctorsOnly := by simp [litProgram]
  noSet := by simp [litProgram, Cmd.NoSet, litQuery, Pattern.NoValues]
  noPrim := by simp [litProgram, Program.ctors, Cmd.ctors, litQuery, Pattern.ctors, Expr.ctors]
  noAt := by simp [litProgram, Program.ctors, Cmd.ctors, litQuery, Pattern.ctors, Expr.ctors]
  noAtVar := by
    simp [litProgram, Program.vars, Cmd.vars, litQuery, Query.vars, Pattern.vars, Expr.vars]
  noAtRuleset := by
    simp only [litProgram, Program.rulesets, Cmd.rulesets, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_dedup, List.mem_singleton]
    rintro R rfl
    exact of_decide_eq_false rfl

/-- **And `encodeQuery` emits nothing for it.** -/
theorem encodeQuery_litQuery : (encodeQuery litQuery 0).1 = [] := rfl

/-- **The correspondence is false without `Pattern.Grounded`.** The encoded query is empty,
so it matches under the empty substitution at every target; the source query matches under
*no* substitution at `satProgram`'s own source state, which holds `(A)` and no literal.
Compiled, and `Pattern.Grounded` is exactly the side condition that excludes it. -/
theorem encodeQuery_drops_literal_pattern :
    ValidQuerySubst satTarget (encodeQuery litQuery 0).1 [] ∧
      (∀ τ, ¬ ValidQuerySubst satSrc litQuery τ) ∧
      ¬ (∀ p ∈ litQuery, Pattern.Grounded p) := by
  refine ⟨by rw [encodeQuery_litQuery]; exact ValidQuerySubst.nil_iff.mpr rfl, ?_, ?_⟩
  · rintro τ ⟨σs, hall, -⟩
    cases hall with
    | cons hv _ =>
      obtain ⟨-, hm⟩ := hv
      cases hm with
      | @expr e σ w t hw hev hc =>
        obtain rfl : t = Term.lit (.int 1) := (Option.some.inj hev).symm
        obtain rfl : w = Term.lit (.int 1) := congOn_eq_of_diag satSrc_diag hc
        rw [satSrc_terms] at hw
        simp at hw
  · intro h
    have hgd : Pattern.Grounded (.expr (.lit (.int 1))) := h _ (by simp [litQuery])
    exact hgd (.int 1) rfl

/-! ### The witness

`Encoding/Correspond.lean`'s discipline: before any hypothesis introduced above is allowed to
stand, it is discharged at a state a program *reaches*, and the premise it guards is checked
inhabited there. `satProgram` is the same program both files use; `satProgram_programStep` is
the target's half of the reachability and `satProgramStep_src` below is the source's, which
`Encoding/Correspond.lean` did not need because `Cong` does not read the signature and
`Expr.eval` does.

**One clause is carried vacuously at that pair and is discharged separately.**
`Database.GlobalsRead` is about the two environments and `satProgram` has no `let`, so both
are empty there; `globalsRead_nonvacuous` is the same clause at a state that binds a
global. -/

/-- `A`'s declaration, the one `satProgram`'s first command makes. -/
def satCtorDecl : FnDecl := { arity := 0, outArity := 1, merge := none }

/-- The signature after that command, and nothing else. -/
def satSrcSig : Signature := Function.update Database.empty.sig "A" (some satCtorDecl)

/-- **The source state `satProgram` runs to.** `Encoding/Correspond.lean`'s `satSrc` drops the
declaration, which costs it nothing — `Cong` does not read the signature — and costs this file
everything, since `Expr.eval` does: without it the source-side reading of `(A)` is stuck. -/
def satSrcD : Database :=
  ({ Database.empty with sig := satSrcSig }).addTerm (.app "A" [])

theorem satSrcD_eqs : satSrcD.eqs = satSrc.eqs := rfl

private theorem satSrcBase_terms :
    ({ Database.empty with sig := satSrcSig } : Database).terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [Database.empty] at hu

theorem satSrcD_terms : satSrcD.terms = (Term.app "A" []).subterms := by
  rw [satSrcD, Database.addTerm_terms, satSrcBase_terms, Set.empty_union]

/-- **And it is reachable**: two commands, each a `cmdEffect` and a reflexive merge phase. The
source-side counterpart of `satProgram_programStep`. -/
theorem satProgramStep_src : ProgramStep Database.empty satProgram satSrcD := by
  refine .cons ⟨_, rfl, .refl⟩ (.cons ⟨satSrcD, ?_, .refl⟩ .nil)
  change cmdEffect _ (.action (.expr (.app "A" []))) = some satSrcD
  simp only [cmdEffect, evalAction, Expr.eval, Expr.evalList, satSrcD]
  rfl

private theorem satSrcBase_wf : ({ Database.empty with sig := satSrcSig } : Database).WF where
  eqsRefl := fun t ht => absurd (satSrcBase_terms ▸ ht) (by simp)
  subtermClosed := fun t ht => absurd (satSrcBase_terms ▸ ht) (by simp)
  envInTerms := by simp [Database.empty]
  litsIsolated := by simp [Database.LitsIsolated, Database.empty]

theorem satSrcD_wf : satSrcD.WF := satSrcBase_wf.addTerm _

/-- **`Database.TermsBuild` holds at it**, non-vacuously: the one term it holds is `(A)`, and
`A` is declared and shadows no primitive. -/
theorem satSrcD_termsBuild : satSrcD.TermsBuild := by
  intro f as hm
  rw [satSrcD_terms] at hm
  obtain ⟨rfl, rfl⟩ : f = "A" ∧ as = [] := by simpa [Term.subterms_app] using hm
  exact ⟨rfl, satCtorDecl, by simp [satSrcD, satSrcSig], rfl⟩

theorem satSrcD_mem : Term.app "A" [] ∈ satSrcD.terms := by
  rw [satSrcD_terms]; exact Term.self_mem_subterms _

/-- `Database.ViewsSound` reads only `eqs`, so it transports along an equality of them —
which is all that separates `satSrc` from the state the source program actually reaches. -/
theorem EntrySound.congr_eqs {s s' : Database} (he : s.eqs = s'.eqs) {f : FnName}
    {cs : List Term} {e : Term} (h : EntrySound s f cs e) : EntrySound s' f cs e :=
  let hc : s.Contained s' := ⟨he.subset⟩
  let ⟨as, ham, hal, hae⟩ := h
  ⟨as, hc.terms ham, CongList.mono hc hal, Cong.mono hc hae⟩

@[inherit_doc EntrySound.congr_eqs]
theorem Database.ViewsSound.congr_eqs {d s s' : Database} (h : d.ViewsSound s)
    (he : s.eqs = s'.eqs) : d.ViewsSound s' :=
  fun f cs e pf ho => (h f cs e pf ho).congr_eqs he

theorem satTarget_viewsSound_srcD : satTarget.ViewsSound satSrcD :=
  satTarget_viewsSound.congr_eqs satSrcD_eqs.symm

/-- The target's subterm closure, which is what turns a matched view read into a
`Database.Out`. -/
theorem satTarget_subtermClosed : ∀ t ∈ satTarget.terms, t.subterms ⊆ satTarget.terms := by
  intro t ht
  rw [satTarget_terms] at ht ⊢
  exact ht.elim (fun h => (Term.subterms_subset_of_mem h).trans Set.subset_union_left)
    (fun h => (Term.subterms_subset_of_mem h).trans Set.subset_union_right)

/-- **A view read really matches there**, so `out_of_matches_values` is not carried by an
empty premise: `satRebuildRule`'s own first atom, at the entry the build wrote. -/
theorem satTarget_matches_view :
    Matches satTarget (.values [.var "@e", .var "@p"] (viewName "A") [])
      [("@e", .app "A" []), ("@p", .app fiatName [])] :=
  .values satTarget_mem_view rfl rfl (Database.mem_addTerm _ _)

/-- **And `out_of_matches_values` reads it back as a lookup**, at the entry the build wrote. -/
theorem satTarget_out_view : satTarget.Out (viewName "A") [] [.app "A" [], .app fiatName []] := by
  obtain ⟨ts, us, hts, hus, -, ho⟩ :=
    out_of_matches_values satTarget_diag satTarget_subtermClosed satTarget_matches_view
  obtain rfl : ts = [] := Option.some.inj hts.symm
  obtain rfl : us = [.app "A" [], .app fiatName []] := Option.some.inj hus.symm
  exact ho

/-- **The premise of the correspondence is inhabited**: the target's reading of the source
pattern `(A)`, which is the whole of `satProgram`'s one action read as a query. -/
theorem satTarget_patternRead : PatternRead satTarget [] (.expr (.app "A" [])) :=
  .expr (.app .nil satTarget_out_view)

/-- **`Database.GlobalsRead` at a state that binds a global**, so the clause is not carried by
its vacuous case at `satProgram`, which has no `let`. -/
theorem globalsRead_nonvacuous :
    ({ satSrcD with env := [("x", .app "A" [])] } : Database).GlobalsRead
      [("x", .app "A" [])] := by
  intro v t i ht hi
  obtain ⟨-, rfl⟩ : v = "x" ∧ Term.app "A" [] = t := by simpa using ht
  obtain ⟨-, rfl⟩ : v = "x" ∧ Term.app "A" [] = i := by simpa using hi
  have hmem : Term.app "A" [] ∈ satSrcD.terms := by
    rw [satSrcD_terms]; exact Term.self_mem_subterms _
  exact Cong.mono (d₁ := satSrcD)
    (d₂ := { satSrcD with env := [("x", Term.app "A" [])] }) ⟨subset_rfl⟩ hmem

/-- **The variable path, exercised.** `satProgram`'s one view entry has a *nullary* key, so the
end-to-end witness below drives `congUp_of_queryRead` through its application case and through
`Database.ViewsSound` but never through a key column. These two check that path directly at the
same pair of states: a variable read as an id, and `exists_source_of_memVar` handing the source
term back out of one `CongList`.

What no reachable witness checks is the two *composed* — a source application one of whose
arguments is a variable — because no program `Encoding/Correspond.lean` steps declares a
constructor of positive arity. -/
theorem congUp_var_witness :
    ∃ t, (Expr.var "x").eval satSrcD.sig [("x", Term.app "A" [])] = some t ∧
      CongUp satSrcD t (Term.app "A" []) := by
  refine congUp_of_queryRead (d := satTarget) (ρt := [("x", Term.app "A" [])])
    satSrcD_termsBuild satTarget_viewsSound_srcD (.var (by simp)) fun v hv i hi => ?_
  obtain rfl : v = "x" := by rw [Expr.vars_var, List.mem_singleton] at hv; exact hv
  obtain rfl : Term.app "A" [] = i := by simpa using hi
  exact ⟨_, by simp, satSrcD_mem⟩

@[inherit_doc congUp_var_witness]
theorem exists_source_of_memVar_witness :
    ∃ j t, Env.lookup "x" [("x", Term.app "A" [])] = some j ∧ Cong satSrcD t j :=
  exists_source_of_memVar (d := satTarget) (args := [Expr.var "x"])
    (es := [Term.app "A" []]) (as := [Term.app "A" []]) (.cons (.var (by simp)) .nil)
    (.cons satSrcD_mem .nil) (by simp)

/-- **All of the correspondence's hypotheses hold together at a reachable pair of states, its
premise is inhabited there, and its conclusion is what comes out.**

`satProgramStep_src` and `satProgram_programStep` are the two reachabilities;
`Database.GlobalsRead` is the one clause vacuous here, discharged at
`globalsRead_nonvacuous`. The final conjunct is the correspondence run at that pair: the
source query `((A))` matches, which is exactly what a rule head building `(A)` would need. -/
theorem exists_validQuerySubst_witness :
    satSrcD.WF ∧ satSrcD.TermsBuild ∧ satTarget.ViewsSound satSrcD ∧
      satSrcD.GlobalsRead [] ∧ PatternRead satTarget [] (.expr (.app "A" [])) ∧
      ∃ τ, ValidQuerySubst satSrcD [Pattern.expr (.app "A" [])] τ := by
  refine ⟨satSrcD_wf, satSrcD_termsBuild, satTarget_viewsSound_srcD,
    by simp [Database.GlobalsRead], satTarget_patternRead, ?_⟩
  obtain ⟨τ, hτ, -⟩ := exists_validQuerySubst_of_patternReads (d := satTarget)
    (q := [Pattern.expr (.app "A" [])]) (ρt := []) satSrcD_wf satSrcD_termsBuild
    satTarget_viewsSound_srcD (by simp [Database.GlobalsRead])
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; intro l; simp)
    (by intro v hv; simp [Query.vars, Pattern.vars, Expr.vars, Expr.varsList] at hv)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact satTarget_patternRead)
  exact ⟨τ, hτ⟩

end Egglog
