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
lookup. `patternReads_of_encodeQuery` is that hypothesis established from the encoder itself,
so `exists_validQuerySubst_of_encodeQuery` consumes a match of the *emitted* query and nothing
hand-written. `encodeQuery` **flattens**, so one source pattern becomes several reads and
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
`Query.VarsKeyed` is its counterpart for the bare-*variable* half. Both are restrictions on
the *source program's text*, and both are now clauses of **`Program.EncodeDomain`**
(`EncodeDomain.noLeafPattern`), so the program the refutation is about is outside the
encoder's declared domain rather than inside it — `litProgram_not_encodeDomain`.

## Where it is checked

`Encoding/Correspond.lean`'s discipline: every hypothesis is discharged at a state some
program *reaches*, and the premise it guards is checked inhabited there.
`exists_validQuerySubst_witness` does that at `satProgram`, whose one constructor is
**nullary** — so `congUp_of_queryRead`'s application case runs at an empty argument list,
there is no key column anywhere, and `Query.VarsKeyed` is vacuous.
`exists_validQuerySubst_composed_witness` is the case the correspondence was written for: a
**unary** constructor, a rule whose query is `((F x))`, both runs stepped, and `VarsKeyed`
non-vacuous. It runs the whole path, `encodeQuery`'s own output included — the encoded query's
match is `wTarget_validQuerySubst`, and `patternReads_of_encodeQuery` is what turns it into the
reading. `Database.GlobalsRead` is the one clause no pair reached here makes non-vacuous, and
`globalsRead_nonvacuous` is that clause at a state binding a global.
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
nothing to read it back from. `Expr.ArgVar` and `Query.VarsKeyed` are `Encoding/Encode.lean`'s,
next to the domain clause that now demands them. -/

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
violates them, and both folded into `Program.EncodeDomain`. -/
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

/-! ### Reading the encoded query back off the encoder

`encodeQuery` **flattens**: one source pattern becomes a contiguous run of view reads, and the
runs of the whole query are concatenated with the fresh-variable counter threaded through. So
recovering the source pattern from the matched encoding is three separate moves — pick the run
belonging to one pattern out of the concatenation, see each atom of that run as matching under
the *joined* substitution rather than its own, and fold the run's reads back into the single
`QueryRead` the source expression's shape calls for.

The counter is never reasoned about, only carried: every statement below is existential in it
or quantified over it, so no two patterns' atoms are conflated through it. -/

/-! #### The emitted atoms, per case

`rfl` for each projection of the encoder's output tuples that the induction rewrites with. -/

theorem encodeQueryExpr_var {v : Var} {n : Nat} :
    encodeQueryExpr (.var v) n = (.var v, [], n) := rfl

/-- An application's naming expression is the **generated e-class variable**, numbered after
its arguments' reads. -/
theorem encodeQueryExpr_app_expr {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).1 = .var (freshVar (encodeQueryArgs args n).2.2) := rfl

/-- And its atoms are its arguments' reads, then **one** view read keyed on their naming
expressions and binding both value columns. -/
theorem encodeQueryExpr_app_atoms {f : FnName} {args : List Expr} {n : Nat} :
    (encodeQueryExpr (.app f args) n).2.1 =
      (encodeQueryArgs args n).2.1 ++
        [.values [.var (freshVar (encodeQueryArgs args n).2.2),
            .var (freshVar ((encodeQueryArgs args n).2.2 + 1))]
          (viewName f) (encodeQueryArgs args n).1] := rfl

@[inherit_doc encodeQueryExpr_app_expr]
theorem encodeQueryArgs_cons_exprs {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).1 =
      (encodeQueryExpr e n).1 :: (encodeQueryArgs es (encodeQueryExpr e n).2.2).1 := rfl

@[inherit_doc encodeQueryExpr_app_atoms]
theorem encodeQueryArgs_cons_atoms {e : Expr} {es : List Expr} {n : Nat} :
    (encodeQueryArgs (e :: es) n).2.1 =
      (encodeQueryExpr e n).2.1 ++ (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.1 := rfl

/-- `.expr e` emits exactly `e`'s reads, and **discards** the naming expression: "`e` is
present" is what the reads already say. -/
theorem encodePattern_expr_atoms {e : Expr} {n : Nat} :
    (encodePattern (.expr e) n).1 = (encodeQueryExpr e n).2.1 := rfl

/-- `.eq` emits both sides' reads and then compares the two naming expressions — id equality,
which at a diagonal target is equality. -/
theorem encodePattern_eq_atoms {e₁ e₂ : Expr} {n : Nat} :
    (encodePattern (.eq e₁ e₂) n).1 =
      (encodeQueryExpr e₁ n).2.1 ++
        (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).2.1 ++
        [.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1] := rfl

@[inherit_doc encodeQuery]
theorem encodeQuery_cons_atoms {p : Pattern} {ps : Query} {n : Nat} :
    (encodeQuery (p :: ps) n).1 =
      (encodePattern p n).1 ++ (encodeQuery ps (encodePattern p n).2).1 := rfl

/-! #### Locating one source pattern's block -/

/-- **One source pattern's atoms are among the query's.** The flattening in the form the
correspondence uses: `@Rule_i`'s premise count is the emitted read count and not the source
pattern count, and this is what picks out the block belonging to one source pattern.

The counter it is emitted at is existential, because the block sits at whatever number the
patterns before it left behind. A `⊆` and not a `Sublist`: nothing downstream needs the run to
be contiguous, only that every atom of it is an atom of the whole query. -/
theorem encodePattern_subset_encodeQuery {p : Pattern} : ∀ {q : Query}, p ∈ q → ∀ n : Nat,
    ∃ m, (encodePattern p m).1 ⊆ (encodeQuery q n).1
  | [], hp, _ => absurd hp (by simp)
  | p' :: ps, hp, n => by
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨n, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inl ha)⟩
    · obtain ⟨m, hm⟩ := encodePattern_subset_encodeQuery hp' (encodePattern p' n).2
      exact ⟨m, by
        rw [encodeQuery_cons_atoms]; exact fun a ha => List.mem_append.mpr (Or.inr (hm ha))⟩

/-! #### Folding one source expression's reads into one `QueryRead`

The atoms of one block all match under the joined substitution — `ValidQuerySubst.matches_of_mem`,
which is where the partial-agreement congruence `Expr.eval_agreeOn` is spent — and from there
the recursion is `encodeQueryExpr`'s own: one `out_of_matches_values` per emitted read, joined
on the generated e-class variable, which the emitted atom binds as its first value column and
the parent atom reads as a key column.

Nothing here asks a view table to be functional. Each read is turned into a `Database.Out`
independently and `QueryRead` carries the id the *substitution* bound, so two entries at one
key are two readings rather than a contradiction. -/

/-- A variable argument is its own naming expression, so it survives into the emitted atom's
key columns. -/
theorem mem_encodeQueryArgs_of_mem {v : Var} : ∀ {args : List Expr} {n : Nat},
    Expr.var v ∈ args → Expr.var v ∈ (encodeQueryArgs args n).1
  | [], _, h => absurd h (by simp)
  | a :: as, n, h => by
    rw [encodeQueryArgs_cons_exprs]
    rcases List.mem_cons.mp h with rfl | h'
    · rw [encodeQueryExpr_var]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_encodeQueryArgs_of_mem h')

mutual

/-- **A variable at a key column is bound by the match.** The emitted read that has `v` in its
key columns cannot match without `Expr.evalList` succeeding there, and that is a lookup.

This is the target-side half of what `Query.VarsKeyed` buys: a source pattern that is a bare
variable emits no atom, so its own reads say nothing about it, and the *other* pattern that
mentions it at a key column is where its binding comes from. -/
theorem lookup_isSome_of_argVar {d : Database} {σ : Env} {v : Var} :
    ∀ (e : Expr) (n : Nat), (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.ArgVar v e → (Env.lookup v (d.env ++ σ)).isSome
  | .lit _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .var _, _, _, hv => absurd hv (by simp [Expr.ArgVar])
  | .app f args, n, hm, hv => by
    rw [encodeQueryExpr_app_atoms] at hm
    rcases hv with hv | hv
    · cases hm (.values [.var (freshVar (encodeQueryArgs args n).2.2),
          .var (freshVar ((encodeQueryArgs args n).2.2 + 1))]
          (viewName f) (encodeQueryArgs args n).1) (by simp) with
      | values _ hts _ _ =>
        exact Expr.lookup_isSome_of_mem_evalList hts (mem_encodeQueryArgs_of_mem hv)
    · exact lookup_isSome_of_argVarList args n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv

@[inherit_doc lookup_isSome_of_argVar]
theorem lookup_isSome_of_argVarList {d : Database} {σ : Env} {v : Var} :
    ∀ (es : List Expr) (n : Nat), (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.ArgVarList v es → (Env.lookup v (d.env ++ σ)).isSome
  | [], _, _, hv => absurd hv (by simp [Expr.ArgVarList])
  | e :: es, n, hm, hv => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl ha))) hv
    · exact lookup_isSome_of_argVarList es (encodeQueryExpr e n).2.2
        (fun a ha => hm a (List.mem_append.mpr (Or.inr ha))) hv

end

@[inherit_doc lookup_isSome_of_argVar]
theorem lookup_isSome_of_patternArgVar {d : Database} {σ : Env} {v : Var} :
    ∀ (p : Pattern) (n : Nat), p.NoValues →
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → Pattern.ArgVar v p →
      (Env.lookup v (d.env ++ σ)).isSome
  | .expr e, n, _, hm, hv => lookup_isSome_of_argVar e n hm hv
  | .eq e₁ e₂, n, _, hm, hv => by
    rw [encodePattern_eq_atoms] at hm
    rcases hv with hv | hv
    · exact lookup_isSome_of_argVar e₁ n
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha))))) hv
    · exact lookup_isSome_of_argVar e₂ (encodeQueryExpr e₁ n).2.2
        (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha))))) hv
  | .values _ _ _, _, hnv, _, _ => absurd hnv id

/-- **The naming expression evaluates.** An application's is the e-class variable its own read
binds, a literal's is itself — and a bare *variable*'s is the variable, which no emitted atom
binds, so that case is exactly where the hypothesis is spent. -/
theorem exists_eval_encodeQueryExpr {d : Database} {σ : Env} :
    ∀ (e : Expr) (n : Nat), (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      (∀ v ∈ e.vars, (Env.lookup v (d.env ++ σ)).isSome) →
      ∃ i, Expr.eval d.sig (encodeQueryExpr e n).1 (d.env ++ σ) = some i
  | .lit l, _, _, _ => ⟨.lit l, rfl⟩
  | .var v, _, _, hb => Option.isSome_iff_exists.mp (hb v (by simp))
  | .app f args, n, hm, _ => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var]
    cases hm (.values [.var (freshVar (encodeQueryArgs args n).2.2),
        .var (freshVar ((encodeQueryArgs args n).2.2 + 1))]
        (viewName f) (encodeQueryArgs args n).1) (by simp) with
    | values _ _ hus _ =>
      exact Option.isSome_iff_exists.mp (Expr.lookup_isSome_of_mem_evalList hus (by simp))

/-- A read binds two value columns, so its match pins a two-element list: the e-class and the
premise proof, in that order. -/
private theorem evalList_two_vars {sig : Signature} {x y : Var} {ρ : Env} {us : List Term}
    (h : Expr.evalList sig [.var x, .var y] ρ = some us) :
    ∃ a b, Env.lookup x ρ = some a ∧ Env.lookup y ρ = some b ∧ us = [a, b] := by
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨us', hus', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Expr.evalList_cons, Option.bind_eq_some_iff] at hus'
  obtain ⟨b, hb, hus'⟩ := hus'
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hus'
  obtain rfl : w = [] := (Option.some.inj hw).symm
  rw [Expr.eval_var] at ha hb
  exact ⟨a, b, ha, hb, rfl⟩

mutual

/-- **One source expression's emitted reads, folded into one `QueryRead`.** The id is the one
the naming expression evaluates to: for an application, the value the match gave the generated
e-class variable, which the emitted read's own `Database.Out` carries as its first value
column.

`Database.Diag` is spent once per read, inside `out_of_matches_values`. -/
theorem queryRead_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (e : Expr) (n : Nat) {i : Term}, (∀ a ∈ (encodeQueryExpr e n).2.1, Matches d a σ) →
      Expr.eval d.sig (encodeQueryExpr e n).1 (d.env ++ σ) = some i →
      QueryRead d (d.env ++ σ) e i
  | .lit l, _, _, _, hi => by
    obtain rfl : Term.lit l = _ := Option.some.inj hi
    exact .lit
  | .var _, _, _, _, hi => .var hi
  | .app f args, n, i, hm, hi => by
    rw [encodeQueryExpr_app_atoms] at hm
    rw [encodeQueryExpr_app_expr, Expr.eval_var] at hi
    obtain ⟨ts, us, hts, hus, -, ho⟩ :=
      out_of_matches_values hd hsc (hm (.values
        [.var (freshVar (encodeQueryArgs args n).2.2),
          .var (freshVar ((encodeQueryArgs args n).2.2 + 1))]
        (viewName f) (encodeQueryArgs args n).1) (by simp))
    obtain ⟨a, b, ha, -, rfl⟩ := evalList_two_vars hus
    obtain rfl : a = i := Option.some.inj (ha.symm.trans hi)
    exact .app (queryReadList_of_matches hd hsc args n
      (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) hts) ho

@[inherit_doc queryRead_of_matches]
theorem queryReadList_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (es : List Expr) (n : Nat) {ts : List Term},
      (∀ a ∈ (encodeQueryArgs es n).2.1, Matches d a σ) →
      Expr.evalList d.sig (encodeQueryArgs es n).1 (d.env ++ σ) = some ts →
      QueryReadList d (d.env ++ σ) es ts
  | [], _, _, _, h => by
    obtain rfl : ([] : List Term) = _ := Option.some.inj h
    exact .nil
  | e :: es, n, ts, hm, h => by
    rw [encodeQueryArgs_cons_atoms] at hm
    rw [encodeQueryArgs_cons_exprs, Expr.evalList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h'⟩ := h
    obtain ⟨us, hus, rfl⟩ := Option.map_eq_some_iff.mp h'
    exact .cons (queryRead_of_matches hd hsc e n
        (fun x hx => hm x (List.mem_append.mpr (Or.inl hx))) ht)
      (queryReadList_of_matches hd hsc es (encodeQueryExpr e n).2.2
        (fun x hx => hm x (List.mem_append.mpr (Or.inr hx))) hus)

end

/-- **One source pattern's block, folded into one `PatternRead`.**

A `.eq` needs no bound-variables hypothesis: its emitted `.eq` atom evaluates *both* naming
expressions itself, and at a diagonal target it forces the two ids equal — which is the single
id `PatternRead.eq` asks for. A `.expr` needs one, and only at a bare variable.

`Pattern.NoValues` is a fragment restriction and not a gap: `encodePattern` passes a source
entry atom through unchanged and `PatternRead` has no case for it. -/
theorem patternRead_of_matches {d : Database} (hd : d.Diag)
    (hsc : ∀ t ∈ d.terms, t.subterms ⊆ d.terms) {σ : Env} :
    ∀ (p : Pattern) (n : Nat), p.NoValues →
      (∀ v ∈ p.vars, (Env.lookup v (d.env ++ σ)).isSome) →
      (∀ a ∈ (encodePattern p n).1, Matches d a σ) → PatternRead d (d.env ++ σ) p
  | .expr e, n, _, hb, hm => by
    rw [encodePattern_expr_atoms] at hm
    obtain ⟨i, hi⟩ := exists_eval_encodeQueryExpr e n hm hb
    exact .expr (queryRead_of_matches hd hsc e n hm hi)
  | .eq e₁ e₂, n, _, _, hm => by
    rw [encodePattern_eq_atoms] at hm
    cases hm (.eq (encodeQueryExpr e₁ n).1 (encodeQueryExpr e₂ (encodeQueryExpr e₁ n).2.2).1)
        (by simp) with
    | @eq _ _ _ w t₁ t₂ hw he₁ he₂ hc₁ hc₂ =>
      obtain rfl : t₁ = t₂ := congOn_eq_of_diag hd hc₂
      exact .eq
        (queryRead_of_matches hd hsc e₁ n
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha)))))
          he₁)
        (queryRead_of_matches hd hsc e₂ (encodeQueryExpr e₁ n).2.2
          (fun a ha => hm a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ha)))))
          he₂)
  | .values _ _ _, _, hnv, _, _ => absurd hnv id

/-- **A matched encoded query is a `PatternRead` of the source query it came from.** The
target-side hypothesis of the correspondence, established from the encoder.

`Query.VarsKeyed` is needed here and not only downstream: a source pattern that is a bare
variable emits no atom, so nothing in *its* block binds it, and `PatternRead.expr` has no
`QueryRead.var` to offer unless some other pattern reads it at a key column.

`Pattern.Grounded` is **not** needed. A bare *literal* pattern emits no atom either, but
`QueryRead.lit` reads a literal back with no premise at all, so the reading exists whether or
not the target holds the term — which is exactly why `encodeQuery_drops_literal_pattern`
refutes the correspondence downstream rather than this. -/
theorem patternReads_of_encodeQuery {tgt : Database} (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hnv : ∀ p ∈ q, p.NoValues) (hk : Query.VarsKeyed q)
    (h : ValidQuerySubst tgt (encodeQuery q n).1 σ) :
    ∀ p ∈ q, PatternRead tgt (tgt.env ++ σ) p := by
  have hblock : ∀ p ∈ q, ∃ m, ∀ a ∈ (encodePattern p m).1, Matches tgt a σ := by
    intro p hp
    obtain ⟨m, hsub⟩ := encodePattern_subset_encodeQuery hp n
    exact ⟨m, fun a ha => h.matches_of_mem (hsub ha)⟩
  have hbound : ∀ v ∈ Query.vars q, (Env.lookup v (tgt.env ++ σ)).isSome := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    obtain ⟨m, hm⟩ := hblock p hp
    exact lookup_isSome_of_patternArgVar p m (hnv p hp) hm ha
  intro p hp
  obtain ⟨m, hm⟩ := hblock p hp
  exact patternRead_of_matches hd hsc p m (hnv p hp)
    (fun v hv => hbound v (Query.mem_vars.mpr ⟨p, hp, hv⟩)) hm

/-- **The correspondence in the form a rule head consumes.** The state-level theorem composed
with the encoder read-back above: `exists_validQuerySubst_of_patternReads` is the mathematics
and `patternReads_of_encodeQuery` establishes its premise from a matched encoded query. -/
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

/-- **And the domain supplies the two source-text conditions.** `EncodeDomain.noLeafPattern`
is stated per command; this is it at a rule, which is the form the correspondence consumes —
so a program `encode` claims never needs `hgr` and `hk` assumed separately. -/
theorem Program.EncodeDomain.noLeafPattern_of_mem {P : Program} (h : P.EncodeDomain) {r : Rule}
    (hr : Cmd.rule r ∈ P) : (∀ p ∈ r.query, p.Grounded) ∧ Query.VarsKeyed r.query :=
  h.noLeafPattern _ hr

/-! ### The refutation: `encodeQuery` drops a leaf pattern

`encodeQueryExpr` flattens an *application* and returns a leaf unchanged, emitting no atom
for it, so `encodePattern` maps a source pattern whose expression is a bare literal to the
**empty** list of atoms. A dropped constraint is a rule the target fires and the source does
not, and the correspondence is false without `Pattern.Grounded`.

The same defect at a bare *variable* is `Query.VarsKeyed`: `.expr (.var v)` gets no atom
either, so nothing in the encoded query binds `v` and the head reads it unbound — which the
source rule, whose `ValidEnv` must bind it to a term the source holds, does not do.

Both are conditions on the source program's **text** and decidable, and both are now clauses
of `Program.EncodeDomain`: `litProgram` below *was* in the domain, which is what made the
refutation a program the encoder claimed and got wrong, and
`litProgram_not_encodeDomain` is that closed. The refutation stays as the reason the clause is
there. -/

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

/-- **And it is *outside* the encoder's declared domain**, which is the repair: every other
clause of `Program.EncodeDomain` holds of it — one constructor-free rule, no `set`, no
generated name anywhere — and `EncodeDomain.noLeafPattern` is the one it fails. Before that
clause was folded in, this program was in the domain and the refutation below was a program
the encoder claimed and got wrong. -/
theorem litProgram_not_encodeDomain : ¬ litProgram.EncodeDomain := by
  intro h
  have hq := h.noLeafPattern (.rule { query := litQuery, actions := [], ruleset := "" })
    (by simp [litProgram])
  exact hq.1 (.expr (.lit (.int 1))) (by simp [litQuery]) (.int 1) rfl

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

The two *composed* — a source application one of whose arguments is a variable — needs a
program declaring a constructor of **positive arity**, which no program
`Encoding/Correspond.lean` steps does. `wProgram` below is that program, and
`exists_validQuerySubst_composed_witness` is the composition run at the pair it reaches. -/
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

/-! ### The composed witness: an application whose argument is a variable

Everything above is exercised at `satProgram`, whose one constructor is **nullary** — so
`congUp_of_queryRead`'s application case runs at an empty argument list and its variable case
runs only in isolation (`congUp_var_witness`). Composing the two is the case the
correspondence was written for and the one nothing reached: a source pattern `(F x)`, whose
encoding is the single view read `(= (@v0 @v1) (@FView x))` — the query variable at a *key
column*.

`wProgram` is that program — one nullary constructor, one **unary** one, a build of `(F (A))`,
and a rule whose query is `((F x))` — stepped on both sides and run end to end at the pair.
`Query.VarsKeyed` is non-vacuous there for the first time: `x` is a query variable, it sits at
a key column, and `exists_sourceReading` reads it back through `Database.ViewsSound` at the
entry the build wrote. -/

/-- `(constructor A () S)`. -/
def wADecl : FnDecl := { arity := 0, outArity := 1, merge := none }

/-- `(constructor F (S) S)`, the positive-arity declaration `satProgram` has none of. -/
def wFDecl : FnDecl := { arity := 1, outArity := 1, merge := none }

/-- `(rule ((F x)) ())`: one pattern, an application whose argument is a variable. -/
def wSrcRule : Rule :=
  { query := [.expr (.app "F" [.var "x"])], actions := [], ruleset := "" }

/-- Two constructors, the rule, and the build of `(F (A))`. The rule precedes the action so
that the encoding's one `Cmd.saturate` is its last command. -/
def wProgram : Program :=
  [.decl "A" wADecl, .decl "F" wFDecl, .rule wSrcRule,
   .action (.expr (.app "F" [.app "A" []]))]

/-! #### The source side -/

/-- The signature the two declarations install. -/
def wSrcSig : Signature :=
  Function.update (Function.update Database.empty.sig "A" (some wADecl)) "F" (some wFDecl)

/-- After the two declarations and the rule: no term yet. -/
def wSrcBase : Database :=
  { Database.empty with
    sig := wSrcSig,
    rules := insert wSrcRule Database.empty.rules }

/-- **The source state `wProgram` runs to**: the rule registered, and `(F (A))` built. -/
def wSrcD : Database := wSrcBase.addTerm (.app "F" [.app "A" []])

private theorem wSrcBase_terms : wSrcBase.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [wSrcBase, Database.empty] at hu

theorem wSrcD_terms : wSrcD.terms = (Term.app "F" [.app "A" []]).subterms := by
  rw [wSrcD, Database.addTerm_terms, wSrcBase_terms, Set.empty_union]

/-- **And it is reachable**: two declarations, the rule, and the build. -/
theorem wProgramStep_src : ProgramStep Database.empty wProgram wSrcD := by
  refine .cons ⟨_, rfl, .refl⟩ (.cons ⟨_, rfl, .refl⟩
    (.cons ⟨_, rfl, .refl⟩ (.cons ⟨wSrcD, ?_, .refl⟩ .nil)))
  change cmdEffect _ (.action (.expr (.app "F" [.app "A" []]))) = some wSrcD
  simp only [cmdEffect, evalAction, Expr.eval, Expr.evalList, wSrcD]
  rfl

private theorem wSrcBase_wf : wSrcBase.WF where
  eqsRefl := fun t ht => absurd (wSrcBase_terms ▸ ht) (by simp)
  subtermClosed := fun t ht => absurd (wSrcBase_terms ▸ ht) (by simp)
  envInTerms := by simp [wSrcBase, Database.empty]
  litsIsolated := by simp [Database.LitsIsolated, wSrcBase, Database.empty]

theorem wSrcD_wf : wSrcD.WF := wSrcBase_wf.addTerm _

theorem wSrcD_mem_F : Term.app "F" [.app "A" []] ∈ wSrcD.terms := by
  rw [wSrcD_terms]; exact Term.self_mem_subterms _

theorem wSrcD_mem_A : Term.app "A" [] ∈ wSrcD.terms := by
  rw [wSrcD_terms]
  exact Term.arg_subterms (List.mem_singleton_self _) (Term.self_mem_subterms _)

/-- **`Database.TermsBuild` holds**, at both arities: the two applications the state holds are
the declared `F` and the declared `A`, neither shadowing a primitive. -/
theorem wSrcD_termsBuild : wSrcD.TermsBuild := by
  intro f as hm
  rw [wSrcD_terms] at hm
  have h : (f = "F" ∧ as = [Term.app "A" []]) ∨ (f = "A" ∧ as = []) := by
    simpa [Term.subterms_app, or_comm] using hm
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, wFDecl, by simp [wSrcD, wSrcBase, wSrcSig], rfl⟩
  · exact ⟨rfl, wADecl, by simp [wSrcD, wSrcBase, wSrcSig], rfl⟩

/-! #### The target side

`satProgram_programStep`'s shape at twenty-two commands instead of twelve: `congrArities` is
non-empty now, so the prelude declares `@Congr_1`; the rule contributes `@Rule_0`; and
`rebuildRules "F" 1` emits a **column** rule beside the e-class one. The one `Cmd.saturate`
is still discharged rather than assumed, and for the same two reasons — nothing wrote a `@UF`
entry, and each view holds a single row. -/

/-- The signature `encode wProgram`'s prelude installs, in declaration order. -/
def wSig : Signature :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        Database.empty.sig
        fiatName (some (proofDecl 0))) symName (some (proofDecl 1)))
        transName (some (proofDecl 2))) (congrName 1) (some (proofDecl 1)))
        (ruleName 0) (some (proofDecl 1))) ufName (some ufDecl))
        "F" (some (skolemDecl 1))) (viewName "F") (some (viewDecl 1)))
        (termName "F") (some (termDecl 1))) "A" (some (skolemDecl 0)))
        (viewName "A") (some (viewDecl 0))) (termName "A") (some (termDecl 0))

set_option maxHeartbeats 2000000 in
-- `split_ifs` on a twelve-deep `Function.update` chain is thirteen goals, and each one
-- decides a `FnDecl` equality through `viewName`/`termName`; the default budget is short.
/-- **The three `:merge` functions with a body are `@UF` and the two views.** The two term
relations are `:no-merge` and everything else is a constructor. -/
private theorem wSig_merge {f : FnName} {decl : FnDecl} {body : List Action} {res : List Expr}
    (hsig : wSig f = some decl) (hm : decl.merge = some (.merge body res)) :
    (f = ufName ∧ decl = ufDecl) ∨ (f = viewName "F" ∧ decl = viewDecl 1) ∨
      (f = viewName "A" ∧ decl = viewDecl 0) := by
  simp only [wSig, Function.update_apply, Database.empty] at hsig
  split_ifs at hsig <;>
    obtain rfl := Option.some.inj hsig
    <;> first
      | exact Or.inl ⟨by assumption, rfl⟩
      | exact Or.inr (Or.inl ⟨by assumption, rfl⟩)
      | exact Or.inr (Or.inr ⟨by assumption, rfl⟩)
      | simp [proofDecl, skolemDecl, termDecl] at hm

/-- `F`'s e-class rebuild rule: `@FView(@c0) ↦ (@e, @p)` follows `@e`'s union-find edge. -/
def wRebuildFEclass : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName "F") [.var "@c0"],
              .values [.var "@x", .var "@q"] ufName [.var "@e"]],
    actions := [.set (viewName "F") [.var "@c0"] [.var "@x", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

/-- `F`'s **column** rebuild rule, the one a nullary constructor has no counterpart for: the
key's single column follows its edge, and the entry keeps its e-class. -/
def wRebuildFCol : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName "F") [.var "@c0"],
              .values [.var "@x", .var "@q"] ufName [.var "@c0"]],
    actions := [.set (viewName "F") [.var "@x"]
      [.var "@e", transE (symE (congrE [.var "@q"])) (.var "@p")]],
    ruleset := rebuildRuleset }

/-- The source rule's encoding: one view read, keyed on the query variable. -/
def wEncRule : Rule :=
  { query := [.values [.var "@v0", .var "@v1"] (viewName "F") [.var "x"]],
    actions := [], ruleset := "" }

/-- After the prelude and the encoded rule: twelve declarations and five rules. `A`'s rebuild
rule is `satRebuildRule`, unchanged. -/
def wPrelude : Database :=
  { Database.empty with
    sig := wSig,
    rules := insert wEncRule (insert satRebuildRule (insert wRebuildFCol
      (insert wRebuildFEclass (insert pathCompressRule Database.empty.rules)))) }

/-- `@ATerm(A)`. -/
def wATermE : Term := .app (termName "A") [.app "A" []]

/-- `@AView() ↦ (A, @Fiat)`. -/
def wAViewE : Term := .app (viewName "A") [.app "A" [], .app fiatName []]

/-- `@FTerm(A, F(A))`: a term-relation row **two** columns wide, which is what makes
`viewName_ne_termName` necessary. -/
def wFTermE : Term := .app (termName "F") [.app "A" [], .app "F" [.app "A" []]]

/-- `@FView(A) ↦ (F(A), @Fiat)`, the entry the correspondence reads. -/
def wFViewE : Term :=
  .app (viewName "F") [.app "A" [], .app "F" [.app "A" []], .app fiatName []]

/-- **The state `encode wProgram` runs to.** -/
def wTarget : Database :=
  (((wPrelude.addTerm wATermE).addTerm wAViewE).addTerm wFTermE).addTerm wFViewE

theorem wTarget_sig : wTarget.sig = wSig := rfl

theorem wTarget_rules : wTarget.rules = wPrelude.rules := rfl

theorem wPrelude_terms : wPrelude.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [wPrelude, Database.empty] at hu

theorem wTarget_terms : wTarget.terms =
    wATermE.subterms ∪ wAViewE.subterms ∪ wFTermE.subterms ∪ wFViewE.subterms := by
  simp [wTarget, wPrelude_terms, Set.union_assoc]

/-- The seven terms the run holds, enumerated. -/
private theorem wTarget_mem_cases {t : Term} (h : t ∈ wTarget.terms) :
    t = wFViewE ∨ t = wFTermE ∨ t = Term.app "F" [.app "A" []] ∨ t = wAViewE ∨
      t = Term.app fiatName [] ∨ t = wATermE ∨ t = Term.app "A" [] := by
  rw [wTarget_terms] at h
  simpa [wATermE, wAViewE, wFTermE, wFViewE] using h

/-- Only `Database.addTerm` writes, so the state is diagonal. -/
theorem wTarget_diag : wTarget.Diag := by
  have h : wPrelude.Diag := fun p hp => absurd hp (by simp [wPrelude, Database.empty])
  exact (((h.addTerm _).addTerm _).addTerm _).addTerm _

/-- **No `@UF` entry.** `wProgram` has no `union`, so nothing writes one. -/
theorem wTarget_no_uf (ts : List Term) : Term.app ufName ts ∉ wTarget.terms := by
  intro h
  rcases wTarget_mem_cases h with h' | h' | h' | h' | h' | h' | h' <;>
    simp [wATermE, wAViewE, wFTermE, wFViewE, ufName, viewName, termName, fiatName] at h'

/-- The `@FView` entry is there, so the correspondence has something to read at a key
column. -/
theorem wTarget_mem_view : wFViewE ∈ wTarget.terms := Database.mem_addTerm _ _

/-- The one `@AView` row pins its value tuple. -/
private theorem wTarget_pin_A {vals : List Term}
    (hmem : Term.app (viewName "A") ([] ++ vals) ∈ wTarget.terms) :
    vals = [.app "A" [], .app fiatName []] := by
  rcases wTarget_mem_cases hmem with h' | h' | h' | h' | h' | h' | h' <;>
    simp_all [wATermE, wAViewE, wFTermE, wFViewE, viewName, termName, fiatName]

/-- And the one `@FView` row pins both its key and its value tuple. -/
private theorem wTarget_pin_F {as vals : List Term} (hlen : as.length = 1)
    (hmem : Term.app (viewName "F") (as ++ vals) ∈ wTarget.terms) :
    as = [.app "A" []] ∧ vals = [.app "F" [.app "A" []], .app fiatName []] := by
  obtain ⟨a, rfl⟩ : ∃ a, as = [a] := by
    match as, hlen with
    | [a], _ => exact ⟨a, rfl⟩
  rcases wTarget_mem_cases hmem with h' | h' | h' | h' | h' | h' | h' <;>
    simp_all [wATermE, wAViewE, wFTermE, wFViewE, viewName, termName, fiatName]

/-- **The state is merge-saturated.** `@UF` has no entry, and each view has exactly one — so
its only collision is with itself, and `identityVals := some 1` makes that no conflict. -/
theorem wTarget_mergeSaturated : MergeSaturated wTarget := by
  intro db' h
  cases h with
  | @collide _ f decl as bs a b vs body res hsig hm hconf hla hlb hma hmb _ _ _ =>
    rcases wSig_merge (wTarget_sig ▸ hsig) hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hma (wTarget_no_uf _)
    · obtain ⟨rfl, rfl⟩ : body = mergeBody ∧ res = mergeResult := by
        simpa [viewDecl] using hm.symm
      have hab : a = b :=
        (wTarget_pin_F (by simpa [viewDecl] using hla) hma).2.trans
          (wTarget_pin_F (by simpa [viewDecl] using hlb) hmb).2.symm
      rw [hab] at hconf
      exact (not_mergeConflict_self mergeBody_ne_nil b hconf).elim
    · obtain ⟨rfl, rfl⟩ : body = mergeBody ∧ res = mergeResult := by
        simpa [viewDecl] using hm.symm
      obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (by simpa [viewDecl] using hla)
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by simpa [viewDecl] using hlb)
      have hab : a = b := (wTarget_pin_A hma).trans (wTarget_pin_A hmb).symm
      rw [hab] at hconf
      exact (not_mergeConflict_self mergeBody_ne_nil b hconf).elim

/-- No `@UF` read matches: a `Pattern.values` match needs the entry term itself, and on a
diagonal state `withOperands` cannot supply one. -/
theorem wTarget_not_matches_uf {vs as : List Expr} {σ : Env} :
    ¬ Matches wTarget (.values vs ufName as) σ := by
  intro h
  cases h with
  | values hw _ _ hcong =>
    exact absurd (congOn_eq_of_diag wTarget_diag hcong ▸ hw) (wTarget_no_uf _)

private theorem wTarget_not_forall₂ : ∀ {q : Query} {σs : List Env},
    List.Forall₂ (ValidSubst wTarget) q σs →
    ∀ {vs as : List Expr}, Pattern.values vs ufName as ∈ q → False
  | _, _, .nil, _, _, h => absurd h (by simp)
  | _ :: _, _, .cons hp hrest, _, _, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact wTarget_not_matches_uf hp.2
    · exact wTarget_not_forall₂ hrest h'

/-- **The rebuild ruleset has reached its fixpoint.** Every maintenance rule reads `@UF` and
there is no `@UF` entry; the encoded source rule is in another ruleset. -/
theorem wTarget_runRules : RunRules rebuildRuleset wTarget = wTarget := by
  have hS : {d | ∃ r ∈ wTarget.rules, r.ruleset = rebuildRuleset ∧
      d ∈ RuleResults wTarget r} = (∅ : Set Database) := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro d ⟨r, hr, hR, σ, ⟨σs, hall, -⟩, -⟩
    rw [wTarget_rules] at hr
    have hr' : r = wEncRule ∨ r = satRebuildRule ∨ r = wRebuildFCol ∨
        r = wRebuildFEclass ∨ r = pathCompressRule := by
      simpa [wPrelude, Database.empty] using hr
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact absurd hR (by simp [wEncRule, rebuildRuleset])
    · exact wTarget_not_forall₂ hall (vs := [.var "@x", .var "@q"]) (as := [.var "@e"])
        (by simp [satRebuildRule])
    · exact wTarget_not_forall₂ hall (vs := [.var "@x", .var "@q"]) (as := [.var "@c0"])
        (by simp [wRebuildFCol])
    · exact wTarget_not_forall₂ hall (vs := [.var "@x", .var "@q"]) (as := [.var "@e"])
        (by simp [wRebuildFEclass])
    · exact wTarget_not_forall₂ hall (vs := [.var "@b", .var "@p"]) (as := [.var "@a"])
        (by simp [pathCompressRule])
  unfold RunRules
  rw [hS]
  exact Database.ext rfl (by simp) rfl rfl

/-- **The trailing `Cmd.saturate rebuildRuleset` steps from this state to itself.** -/
theorem wTarget_cmdStep_saturate :
    CmdStep wTarget (.saturate rebuildRuleset) wTarget :=
  ⟨wTarget, ⟨.refl, wTarget_runRules, wTarget_mergeSaturated⟩, .refl⟩

/-- **The prelude `encode wProgram` emits**: twelve declarations — the three fixed proof
heads, `@Congr_1`, `@Rule_0`, `@UF` and the two table triples — and then five rules. -/
def wEncodedPrelude : Program :=
  [.decl fiatName (proofDecl 0), .decl symName (proofDecl 1), .decl transName (proofDecl 2),
   .decl (congrName 1) (proofDecl 1), .decl (ruleName 0) (proofDecl 1),
   .decl ufName ufDecl,
   .decl "F" (skolemDecl 1), .decl (viewName "F") (viewDecl 1),
   .decl (termName "F") (termDecl 1),
   .decl "A" (skolemDecl 0), .decl (viewName "A") (viewDecl 0),
   .decl (termName "A") (termDecl 0),
   .rule pathCompressRule, .rule wRebuildFEclass, .rule wRebuildFCol, .rule satRebuildRule,
   .rule wEncRule]

/-- **And what the one source action becomes**: four `set`s and the rebuild. -/
def wEncodedActions : Program :=
  [.action (.set (termName "A") [.app "A" []] []),
   .action (.set (viewName "A") [] [.app "A" [], fiatE]),
   .action (.set (termName "F") [.app "A" [], .app "F" [.app "A" []]] []),
   .action (.set (viewName "F") [.app "A" []] [.app "F" [.app "A" []], fiatE]),
   .saturate rebuildRuleset]

/-- The twenty-two commands, as `satEncoded` is. -/
def wEncoded : Program := wEncodedPrelude ++ wEncodedActions

theorem wEncoded_eq : encode wProgram = wEncoded := rfl

/-- The three states the four `set`s pass through. **Named, and that is not cosmetic**: a
`set` reduces `Expr.eval`, which decides `Signature.IsCtor` through the whole twelve-deep
declaration chain, and asking the kernel to do that at a state written as seventeen nested
structure updates costs minutes where doing it at a constant costs milliseconds. -/
private def wS1 : Database := wPrelude.addTerm wATermE

@[inherit_doc wS1] private def wS2 : Database := wS1.addTerm wAViewE

@[inherit_doc wS1] private def wS3 : Database := wS2.addTerm wFTermE

/-- The seventeen declaration and rule commands, stepped: each a `cmdEffect` and a reflexive
merge phase. -/
theorem wPreludeStep : ProgramStep Database.empty wEncodedPrelude wPrelude := by
  iterate 16 refine .cons ⟨_, rfl, .refl⟩ ?_
  exact .cons ⟨wPrelude, rfl, .refl⟩ .nil

/-- The four `set`s and the rebuild. -/
theorem wActionsStep : ProgramStep wPrelude wEncodedActions wTarget :=
  .cons ⟨wS1, rfl, .refl⟩ (.cons ⟨wS2, rfl, .refl⟩ (.cons ⟨wS3, rfl, .refl⟩
    (.cons ⟨wTarget, rfl, .refl⟩ (.cons wTarget_cmdStep_saturate .nil))))

/-- **And the encoded run is reachable**, the target's half of the pair. -/
theorem wProgram_programStep :
    ProgramStep Database.empty (encode wProgram) wTarget := by
  rw [wEncoded_eq, wEncoded]
  exact wPreludeStep.append wActionsStep

/-! #### The correspondence, run at the pair -/

/-- Only `Database.addTerm` writes on the source side either. -/
theorem wSrcD_diag : wSrcD.Diag := by
  have h : wSrcBase.Diag := fun p hp => absurd hp (by simp [wSrcBase, Database.empty])
  exact h.addTerm _

/-- **`Database.ViewsSound` holds at `wTarget`**, and at *two* view entries rather than one.
Three of the seven terms are too short to be a view entry — a key plus the two value columns
is two columns at least — and the two term-relation rows go by **name**: `@ATerm`'s row is one
column and a length would have done, but `@FTerm`'s is two, exactly as wide as a nullary view
entry, so at a constructor of positive arity `viewName_ne_termName` is the only thing that
excludes it. What is left is `@AView() ↦ (A, @Fiat)` and `@FView(A) ↦ (F(A), @Fiat)`, and both
are `entrySound_build` at a term the source holds. -/
theorem wTarget_viewsSound : wTarget.ViewsSound wSrcD := by
  intro f cs e pf ho
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : cs = bs :=
    List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag wTarget_diag h)
  rcases wTarget_mem_cases hmem with h' | h' | h' | h' | h' | h' | h' <;>
      simp only [wFViewE, wFTermE, wAViewE, wATermE, Term.app.injEq] at h' <;>
    [skip; skip; skip; skip; skip; skip; skip]
  · obtain rfl : f = "F" := viewName_inj h'.1
    obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
      have hl : (cs ++ [e, pf]).length = 3 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      match cs, hl with | [c], _ => exact ⟨c, rfl⟩
    obtain ⟨rfl, rfl, -⟩ : c = Term.app "A" [] ∧ e = Term.app "F" [.app "A" []] ∧
        pf = Term.app fiatName [] := by simpa using h'.2
    exact entrySound_build wSrcD_wf wSrcD_mem_F
  · exact absurd h'.1 viewName_ne_termName
  · have hl : (cs ++ [e, pf]).length = 1 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · obtain rfl : f = "A" := viewName_inj h'.1
    obtain rfl : cs = [] := by
      have hl : (cs ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨rfl, -⟩ : e = Term.app "A" [] ∧ pf = Term.app fiatName [] := by simpa using h'.2
    exact entrySound_build wSrcD_wf wSrcD_mem_A
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · exact absurd h'.1 viewName_ne_termName
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega

/-- The target's subterm closure, which is what turns a matched view read into a
`Database.Out`. -/
theorem wTarget_subtermClosed : ∀ t ∈ wTarget.terms, t.subterms ⊆ wTarget.terms := by
  intro t ht
  rw [wTarget_terms] at ht ⊢
  rcases ht with ((h | h) | h) | h <;> intro s hs <;>
    first
      | exact Or.inl (Or.inl (Or.inl (Term.subterms_subset_of_mem h hs)))
      | exact Or.inl (Or.inl (Or.inr (Term.subterms_subset_of_mem h hs)))
      | exact Or.inl (Or.inr (Term.subterms_subset_of_mem h hs))
      | exact Or.inr (Term.subterms_subset_of_mem h hs)

/-- **The view read matches, with a variable in its key column.** `wEncRule`'s own atom, at
the entry the build wrote: the key is `x`, and the substitution binds it to `(A)`. -/
theorem wTarget_matches_view :
    Matches wTarget (.values [.var "@e", .var "@p"] (viewName "F") [.var "x"])
      [("x", .app "A" []), ("@e", .app "F" [.app "A" []]), ("@p", .app fiatName [])] :=
  .values wTarget_mem_view rfl rfl (Database.mem_addTerm _ _)

/-- **And `out_of_matches_values` reads it back as a lookup.** -/
theorem wTarget_out_view :
    wTarget.Out (viewName "F") [.app "A" []]
      [.app "F" [.app "A" []], .app fiatName []] := by
  obtain ⟨ts, us, hts, hus, -, ho⟩ :=
    out_of_matches_values wTarget_diag wTarget_subtermClosed wTarget_matches_view
  obtain rfl : ts = [Term.app "A" []] := Option.some.inj hts.symm
  obtain rfl : us = [Term.app "F" [.app "A" []], Term.app fiatName []] :=
    Option.some.inj hus.symm
  exact ho

/-- **The premise of the correspondence at the composed case**: the target's reading of `(F
x)`, which drives `congUp_of_queryRead` through its application case *and* its variable case,
at one reading. -/
theorem wTarget_patternRead :
    PatternRead wTarget [("x", .app "A" [])] (.expr (.app "F" [.var "x"])) :=
  .expr (.app (.cons (.var (by simp)) .nil) wTarget_out_view)

/-- The query binds one variable, so `Query.VarsKeyed` has something to say about it. -/
theorem wSrcRule_query_vars : Query.vars wSrcRule.query = ["x"] := rfl

/-- **`Query.VarsKeyed` holds non-vacuously**: the query has a variable, and it sits at the
key column of the read `encodeQueryExpr` emits for `(F x)`. -/
theorem wSrcRule_varsKeyed : Query.VarsKeyed wSrcRule.query := by
  intro v hv
  obtain rfl : v = "x" := by
    rw [wSrcRule_query_vars, List.mem_singleton] at hv; exact hv
  exact ⟨.expr (.app "F" [.var "x"]), by simp [wSrcRule],
    by simp [Pattern.ArgVar, Expr.ArgVar]⟩

/-- And its one pattern is not a bare leaf. -/
theorem wSrcRule_grounded : ∀ p ∈ wSrcRule.query, p.Grounded := by
  intro p hp
  obtain rfl : p = .expr (.app "F" [.var "x"]) := by simpa [wSrcRule] using hp
  intro l
  simp

/-! #### The encoder read-back, run at the witness

`patternReads_of_encodeQuery`'s hypothesis is a match of the *encoded* query, so it is checked
inhabited here rather than assumed: `wEncRule`'s query **is** what `encodeQuery` emits for the
source query, and the substitution below is the one the run's single `@FView` row admits. -/

/-- The rule the prelude installed is the encoding of the source rule's query, at the counter
`encodeRule` starts it from. -/
theorem wEncRule_query_eq : (encodeQuery wSrcRule.query 0).1 = wEncRule.query := rfl

/-- What the encoded query matched under: the source key variable, and the read's two
generated columns — the e-class and the premise proof. -/
def wSubst : Env :=
  [("@v0", .app "F" [.app "A" []]), ("@v1", .app fiatName []), ("x", .app "A" [])]

private theorem wTarget_mem_of_sub {t : Term} (h : t ∈ wFViewE.subterms) :
    t ∈ wTarget.terms := wTarget_subtermClosed _ wTarget_mem_view h

/-- The one emitted atom matches, at the one entry the build wrote. -/
theorem wTarget_validSubst :
    ValidSubst wTarget (.values [.var "@v0", .var "@v1"] (viewName "F") [.var "x"]) wSubst := by
  refine ⟨⟨List.Perm.refl _, ?_⟩, .values wTarget_mem_view rfl rfl (Database.mem_addTerm _ _)⟩
  intro b hb
  simp only [wSubst, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;>
    exact wTarget_mem_of_sub (Term.arg_subterms (by simp) (Term.self_mem_subterms _))

/-- **And so the encoded query matches** — the hypothesis `patternReads_of_encodeQuery`
consumes, inhabited at a state the encoded program reaches. -/
theorem wTarget_validQuerySubst :
    ValidQuerySubst wTarget (encodeQuery wSrcRule.query 0).1 wSubst :=
  ⟨[wSubst], .cons wTarget_validSubst .nil, .single _⟩

/-- Its one pattern is a source `.expr`, so nothing in the query is an entry atom. -/
theorem wSrcRule_noValues : ∀ p ∈ wSrcRule.query, p.NoValues := by
  intro p hp
  obtain rfl : p = .expr (.app "F" [.var "x"]) := by simpa [wSrcRule] using hp
  trivial

/-- **The read-back, run at the witness**: the emitted view read, folded back into the target's
reading of the *source* expression `(F x)`. Definitionally `wTarget_patternRead` extended by
the two generated columns the encoded query also binds. -/
theorem wTarget_patternRead_encoded :
    PatternRead wTarget (wTarget.env ++ wSubst) (.expr (.app "F" [.var "x"])) :=
  patternReads_of_encodeQuery wTarget_diag wTarget_subtermClosed wSrcRule_noValues
    wSrcRule_varsKeyed wTarget_validQuerySubst _ (by simp [wSrcRule])

/-- **And the witness program is inside the encoder's declared domain**, the narrowed one:
the clause that puts `litProgram` out keeps this in, so the composed case is a case `encode`
claims rather than one it is excused from. -/
theorem wProgram_encodeDomain : wProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc f d heq
    subst heq
    simp only [wProgram, List.mem_cons] at hc
    rcases hc with h | h | h | h | h <;> simp_all [wADecl, wFDecl]
  noSet := by
    intro c hc
    simp only [wProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.NoSet, Action.NoSet, Pattern.NoValues, wSrcRule]
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  noAtVar := by decide +kernel
  noAtRuleset := by decide +kernel
  noLeafPattern := by
    intro c hc
    simp only [wProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · exact ⟨wSrcRule_grounded, wSrcRule_varsKeyed⟩
    · trivial
    · exact absurd h (by simp)

/-- **The correspondence, run end to end at the composed case.**

The first three conjuncts are that the pair is reachable and in the encoder's domain, and
every hypothesis of the correspondence holds there: `Database.WF` and `Database.TermsBuild`
on the source, `Database.ViewsSound` on the target, `Pattern.Grounded` and — for the first
time non-vacuously — `Query.VarsKeyed` on the source text. Both premises are inhabited: the
target's reading (`wTarget_patternRead`) and, upstream of it, a match of the **encoded** query
itself (`wTarget_validQuerySubst`), so the composition runs from the encoder's own output
rather than from a hand-written reading. The conclusion is the last conjunct: the source query
`((F x))` matches, at a substitution binding `x` to the source term `(A)` — the very term the
id the target read it as stands for. That is what a rule head building over `x` needs, and it
is the composition `congUp_var_witness` and `satTarget_patternRead` could only check apart.

`Database.GlobalsRead` is the one clause vacuous here — `wProgram` has no `let` — and is
discharged non-vacuously at `globalsRead_nonvacuous`. -/
theorem exists_validQuerySubst_composed_witness :
    wProgram.EncodeDomain ∧ ProgramStep Database.empty wProgram wSrcD ∧
      ProgramStep Database.empty (encode wProgram) wTarget ∧
      wSrcD.WF ∧ wSrcD.TermsBuild ∧ wTarget.ViewsSound wSrcD ∧
      Query.vars wSrcRule.query = ["x"] ∧ Query.VarsKeyed wSrcRule.query ∧
      PatternRead wTarget [("x", .app "A" [])] (.expr (.app "F" [.var "x"])) ∧
      ValidQuerySubst wTarget (encodeQuery wSrcRule.query 0).1 wSubst ∧
      ∃ τ, ValidQuerySubst wSrcD wSrcRule.query τ ∧
        Env.lookup "x" (wSrcD.env ++ τ) = some (.app "A" []) := by
  refine ⟨wProgram_encodeDomain, wProgramStep_src, wProgram_programStep, wSrcD_wf,
    wSrcD_termsBuild, wTarget_viewsSound, wSrcRule_query_vars, wSrcRule_varsKeyed,
    wTarget_patternRead, wTarget_validQuerySubst, ?_⟩
  obtain ⟨τ, hv, hτ⟩ := exists_validQuerySubst_of_encodeQuery wSrcD_wf wSrcD_termsBuild
    wTarget_viewsSound wTarget_diag wTarget_subtermClosed
    (by simp [Database.GlobalsRead, wSrcD, wSrcBase, Database.empty])
    wSrcRule_noValues wSrcRule_grounded wSrcRule_varsKeyed wTarget_validQuerySubst
  obtain ⟨t, hlk, hc⟩ := hτ "x" (by rw [wSrcRule_query_vars]; simp) (.app "A" []) rfl
  obtain rfl : t = Term.app "A" [] := Cong.eq_of_diag wSrcD_diag hc
  exact ⟨τ, hv, hlk⟩

end Egglog
