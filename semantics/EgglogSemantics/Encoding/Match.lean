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

## The head build, and why it is not obstructed

`encodeBuild` mints the skolem over its arguments' **ids**, so the entry a head writes is keyed
and valued at ids. `mem_terms_of_entrySound_skolem` is what that costs, compiled:
`Database.ViewsSound` at a freshly built entry is *equivalent* to the minted id being a source
term. Read off the key that is the fact `encode_corresponds_invents_enode` refutes, and the
head-build case looks obstructed.

It is not, because **which source terms the correspondence delivers is a choice**. A variable at
a key column is read back by `Database.ViewsSound` as a source term *congruent* to the id, and
both endpoints of a congruence are present — so the id is itself a term the source holds, and
the reading may be taken to be the ids. `exists_validQuerySubst_at_ids` is that reading;
`Matches` is congruence-closed, so nothing about the source match is lost. Then the source's own
head evaluation is the same expression at the same values — `encodeBuild_fst` says the naming
expression *is* the source expression, `Expr.eval_transport` says the two signatures and
environments agree where a head reads — so it builds the very term the target's skolem names.
`entrySound_headBuild` and `cong_headUnion` are the two head writers, and what they owe is only
`hfired`: the source rule fired, and holds what its own head built. That is `RunRules`' fixpoint
and belongs to `execM_viewsSound`.

What the head's path costs is `Database.GlobalsAgree` where the plain correspondence asks only
`Database.GlobalsRead`: a source global and the target's reading of it must be the *same* term,
not merely congruent ones, which is what the encoding gives (`encodeBuild_fst` again, at a
top-level `let`).

## Globals in the query, and why nothing here sees one

A rule *head* reads a global off the environment on both sides, which is what the two clauses
above are for. A rule **query** does not: `Encoding/Encode.lean`'s `Rule.substGlobals` replaces
a global by its (closed) definition before `encodeQuery` ever sees the rule, so what is
flattened has no global in it and everything below is about an ordinary query. What the
substitution costs on the source side is `ValidQuerySubst.of_substGlobals` — a source match of
the substituted query is one of the query — under `Database.GlobalsInline`, the clause saying
the environment realizes the definitions the encoder carries. `Pattern.Grounded`,
`Pattern.NoValues` and `Query.VarsKeyed` all survive the substitution
(`Query.grounded_substGlobals`, `Query.noValues_substGlobals`, `Query.VarsKeyed.substGlobals`),
so the three text conditions this file consumes hold of the substituted query too.

## And what it is false for

`encodePattern` emits **no atom** for a source pattern whose expression is a bare literal or
a bare variable — `encodeQueryExpr` flattens an application and returns a leaf unchanged. A
dropped constraint is a rule the target fires and the source does not, and
`encodeQuery_drops_literal_pattern` is that refuted: at `satProgram`'s own source state, the
source query `[(1)]` matches under no substitution while its encoding, the empty query,
matches under the empty one. `Pattern.Grounded` is the side condition that excludes it, and
`Query.VarsKeyed` is its counterpart for the bare-*variable* half. Both are restrictions on
the *source program's text*, and both are now clauses of **`Program.EncodeDomain`**
(`EncodeDomain.queryEncodable`), so the program the refutation is about is outside the
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
`globalsRead_nonvacuous` — with `globalsAgree_nonvacuous` for the strengthening — is that clause
at a state binding a global. `entrySound_headBuild_witness` is the head-build case run at the
same pair, at the view entry that run really wrote.

`uProgram`, at the end, is the pair the head's *`union`* case needs: a rule head that unions
two distinct nullary constructors, so that `cong_headUnion` is discharged where the source
state is **not** diagonal — which `cong_headUnion_witness` cannot check and which is the whole
of what that lemma is for. Its target-side run stops one command short of `encode`'s output,
and `uTgt_saturate_infinite` is the compiled reason: `encode`'s rebuild has **no fixpoint**
after a `union` between distinct built terms, so `ProgramStep Database.empty (encode P) tgt`
— satisfiable at a program that only builds (`satProgram_programStep`) — is satisfiable at no
program that asserts an equation. `Database.UnionsJoined` and `Database.ViewLeader`, which is
what `Encoding/Complete.lean` now reduces `execM_unionsRead` to, are witnessed there too:
`uTgt_not_unionsRead` is the obligation failing before the rebuild's one firing,
`uTgt_not_viewLeader` is which of the two properties fails there, and
`uRebuilt_unionsJoined`/`uRebuilt_viewLeader` are both holding after it — the second with all
three of its clauses non-vacuous, which no other state in the tree makes them.
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

/-! ### Reading a global through its definition

`Encoding/Encode.lean`'s `Rule.substGlobals` replaces a global by the (closed) expression the
`let` bound it to, so what the encoded query flattens is that expression and not the frozen
term. Everything below is the source-side half of that: at a state whose environment agrees
with the substitution, a source pattern and its substituted form evaluate alike, match alike,
and bind alike — so a source-side match of the substituted query *is* one of the original. -/

/-! #### The substitution is invisible to the source

Three facts, all by the same induction: the substituted expression evaluates to what the
original does, mentions no variable the original does not, and keeps a bare variable bare
unless it replaced it by an application. Together they say a source-side match of
`Query.substGlobals G q` is one of `q`, which is what lets the encoder read the definition
where the source reads the name. -/

/-- A closed expression's value does not depend on the environment. -/
theorem Expr.eval_of_vars_nil {sig : Signature} {e : Expr} (h : e.vars = []) (σ : Env) :
    e.eval sig σ = e.eval sig [] :=
  Expr.eval_agreeOn e fun v hv => absurd (h ▸ hv) (by simp)

mutual

/-- **What the substitution replaced, the source's own environment binds to the same term.** -/
theorem Expr.eval_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) (σ : Env)
    (hσ : ∀ v t, Env.lookup v src.env = some t → Env.lookup v (src.env ++ σ) = some t) :
    ∀ e : Expr, (e.substGlobals G).eval src.sig (src.env ++ σ)
      = e.eval src.sig (src.env ++ σ)
  | .lit _ => rfl
  | .var v => by
      rw [Expr.substGlobals]
      cases hlk : Expr.lookupG v G with
      | none => simp only []
      | some e =>
          obtain ⟨hcl, t, hev, hbind⟩ := hG v e hlk
          cases e with
          | lit l => simp only []
          | var w => simp only []
          | app f as =>
              rw [Expr.eval_of_vars_nil hcl, hev, Expr.eval, hσ v t hbind]
  | .app f args => by
      rw [Expr.substGlobals, Expr.eval, Expr.eval,
        Expr.evalList_substGlobals hG σ hσ args]

@[inherit_doc Expr.eval_substGlobals]
theorem Expr.evalList_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) (σ : Env)
    (hσ : ∀ v t, Env.lookup v src.env = some t → Env.lookup v (src.env ++ σ) = some t) :
    ∀ es : List Expr, Expr.evalList src.sig (Expr.substGlobalsList G es) (src.env ++ σ)
      = Expr.evalList src.sig es (src.env ++ σ)
  | [] => rfl
  | e :: es => by
      rw [Expr.substGlobalsList, Expr.evalList_cons, Expr.evalList_cons,
        Expr.eval_substGlobals hG σ hσ e, Expr.evalList_substGlobals hG σ hσ es]

end

/-- A closed expression frees nothing. -/
theorem Expr.freeVars_eq_nil {e : Expr} (h : e.vars = []) (σ : Env) : e.freeVars σ = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun v hv => ?_
  exact absurd (e.mem_freeVars.mp hv).1 (by rw [h]; simp)

mutual

/-- **The substitution binds no new variable and frees none the environment holds.** A
replaced variable was bound by `src.env` and its definition is closed, so `Expr.freeVars` at
`src.env` is unmoved. -/
theorem Expr.freeVars_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) :
    ∀ e : Expr, (e.substGlobals G).freeVars src.env = e.freeVars src.env
  | .lit _ => rfl
  | .var v => by
      rw [Expr.substGlobals]
      cases hlk : Expr.lookupG v G with
      | none => simp only []
      | some e =>
          obtain ⟨hcl, t, -, hbind⟩ := hG v e hlk
          cases e with
          | lit l => simp only []
          | var w => simp only []
          | app f as =>
              simp only [Expr.freeVars_var_of_some hbind]
              exact Expr.freeVars_eq_nil hcl _
  | .app f args => by
      rw [Expr.substGlobals, Expr.freeVars_app, Expr.freeVars_app,
        Expr.freeVarsList_substGlobals hG args]

@[inherit_doc Expr.freeVars_substGlobals]
theorem Expr.freeVarsList_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) :
    ∀ es : List Expr, Expr.freeVarsList (Expr.substGlobalsList G es) src.env
      = Expr.freeVarsList es src.env
  | [] => rfl
  | e :: es => by
      rw [Expr.substGlobalsList, Expr.freeVarsList_cons, Expr.freeVarsList_cons,
        Expr.freeVars_substGlobals hG e, Expr.freeVarsList_substGlobals hG es]

end

/-- `Expr.freeVars_substGlobals` over a pattern. -/
theorem Pattern.freeVars_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) :
    ∀ p : Pattern, (p.substGlobals G).freeVars src.env = p.freeVars src.env
  | .expr e => Expr.freeVars_substGlobals hG e
  | .eq e₁ e₂ => by
      rw [Pattern.substGlobals, Pattern.freeVars, Pattern.freeVars,
        Expr.freeVars_substGlobals hG e₁, Expr.freeVars_substGlobals hG e₂]
  | .values vs f as => by
      rw [Pattern.substGlobals, Pattern.freeVars, Pattern.freeVars,
        Expr.freeVarsList_substGlobals hG vs, Expr.freeVarsList_substGlobals hG as]

/-- **A source match of the substituted pattern is one of the pattern.** The instance is the
same term (`Expr.eval_substGlobals`), so every clause of `Matches` transfers unchanged. -/
theorem Matches.of_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) {p : Pattern} {σ : Env}
    (h : Matches src (p.substGlobals G) σ) : Matches src p σ := by
  have hlk : ∀ v t, Env.lookup v src.env = some t → Env.lookup v (src.env ++ σ) = some t :=
    fun v t hv => Env.lookup_append_of_mem (Env.mem_dom_of_mem (Env.mem_of_lookup hv)) ▸ hv
  have he := Expr.eval_substGlobals hG σ hlk
  have hel := Expr.evalList_substGlobals hG σ hlk
  cases p with
  | expr e =>
      cases h with
      | expr hw hev hc => exact .expr hw (he e ▸ hev) hc
  | eq e₁ e₂ =>
      cases h with
      | eq hw h₁ h₂ hc₁ hc₂ => exact .eq hw (he e₁ ▸ h₁) (he e₂ ▸ h₂) hc₁ hc₂
  | values vs f as =>
      cases h with
      | values hw h₁ h₂ hc => exact .values hw (hel as ▸ h₁) (hel vs ▸ h₂) hc

/-- **And so a valid substitution of the substituted query is one of the query.** -/
theorem ValidQuerySubst.of_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) {q : Query} {τ : Env}
    (h : ValidQuerySubst src (Query.substGlobals G q) τ) : ValidQuerySubst src q τ := by
  obtain ⟨σs, hall, hu⟩ := h
  refine ⟨σs, ?_, hu⟩
  rw [Query.substGlobals] at hall
  clear hu
  induction q generalizing σs with
  | nil => cases hall; exact .nil
  | cons p ps ih =>
      rw [List.map_cons] at hall
      cases hall with
      | cons hp hrest =>
          exact .cons ⟨by rw [← Pattern.freeVars_substGlobals hG p]; exact hp.1,
            Matches.of_substGlobals hG hp.2⟩ (ih _ hrest)

/-- **And a source match of the pattern is one of the substituted pattern.** The direction a
*firing* needs: `encodeCmd` flattens `Rule.substGlobals G`, so the reading the target's own
match has to mirror is the **substituted** query's, and the source's `ValidQuerySubst` is at the
query it was written with. Both facts `Matches.of_substGlobals` runs on are equalities
(`Expr.eval_substGlobals`, `Pattern.freeVars_substGlobals`), so the transfer runs both ways.

`Database.GlobalsInline` is exactly what it costs, and `Encoding/Complete.lean`'s
`unionsFire_false_globals` is the residue without it: at a `G` no source state realizes the two
queries are not interchangeable at all, and the encoded rule reads a variable its own query no
longer binds. -/
theorem Matches.to_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) {p : Pattern} {σ : Env}
    (h : Matches src p σ) : Matches src (p.substGlobals G) σ := by
  have hlk : ∀ v t, Env.lookup v src.env = some t → Env.lookup v (src.env ++ σ) = some t :=
    fun v t hv => Env.lookup_append_of_mem (Env.mem_dom_of_mem (Env.mem_of_lookup hv)) ▸ hv
  have he := Expr.eval_substGlobals hG σ hlk
  have hel := Expr.evalList_substGlobals hG σ hlk
  cases p with
  | expr e =>
      cases h with
      | expr hw hev hc => exact .expr hw ((he e).trans hev) hc
  | eq e₁ e₂ =>
      cases h with
      | eq hw h₁ h₂ hc₁ hc₂ => exact .eq hw ((he e₁).trans h₁) ((he e₂).trans h₂) hc₁ hc₂
  | values vs f as =>
      cases h with
      | values hw h₁ h₂ hc => exact .values hw ((hel as).trans h₁) ((hel vs).trans h₂) hc

/-- **And so a valid substitution of the query is one of the substituted query**, which is the
premise `mem_matchQuery_encodeQuery` is handed at `Query.substGlobals G s.query`. -/
theorem ValidQuerySubst.to_substGlobals {src : Database} {G : List (Var × Expr)}
    (hG : src.GlobalsInline G) {q : Query} {τ : Env}
    (h : ValidQuerySubst src q τ) : ValidQuerySubst src (Query.substGlobals G q) τ := by
  obtain ⟨σs, hall, hu⟩ := h
  refine ⟨σs, ?_, hu⟩
  rw [Query.substGlobals]
  clear hu
  induction q generalizing σs with
  | nil => cases hall; exact .nil
  | cons p ps ih =>
      rw [List.map_cons]
      cases hall with
      | cons hp hrest =>
          exact .cons ⟨by rw [Pattern.freeVars_substGlobals hG p]; exact hp.1,
            Matches.to_substGlobals hG hp.2⟩ (ih _ hrest)

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

/-! ### What a head build owes

The correspondence as stated hands a rule head the source application over *some* source terms
the query matched. `encodeBuild` writes its entry over the **ids**: "the skolem is the answer,
nothing is read back", so building `(f x y)` at a head whose query bound `x`, `y` to the ids
`i₁`, `i₂` writes `@fView(i₁, i₂) ↦ (f i₁ i₂, @Fiat)` and `Database.addTerm` records the term
`f(i₁, i₂)`. `Database.ViewsSound` at that entry is a statement about `f(i₁, i₂)` and not about
`f(τx, τy)`, and read that way it asks for the fact `encode_corresponds_invents_enode` refutes
at a key column: that the key's own application is a source term.

**The reading is a choice, and the other choice closes it.** `exists_validQuerySubst_at_ids`
below takes the source reading to be the ids themselves, which is legitimate because a variable
at a key column is read back by `Database.ViewsSound` as something *congruent* to the id and a
congruence's endpoints are both present. Then `τx = i₁`, `τy = i₂`, the source's own head
evaluation is the same expression at the same values (`encodeBuild_fst`,
`Expr.eval_transport`), and what the head owes is only that the source's firing built it —
`entrySound_headBuild`. -/

/-- **A fresh build's obligation is exactly that its minted id is a source term.**
`entrySound_build`'s hypothesis is necessary and not only sufficient, which is why the reading
the correspondence delivers matters: read at arbitrary congruent terms it does not discharge
the rule-head case, and read at the ids (`entrySound_headBuild`) it does. -/
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

/-- **And the domain supplies the three source-text conditions.**
`EncodeDomain.queryEncodable` is stated per command; this is it at a rule, split the way the
correspondence consumes it — so a program `encode` claims never needs `hnv`, `hgr` and `hk`
assumed separately. -/
theorem Program.EncodeDomain.queryEncodable_of_mem {P : Program} (h : P.EncodeDomain)
    {r : Rule} (hr : Cmd.rule r ∈ P) :
    (∀ p ∈ r.query, p.Grounded) ∧ (∀ p ∈ r.query, p.NoValues) ∧ Query.VarsKeyed r.query :=
  ⟨fun p hp => ((h.queryEncodable _ hr).1 p hp).1,
    fun p hp => ((h.queryEncodable _ hr).1 p hp).2, (h.queryEncodable _ hr).2⟩

/-! ### The source reading at the ids themselves

`exists_sourceReading` picks *some* source term per query variable. A rule **head** cannot use
just any: `encodeBuild` mints its skolem over the ids the query bound, so the entry a head
writes is valued at `f` applied to those ids, and `mem_terms_of_entrySound_skolem` says
`Database.ViewsSound` there is *equivalent* to that application being a source term. Reading the
variables back as arbitrary congruent terms leaves exactly the gap
`encode_corresponds_invents_enode` refutes, read at a key column.

**The gap closes because the reading may be chosen to be the ids.** A variable at a key column
is read back by `Database.ViewsSound`, which hands out a source argument list *congruent* to the
key — and a congruence's endpoints are both present, so the id is itself a term the source
holds. `Matches` is congruence-closed (that is the whole of `CongUp`), so the source query
matches at the ids just as it matches at any other reading, and then the source's own head
evaluation builds the very term the target's head did. Nothing about `encode` is used; what
replaces `Database.GlobalsRead` is the stronger `Database.GlobalsAgree`, and the encoder
supplies it because a source `let` becomes a `let` of the *same* expression
(`encodeBuild_fst`). -/

/-- **The target's environment binds every source global to the same term.** Stronger than
`Database.GlobalsRead`, which allows a congruent one, and what the encoding gives: a source
`let` becomes `.letBind v (encodeBuild e n).1` and that expression *is* `e`. -/
def Database.GlobalsAgree (src : Database) (ρ : Env) : Prop :=
  ∀ v t, Env.lookup v src.env = some t → Env.lookup v ρ = some t

/-- Agreement is a reading: a global is a term the source holds, so it is congruent to
itself. -/
theorem Database.GlobalsAgree.globalsRead {src : Database} {ρ : Env} (hw : src.WF)
    (h : src.GlobalsAgree ρ) : src.GlobalsRead ρ := by
  intro v t i ht hi
  obtain rfl : t = i := Option.some.inj ((h v t ht).symm.trans hi)
  exact hw.envInTerms _ (Env.mem_of_lookup ht)

/-- **The id at a key column is itself a term the source holds.** `Database.ViewsSound` at the
enclosing read hands back a source argument list congruent to the key, and both endpoints of a
congruence are present. This is the fact the head-build case turns on, and it is what makes the
reading below well defined. -/
theorem mem_terms_of_patternArgVar {src d : Database} (hs : d.ViewsSound src) {ρt : Env}
    {v : Var} {p : Pattern} (h : PatternRead d ρt p) (hv : Pattern.ArgVar v p) :
    ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
  obtain ⟨j, t, hj, hc⟩ := exists_source_of_patternArgVar hs h hv
  exact ⟨j, hj, hc.mem_right⟩

/-- The reading that takes every variable to **the id itself**. Total, because
`Query.VarsKeyed` and `Database.GlobalsAgree` between them make `ρt` bind everything the query
mentions; the default value is never reached. -/
def idReading (ρt : Env) : Var → Term := fun v => (Env.lookup v ρt).getD (.lit (.int 0))

theorem idReading_eq {ρt : Env} {v : Var} {i : Term} (h : Env.lookup v ρt = some i) :
    idReading ρt v = i := by simp [idReading, h]

/-- **The source query matches at the ids the target read.** The reading of
`validQuerySubst_of_patternReads`, pinned: the substitution it returns binds every query
variable to *the id itself*, not merely to something congruent to it.

That is what a rule head needs and the weaker form does not give. `encodeBuild` writes
`@fView(is) ↦ (f(is), @Fiat)` over the ids, so `entrySound_build`'s hypothesis is
`f(is) ∈ src.terms`; with this substitution the source's own head evaluation is the same
expression at the same values, so the term it builds is that one and no congruence step is
needed at the key. -/
theorem exists_validQuerySubst_at_ids {src d : Database} (hb : src.TermsBuild)
    (hs : d.ViewsSound src) {q : Query} {ρt : Env} (hglob : src.GlobalsAgree ρt)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p) :
    ∃ τ, ValidQuerySubst src q τ ∧
      ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i →
        Env.lookup v (src.env ++ τ) = some i := by
  have hbound : ∀ v ∈ Query.vars q, ∃ i, Env.lookup v ρt = some i ∧ i ∈ src.terms := by
    intro v hv
    obtain ⟨p, hp, ha⟩ := hk v hv
    exact mem_terms_of_patternArgVar hs (hread p hp) ha
  have hgt : ∀ v ∈ Query.vars q, idReading ρt v ∈ src.terms := by
    intro v hv
    obtain ⟨i, hi, hm⟩ := hbound v hv
    rw [idReading_eq hi]; exact hm
  obtain ⟨τ, hv, hτ⟩ := validQuerySubst_of_patternReads hb hs
    (g := idReading ρt) (fun v t ht => idReading_eq (hglob v t ht)) hgt
    (fun v hv i hi => idReading_eq hi ▸ hgt v hv) hgr hread
  exact ⟨τ, hv, fun v hvq i hi => by rw [hτ v hvq, idReading_eq hi]⟩

/-- **And the two environments agree wherever a rule head may read.** A head variable is either
one the query binds — read as the id on both sides, by the substitution above — or a source
global, which `Database.GlobalsAgree` pins and which shadows the substitution on the source
side. This is the hypothesis `Expr.eval_transport` consumes. -/
theorem lookup_eq_of_at_ids {src d : Database} (hs : d.ViewsSound src) {q : Query} {ρt τ : Env}
    (hglob : src.GlobalsAgree ρt) (hk : Query.VarsKeyed q)
    (hread : ∀ p ∈ q, PatternRead d ρt p)
    (hτ : ∀ v ∈ Query.vars q, ∀ i, Env.lookup v ρt = some i →
      Env.lookup v (src.env ++ τ) = some i)
    {v : Var} (hv : v ∈ Query.vars q ∨ (Env.lookup v src.env).isSome) :
    Env.lookup v ρt = Env.lookup v (src.env ++ τ) := by
  rcases hv with hv | hv
  · obtain ⟨p, hp, ha⟩ := hk v hv
    obtain ⟨i, hi, -⟩ := mem_terms_of_patternArgVar hs (hread p hp) ha
    rw [hi, hτ v hv i hi]
  · obtain ⟨t, ht⟩ : ∃ t, Env.lookup v src.env = some t := Option.isSome_iff_exists.mp hv
    rw [hglob v t ht,
      Env.lookup_append_of_mem (Env.lookup_isSome_iff_mem_dom.mp (by rw [ht]; rfl)), ht]

/-! ### Transporting an evaluation between the two states

`Expr.eval` consults the primitive table — which no signature owns — and then
`Signature.IsCtor`, and nothing else. So an evaluation moves between the source and the target
on two conditions: the names it applies build in both, and the two environments agree on the
variables it reads. Both are supplied above at a rule head, which is what makes a head's two
evaluations the *same* term rather than congruent ones. -/

mutual

/-- **An evaluation transports along `Signature.IsCtor` at the names it applies.** -/
theorem Expr.eval_transport {s₁ s₂ : Signature} :
    ∀ (e : Expr) {ρ₁ ρ₂ : Env} {t : Term}, (∀ f ∈ e.fns, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ e.vars, Env.lookup v ρ₁ = Env.lookup v ρ₂) → e.eval s₁ ρ₁ = some t →
      e.eval s₂ ρ₂ = some t
  | .lit _, _, _, _, _, _, h => h
  | .var v, _, _, _, _, hv, h => by
      rw [Expr.eval] at h ⊢
      rw [← hv v (by simp [Expr.vars]), h]
  | .app f args, _, _, _, hc, hv, h => by
      have hfn : ∀ g ∈ Expr.fnsList args, s₁.IsCtor g → s₂.IsCtor g :=
        fun g hg => hc g (by simp [Expr.fns, hg])
      have hvl : ∀ v ∈ Expr.varsList args, Env.lookup v _ = Env.lookup v _ :=
        fun w hw => hv w (by simpa [Expr.vars] using hw)
      cases hp : Prim.ofName f with
      | some p =>
        simp only [Expr.eval, hp] at h ⊢
        obtain ⟨ts, hts, hap⟩ := Option.bind_eq_some_iff.mp h
        rw [Expr.evalList_transport args hfn hvl hts]
        exact hap
      | none =>
        simp only [Expr.eval, hp] at h ⊢
        by_cases hct : s₁.IsCtor f
        · rw [if_pos hct] at h
          obtain ⟨ts, hts, hap⟩ := Option.map_eq_some_iff.mp h
          rw [if_pos (hc f (by simp [Expr.fns]) hct),
            Expr.evalList_transport args hfn hvl hts]
          exact congrArg some hap
        · rw [if_neg hct] at h
          exact absurd h (by simp)

@[inherit_doc Expr.eval_transport]
theorem Expr.evalList_transport {s₁ s₂ : Signature} :
    ∀ (es : List Expr) {ρ₁ ρ₂ : Env} {ts : List Term},
      (∀ f ∈ Expr.fnsList es, s₁.IsCtor f → s₂.IsCtor f) →
      (∀ v ∈ Expr.varsList es, Env.lookup v ρ₁ = Env.lookup v ρ₂) →
      Expr.evalList s₁ es ρ₁ = some ts → Expr.evalList s₂ es ρ₂ = some ts
  | [], _, _, _, _, _, h => h
  | e :: es, _, _, _, hc, hv, h => by
      rw [Expr.evalList] at h ⊢
      obtain ⟨t, ht, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, hcons⟩ := Option.map_eq_some_iff.mp hrest
      rw [Expr.eval_transport e (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) ht,
        Expr.evalList_transport es (fun g hg => hc g (by simp [Expr.fnsList, hg]))
          (fun w hw => hv w (by simp [Expr.varsList, hw])) hts]
      exact congrArg some hcons

end

/-- **`Database.GlobalsInline` along a signature that still builds what it built.** The form
a command's step supplies: only a declaration moves the signature, and under
`Program.CtorDecls` it only ever adds a constructor. -/
theorem Database.GlobalsInline.mono_ctor {src src' : Database} {G : List (Var × Expr)}
    (h : src.GlobalsInline G) (hsig : ∀ f, src.sig.IsCtor f → src'.sig.IsCtor f)
    (henv : ∀ v t, Env.lookup v src.env = some t → Env.lookup v src'.env = some t) :
    src'.GlobalsInline G :=
  h.mono_src (fun e _ he => Expr.eval_transport e (fun f _ => hsig f) (fun _ _ => rfl) he) henv

/-! ### The head-build case, discharged

Everything above composes into the case the completeness half's rule-head obligation is: the
target matched the encoded query, its head built `.app f args`, and the entry it wrote is
`@fView(is) ↦ (f(is), @Fiat)` for `is` the arguments' values *in the target*. Because the source
reading is the ids, the source's evaluation of the same expression gives the same `is`, and
`entrySound_build` needs only that the source holds `f(is)`.

That last thing is `hfired`, and it is the honest residue: it is the source's own rule firing,
which is `RunRules`' fixpoint and not a property of either state alone. The refuted fact — that
the key's application is a source term for no reason but that the target keyed on it — is *not*
among the hypotheses. -/

/-- **A rule head's build writes a sound view entry.**

`hfired` is the only thing not supplied by the two states: that the source rule, fired at the
substitution the correspondence returns, holds the term its own head evaluation built. Every
other hypothesis is either an invariant this file already carries (`Database.ViewsSound`,
`Database.Diag`, subterm closure), a property of the source (`Database.WF`,
`Database.TermsBuild`, `Database.GlobalsAgree`), or a decidable condition on the source text
(`Pattern.NoValues`, `Pattern.Grounded`, `Query.VarsKeyed`, and that the head's names build and
its variables are the query's or globals).

`hval` is what the target wrote, read off the encoder: `encodeBuild`'s naming expression *is*
`.app f args` (`encodeBuild_fst`), so the value column is that expression evaluated in the
target and the key is its arguments'. -/
theorem entrySound_headBuild_post {src src' tgt : Database} (hw : src'.WF)
    (hb : src.TermsBuild) (hs : tgt.ViewsSound src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hglob : src.GlobalsAgree (tgt.env ++ σ)) (hnv : ∀ p ∈ q, p.NoValues)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hmatch : ValidQuerySubst tgt (encodeQuery q n).1 σ)
    {f : FnName} {args : List Expr} {is : List Term} {m : Nat}
    (hctor : ∀ g ∈ (Expr.app f args).fns, tgt.sig.IsCtor g → src.sig.IsCtor g)
    (hvars : ∀ v ∈ (Expr.app f args).vars, v ∈ Query.vars q ∨ (Env.lookup v src.env).isSome)
    (hval : (encodeBuild (.app f args) m).1.eval tgt.sig (tgt.env ++ σ) = some (.app f is))
    (hfired : ∀ τ, ValidQuerySubst src q τ →
      (Expr.app f args).eval src.sig (src.env ++ τ) = some (.app f is) →
      Term.app f is ∈ src'.terms) :
    EntrySound src' f is (.app f is) := by
  rw [encodeBuild_fst] at hval
  have hread := patternReads_of_encodeQuery hd hsc hnv hk hmatch
  obtain ⟨τ, hv, hτ⟩ := exists_validQuerySubst_at_ids hb hs hglob hgr hk hread
  exact entrySound_build hw (hfired τ hv (Expr.eval_transport _ hctor
    (fun v hvv => lookup_eq_of_at_ids hs hglob hk hread hτ (hvars v hvv)) hval))

@[inherit_doc entrySound_headBuild_post]
theorem entrySound_headBuild {src tgt : Database} (hw : src.WF) (hb : src.TermsBuild)
    (hs : tgt.ViewsSound src) (hd : tgt.Diag)
    (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat} {σ : Env}
    (hglob : src.GlobalsAgree (tgt.env ++ σ)) (hnv : ∀ p ∈ q, p.NoValues)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hmatch : ValidQuerySubst tgt (encodeQuery q n).1 σ)
    {f : FnName} {args : List Expr} {is : List Term} {m : Nat}
    (hctor : ∀ g ∈ (Expr.app f args).fns, tgt.sig.IsCtor g → src.sig.IsCtor g)
    (hvars : ∀ v ∈ (Expr.app f args).vars, v ∈ Query.vars q ∨ (Env.lookup v src.env).isSome)
    (hval : (encodeBuild (.app f args) m).1.eval tgt.sig (tgt.env ++ σ) = some (.app f is))
    (hfired : ∀ τ, ValidQuerySubst src q τ →
      (Expr.app f args).eval src.sig (src.env ++ τ) = some (.app f is) →
      Term.app f is ∈ src.terms) :
    EntrySound src f is (.app f is) :=
  entrySound_headBuild_post hw hb hs hd hsc hglob hnv hgr hk hmatch hctor hvars hval hfired

/-- **And a rule head's `union` writes a sound edge.** The `Database.EdgesSound` counterpart:
`encodeAction` writes `@UF (ordering-max x₁ x₂) ↦ (ordering-min x₁ x₂, pf)` over the two
operands' naming expressions, which are the operands themselves, so the pair the edge relates
is the pair the source's own `union` asserted. `ho` absorbs whichever order `ordering-max`
picked, as `cong_of_eqs` does for a top-level `union`. -/
theorem cong_headUnion_post {src src' tgt : Database} (hb : src.TermsBuild)
    (hs : tgt.ViewsSound src)
    (hd : tgt.Diag) (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat}
    {σ : Env} (hglob : src.GlobalsAgree (tgt.env ++ σ)) (hnv : ∀ p ∈ q, p.NoValues)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hmatch : ValidQuerySubst tgt (encodeQuery q n).1 σ)
    {e₁ e₂ : Expr} {t₁ t₂ : Term} {m₁ m₂ : Nat}
    (hctor : ∀ g ∈ e₁.fns ∪ e₂.fns, tgt.sig.IsCtor g → src.sig.IsCtor g)
    (hvars : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∈ Query.vars q ∨ (Env.lookup v src.env).isSome)
    (hv₁ : (encodeBuild e₁ m₁).1.eval tgt.sig (tgt.env ++ σ) = some t₁)
    (hv₂ : (encodeBuild e₂ m₂).1.eval tgt.sig (tgt.env ++ σ) = some t₂)
    (hfired : ∀ τ, ValidQuerySubst src q τ → e₁.eval src.sig (src.env ++ τ) = some t₁ →
      e₂.eval src.sig (src.env ++ τ) = some t₂ → (t₁, t₂) ∈ src'.eqs)
    {t p : Term} (ho : (t = t₁ ∧ p = t₂) ∨ (t = t₂ ∧ p = t₁)) : Cong src' t p := by
  rw [encodeBuild_fst] at hv₁
  rw [encodeBuild_fst] at hv₂
  have hread := patternReads_of_encodeQuery hd hsc hnv hk hmatch
  obtain ⟨τ, hv, hτ⟩ := exists_validQuerySubst_at_ids hb hs hglob hgr hk hread
  have hlk : ∀ v ∈ e₁.vars ∪ e₂.vars,
      Env.lookup v (tgt.env ++ σ) = Env.lookup v (src.env ++ τ) :=
    fun v hvv => lookup_eq_of_at_ids hs hglob hk hread hτ (hvars v hvv)
  exact cong_of_eqs (hfired τ hv
    (Expr.eval_transport _ (fun g hg => hctor g (by simp [hg]))
      (fun v hvv => hlk v (by simp [hvv])) hv₁)
    (Expr.eval_transport _ (fun g hg => hctor g (by simp [hg]))
      (fun v hvv => hlk v (by simp [hvv])) hv₂)) ho

@[inherit_doc cong_headUnion_post]
theorem cong_headUnion {src tgt : Database} (hb : src.TermsBuild) (hs : tgt.ViewsSound src)
    (hd : tgt.Diag) (hsc : ∀ t ∈ tgt.terms, t.subterms ⊆ tgt.terms) {q : Query} {n : Nat}
    {σ : Env} (hglob : src.GlobalsAgree (tgt.env ++ σ)) (hnv : ∀ p ∈ q, p.NoValues)
    (hgr : ∀ p ∈ q, p.Grounded) (hk : Query.VarsKeyed q)
    (hmatch : ValidQuerySubst tgt (encodeQuery q n).1 σ)
    {e₁ e₂ : Expr} {t₁ t₂ : Term} {m₁ m₂ : Nat}
    (hctor : ∀ g ∈ e₁.fns ∪ e₂.fns, tgt.sig.IsCtor g → src.sig.IsCtor g)
    (hvars : ∀ v ∈ e₁.vars ∪ e₂.vars, v ∈ Query.vars q ∨ (Env.lookup v src.env).isSome)
    (hv₁ : (encodeBuild e₁ m₁).1.eval tgt.sig (tgt.env ++ σ) = some t₁)
    (hv₂ : (encodeBuild e₂ m₂).1.eval tgt.sig (tgt.env ++ σ) = some t₂)
    (hfired : ∀ τ, ValidQuerySubst src q τ → e₁.eval src.sig (src.env ++ τ) = some t₁ →
      e₂.eval src.sig (src.env ++ τ) = some t₂ → (t₁, t₂) ∈ src.eqs)
    {t p : Term} (ho : (t = t₁ ∧ p = t₂) ∨ (t = t₂ ∧ p = t₁)) : Cong src t p :=
  cong_headUnion_post hb hs hd hsc hglob hnv hgr hk hmatch hctor hvars hv₁ hv₂ hfired ho

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
generated name anywhere — and `EncodeDomain.queryEncodable` is the one it fails. Before that
clause was folded in, this program was in the domain and the refutation below was a program
the encoder claimed and got wrong. -/
theorem litProgram_not_encodeDomain : ¬ litProgram.EncodeDomain := by
  intro h
  have hq := h.queryEncodable (.rule { query := litQuery, actions := [], ruleset := "" })
    (by simp [litProgram])
  exact (hq.1 (.expr (.lit (.int 1))) (by simp [litQuery])).1 (.int 1) rfl

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
  simp only [cmdEffect, evalTopAction_expr, evalAction, Expr.eval, Expr.evalList, satSrcD]
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
  simp only [cmdEffect, evalTopAction_expr, evalAction, Expr.eval, Expr.evalList, wSrcD]
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
    intro c hc
    simp only [wProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h <;>
      simp_all [Cmd.CtorDecl, wADecl, wFDecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [wProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · exact ⟨fun p hp => ⟨wSrcRule_grounded p hp, wSrcRule_noValues p hp⟩, wSrcRule_varsKeyed⟩
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inr (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

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

/-! #### The head-build case, run at the pair

`exists_validQuerySubst_composed_witness` checks the correspondence; these check the *head's*
use of it. `wProgram`'s rule has an empty head, so the expression below is a build the rule
could have made rather than one it did — which is the point: `entrySound_headBuild` is a
statement about the two states and one head expression, and `hfired` is where a real head's
obligation lives. -/

/-- **`Database.GlobalsAgree` at a state that binds a global**, so the strengthening of
`Database.GlobalsRead` is not carried by its vacuous case at `wProgram`, which has no `let`.
The two environments bind `x` to the *same* term, which is what it adds. -/
theorem globalsAgree_nonvacuous :
    ({ satSrcD with env := [("x", .app "A" [])] } : Database).GlobalsAgree
      [("x", .app "A" [])] := by
  intro v t ht
  obtain ⟨rfl, rfl⟩ : v = "x" ∧ Term.app "A" [] = t := by simpa using ht
  simp

/-- **The reading at the ids, run at the pair.** `exists_validQuerySubst_composed_witness`'s
last conjunct with the reading pinned: the source substitution binds `x` to the very term
`wSubst` bound it to, and not merely to something congruent to it. -/
theorem exists_validQuerySubst_at_ids_witness :
    ∃ τ, ValidQuerySubst wSrcD wSrcRule.query τ ∧
      Env.lookup "x" (wSrcD.env ++ τ) = some (.app "A" []) := by
  obtain ⟨τ, hv, hτ⟩ := exists_validQuerySubst_at_ids wSrcD_termsBuild wTarget_viewsSound
    (by simp [Database.GlobalsAgree, wSrcD, wSrcBase, Database.empty])
    wSrcRule_grounded wSrcRule_varsKeyed
    (patternReads_of_encodeQuery wTarget_diag wTarget_subtermClosed wSrcRule_noValues
      wSrcRule_varsKeyed wTarget_validQuerySubst)
  exact ⟨τ, hv, hτ "x" (by rw [wSrcRule_query_vars]; simp) (.app "A" []) rfl⟩

/-- `F` is a constructor on the source side too, which is what `entrySound_headBuild`'s
`hctor` asks at the one name the head expression applies. -/
theorem wSrcSig_isCtor_F : wSrcSig.IsCtor "F" := ⟨wFDecl, rfl, rfl⟩

/-- **All of `entrySound_headBuild`'s hypotheses hold together at the reachable pair, and its
conclusion is a view entry the target actually holds.**

The head expression is `(F x)`, the build a rule with that head would make: `encodeBuild`'s
naming expression is `(F x)` itself, the target evaluates it to `F(A)` at the substitution the
encoded query matched under, and the entry that pins is `@FView(A) ↦ (F(A), @Fiat)` —
`wTarget_out_view`, the row the run really wrote. `hfired` is `wSrcD_mem_F`. -/
theorem entrySound_headBuild_witness :
    wTarget.Out (viewName "F") [.app "A" []] [.app "F" [.app "A" []], .app fiatName []] ∧
      EntrySound wSrcD "F" [.app "A" []] (.app "F" [.app "A" []]) := by
  refine ⟨wTarget_out_view, entrySound_headBuild (q := wSrcRule.query) (n := 0) (m := 0)
    wSrcD_wf wSrcD_termsBuild wTarget_viewsSound wTarget_diag wTarget_subtermClosed
    (by simp [Database.GlobalsAgree, wSrcD, wSrcBase, Database.empty])
    wSrcRule_noValues wSrcRule_grounded wSrcRule_varsKeyed wTarget_validQuerySubst
    (f := "F") (args := [.var "x"]) (fun g hg _ => ?_) (fun v hv => ?_) rfl
    (fun _ _ _ => wSrcD_mem_F)⟩
  · obtain rfl : g = "F" := by simpa [Expr.fns, Expr.fnsList] using hg
    exact wSrcSig_isCtor_F
  · obtain rfl : v = "x" := by simpa [Expr.vars, Expr.varsList] using hv
    exact Or.inl (by rw [wSrcRule_query_vars]; simp)

/-- **`cong_headUnion` run at the same pair.** What it checks is that the composition typechecks
against a reachable pair with every hypothesis discharged; what it does **not** check is a
non-reflexive edge, because `wProgram` has no `union` inside its rule head and `wSrcD.eqs` is
the diagonal.

**The non-reflexive case is `cong_headUnion_union_witness`**, at the end of this file: a rule
head that unions two distinct terms, both runs stepped, and `Cong` concluded between terms
that are not equal. -/
theorem cong_headUnion_witness :
    Cong wSrcD (.app "F" [.app "A" []]) (.app "F" [.app "A" []]) := by
  refine cong_headUnion (q := wSrcRule.query) (n := 0) (m₁ := 0) (m₂ := 0)
    wSrcD_termsBuild wTarget_viewsSound wTarget_diag wTarget_subtermClosed
    (by simp [Database.GlobalsAgree, wSrcD, wSrcBase, Database.empty])
    wSrcRule_noValues wSrcRule_grounded wSrcRule_varsKeyed wTarget_validQuerySubst
    (e₁ := .app "F" [.var "x"]) (e₂ := .app "F" [.var "x"])
    (fun g hg _ => ?_) (fun v hv => ?_) rfl rfl
    (fun _ _ _ _ => wSrcD_wf.eqsRefl _ wSrcD_mem_F) (Or.inl ⟨rfl, rfl⟩)
  · obtain rfl : g = "F" := by simpa [Expr.fns, Expr.fnsList] using hg
    exact wSrcSig_isCtor_F
  · obtain rfl : v = "x" := by simpa [Expr.vars, Expr.varsList] using hv
    exact Or.inl (by rw [wSrcRule_query_vars]; simp)

/-! ### A `union` inside a rule head

`cong_headUnion_witness` above runs the head's `union` case at `wProgram`, where `wSrcD.eqs`
is the diagonal: the pair it concludes about is `t = t`, and the case the lemma exists for —
an equation between **distinct** terms — is untested. `uProgram` below is the program that
tests it.

`(union (A) (B))` is a rule *head*, `(A)` and `(B)` are two distinct nullary constructors,
and both runs are stepped. `hfired` is discharged from the source's own top-level `union` of
the same pair, exactly as `entrySound_headBuild_witness` discharges its `hfired` from the
term `wProgram`'s own action built: the hypothesis is "the source rule, fired at the
substitution the correspondence returns, asserted this pair", and what a witness owes is a
reachable state where the pair *is* asserted and the head's two operands evaluate to it.

**The encoded run is stepped up to its last command, and that is a finding rather than an
omission.** `encode` emits `Cmd.saturate rebuildRuleset` after the top-level `union`, and
`uTgt_saturate_infinite` below is the compiled reason no state satisfies it: a `union`
between distinct built terms puts a `@UF` edge on a view's e-class column, the e-class
rebuild rule re-keys that view row, the displaced row *stays* (`terms` only grows), and the
collision between the two rows builds the proof tower `Encoding/Encode.lean`'s `Rebuilt`
docstring describes — the one `identityVals := some 1` disarms for a *self*-collision only.
So `ProgramStep Database.empty (encode P) tgt` is satisfiable at a `P` that only builds
(`satProgram_programStep`) and unsatisfiable as soon as `P` asserts an equation between
distinct terms. -/

/-- `(A)`. -/
def uA : Term := .app "A" []

/-- `(B)`, the term `uProgram` unions `uA` with. Above `uA` in `Term.blt`, so it is the
`ordering-max` endpoint and the `@UF` edge is keyed at it. -/
def uB : Term := .app "B" []

theorem uA_ne_uB : uA ≠ uB := by simp [uA, uB]

/-- `(rule ((A)) ((union (A) (B))))`: one grounded pattern, and a head that is a `union` of
two distinct terms. -/
def uSrcRule : Rule :=
  { query := [.expr (.app "A" [])],
    actions := [.union (.app "A" []) (.app "B" [])], ruleset := "" }

/-- Two nullary constructors, the rule whose head unions them, and the same `union` at top
level — which is what puts the pair in `eqs` and what gives the encoded query a row to match
on. -/
def uProgram : Program :=
  [.decl "A" wADecl, .decl "B" wADecl, .rule uSrcRule,
   .action (.union (.app "A" []) (.app "B" []))]

/-! #### The source side -/

/-- The signature the two declarations install. -/
def uSrcSig : Signature :=
  Function.update (Function.update Database.empty.sig "A" (some wADecl)) "B" (some wADecl)

/-- After the two declarations and the rule: no term yet. -/
def uSrcBase : Database :=
  { Database.empty with
    sig := uSrcSig,
    rules := insert uSrcRule Database.empty.rules }

/-- **The source state `uProgram` runs to**: the rule registered, `(A)` and `(B)` built, and
the equation between them asserted. -/
def uSrcD : Database := uSrcBase.addEq uA uB

private theorem uSrcBase_terms : uSrcBase.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [uSrcBase, Database.empty] at hu

theorem uSrcD_terms : uSrcD.terms = uA.subterms ∪ uB.subterms := by
  rw [uSrcD, Database.addEq_terms, uSrcBase_terms, Set.empty_union]

/-- **And it is reachable**: two declarations, the rule, and the `union`. -/
theorem uProgramStep_src : ProgramStep Database.empty uProgram uSrcD := by
  refine .cons ⟨_, rfl, .refl⟩ (.cons ⟨_, rfl, .refl⟩
    (.cons ⟨_, rfl, .refl⟩ (.cons ⟨uSrcD, ?_, .refl⟩ .nil)))
  change cmdEffect _ (.action (.union (.app "A" []) (.app "B" []))) = some uSrcD
  simp only [cmdEffect, evalTopAction_union, evalAction, Expr.eval, Expr.evalList, uSrcD,
    uA, uB]
  rfl

/-- **The pair is asserted**, which is what makes the witness non-reflexive. -/
theorem uSrcD_mem_eq : (uA, uB) ∈ uSrcD.eqs := by
  rw [uSrcD, Database.addEq_eqs]; exact Set.mem_insert _ _

/-- **So the source state is not diagonal** — the one thing `wSrcD` is and this is not. -/
theorem uSrcD_not_diag : ¬ uSrcD.Diag := fun h => uA_ne_uB (h _ uSrcD_mem_eq)

theorem uSrcD_mem_A : uA ∈ uSrcD.terms := by
  rw [uSrcD_terms]; exact Or.inl (Term.self_mem_subterms _)

theorem uSrcD_mem_B : uB ∈ uSrcD.terms := by
  rw [uSrcD_terms]; exact Or.inr (Term.self_mem_subterms _)

theorem uSrcD_wf : uSrcD.WF := by
  refine Database.WF.addEq ?_ _ _ (by simp [uA, uB, Term.isLit])
  exact { eqsRefl := fun t ht => absurd (uSrcBase_terms ▸ ht) (by simp),
          subtermClosed := fun t ht => absurd (uSrcBase_terms ▸ ht) (by simp),
          envInTerms := by simp [uSrcBase, Database.empty],
          litsIsolated := by simp [Database.LitsIsolated, uSrcBase, Database.empty] }

/-- The two terms the state holds, enumerated. -/
private theorem uSrcD_mem_cases {t : Term} (h : t ∈ uSrcD.terms) : t = uA ∨ t = uB := by
  rw [uSrcD_terms] at h
  simpa [uA, uB, or_comm] using h

/-- **`Database.TermsBuild` holds**: both applications the state holds are declared
constructors, neither shadowing a primitive. -/
theorem uSrcD_termsBuild : uSrcD.TermsBuild := by
  intro f as hm
  rcases uSrcD_mem_cases hm with h | h
  · obtain ⟨rfl, rfl⟩ : f = "A" ∧ as = [] := by simpa [uA] using h
    exact ⟨rfl, wADecl, by simp [uSrcD, uSrcBase, uSrcSig], rfl⟩
  · obtain ⟨rfl, rfl⟩ : f = "B" ∧ as = [] := by simpa [uB] using h
    exact ⟨rfl, wADecl, by simp [uSrcD, uSrcBase, uSrcSig], rfl⟩

/-! #### The target side

`wProgram_programStep`'s shape at one command more and one command short: `@Rule_0` is
declared at arity 1 as there, two table triples instead of two, and the encoded rule's head
is where the `@UF` set appears — but the trailing `Cmd.saturate rebuildRuleset` is *not*
stepped, and `uTgt_saturate_infinite` is why. -/

/-- `(ordering-max (A) (B))`, the `@UF` key the encoded `union` writes at. `(A)` is below
`(B)` in `Term.blt`, so this is `(B)`. -/
def uMaxE : Expr := maxE (.app "A" []) (.app "B" [])

/-- `(ordering-min (A) (B))`, which is `(A)`. -/
def uMinE : Expr := minE (.app "A" []) (.app "B" [])

/-- `B`'s e-class rebuild rule, `satRebuildRule` at the other constructor. This is the rule
that fires here and does not fire at `wProgram`: its `@UF` premise has a row to read. -/
def uRebuildB : Rule :=
  { query := [.values [.var "@e", .var "@p"] (viewName "B") [],
              .values [.var "@x", .var "@q"] ufName [.var "@e"]],
    actions := [.set (viewName "B") [] [.var "@x", transE (.var "@p") (.var "@q")]],
    ruleset := rebuildRuleset }

/-- The source rule's encoding: one view read, and a head that `set`s the `@UF` edge under
the firing's own `@Rule_0` justification. -/
def uEncRule : Rule :=
  { query := [.values [.var "@v0", .var "@v1"] (viewName "A") []],
    actions := [.set (termName "A") [.app "A" []] [],
                .set (viewName "A") [] [.app "A" [], fiatE],
                .set (termName "B") [.app "B" []] [],
                .set (viewName "B") [] [.app "B" [], fiatE],
                .set ufName [uMaxE] [uMinE, ruleE 0 [.var "@v1"]]],
    ruleset := "" }

/-- **The prelude `encode uProgram` emits**: eleven declarations — the three fixed proof
heads, `@Rule_0`, `@UF` and the two table triples — and then three rules. `congrArities` is
empty at two nullary constructors, so no `@Congr_k` is declared. -/
def uEncodedPrelude : Program :=
  [.decl fiatName (proofDecl 0), .decl symName (proofDecl 1), .decl transName (proofDecl 2),
   .decl (ruleName 0) (proofDecl 1),
   .decl ufName ufDecl,
   .decl "A" (skolemDecl 0), .decl (viewName "A") (viewDecl 0),
   .decl (termName "A") (termDecl 0),
   .decl "B" (skolemDecl 0), .decl (viewName "B") (viewDecl 0),
   .decl (termName "B") (termDecl 0),
   .rule pathCompressRule, .rule satRebuildRule, .rule uRebuildB, .rule uEncRule]

/-- **And what the one source action becomes**: four `set`s for the two operands' builds and
the `@UF` edge. `wEncodedActions`' counterpart minus its last command, which is the one no
state satisfies. -/
def uEncodedSets : Program :=
  [.action (.set (termName "A") [.app "A" []] []),
   .action (.set (viewName "A") [] [.app "A" [], fiatE]),
   .action (.set (termName "B") [.app "B" []] []),
   .action (.set (viewName "B") [] [.app "B" [], fiatE]),
   .action (.set ufName [uMaxE] [uMinE, fiatE])]

/-- The twenty commands the run below steps, as `satEncoded` and `wEncoded` are stepped. -/
def uEncodedPrefix : Program := uEncodedPrelude ++ uEncodedSets

/-- **And the twenty-first, which is the whole of what is left.** -/
theorem uEncoded_eq : encode uProgram = uEncodedPrefix ++ [.saturate rebuildRuleset] := rfl

/-- The signature `encode uProgram`'s prelude installs, in declaration order. -/
def uSig : Signature :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update
        Database.empty.sig
        fiatName (some (proofDecl 0))) symName (some (proofDecl 1)))
        transName (some (proofDecl 2))) (ruleName 0) (some (proofDecl 1)))
        ufName (some ufDecl))
        "A" (some (skolemDecl 0))) (viewName "A") (some (viewDecl 0)))
        (termName "A") (some (termDecl 0))
        ) "B" (some (skolemDecl 0))) (viewName "B") (some (viewDecl 0)))
        (termName "B") (some (termDecl 0))

set_option maxHeartbeats 2000000 in
-- As `wSig_merge`: `split_ifs` on an eleven-deep `Function.update` chain, each goal
-- deciding an `FnDecl` equality through `viewName`/`termName`.
/-- **The three `:merge` functions with a body are `@UF` and the two views.** The two term
relations are `:no-merge` and everything else is a constructor. -/
private theorem uSig_merge {f : FnName} {decl : FnDecl} {body : List Action} {res : List Expr}
    (hsig : uSig f = some decl) (hm : decl.merge = some (.merge body res)) :
    (f = ufName ∧ decl = ufDecl) ∨ (f = viewName "A" ∧ decl = viewDecl 0) ∨
      (f = viewName "B" ∧ decl = viewDecl 0) := by
  simp only [uSig, Function.update_apply, Database.empty] at hsig
  split_ifs at hsig <;>
    obtain rfl := Option.some.inj hsig
    <;> first
      | exact Or.inl ⟨by assumption, rfl⟩
      | exact Or.inr (Or.inl ⟨by assumption, rfl⟩)
      | exact Or.inr (Or.inr ⟨by assumption, rfl⟩)
      | simp [proofDecl, skolemDecl, termDecl] at hm

/-- After the prelude and the encoded rule: eleven declarations and four rules. -/
def uPrelude : Database :=
  { Database.empty with
    sig := uSig,
    rules := insert uEncRule (insert uRebuildB (insert satRebuildRule
      (insert pathCompressRule Database.empty.rules))) }

/-- `@ATerm(A)`. -/
def uATermE : Term := .app (termName "A") [uA]

/-- `@AView() ↦ (A, @Fiat)`. -/
def uAViewE : Term := .app (viewName "A") [uA, .app fiatName []]

/-- `@BTerm(B)`. -/
def uBTermE : Term := .app (termName "B") [uB]

/-- `@BView() ↦ (B, @Fiat)`, the row the rebuild displaces and `terms` keeps. -/
def uBViewE : Term := .app (viewName "B") [uB, .app fiatName []]

/-- `@UF(B) ↦ (A, @Fiat)`, the edge the top-level `union` writes: keyed at `ordering-max`,
which is `(B)`. -/
def uUFE : Term := .app ufName [uB, uA, .app fiatName []]

/-- The three states the five `set`s pass through, named for the reason `wS1` is. -/
private def uS1 : Database := uPrelude.addTerm uATermE

@[inherit_doc uS1] private def uS2 : Database := uS1.addTerm uAViewE

@[inherit_doc uS1] private def uS3 : Database := uS2.addTerm uBTermE

@[inherit_doc uS1] private def uS4 : Database := uS3.addTerm uBViewE

/-- **The state `encode uProgram` runs to before its rebuild.** -/
def uTgt : Database := uS4.addTerm uUFE

theorem uTgt_sig : uTgt.sig = uSig := rfl

theorem uTgt_rules : uTgt.rules = uPrelude.rules := rfl

theorem uTgt_env : uTgt.env = [] := rfl

theorem uPrelude_terms : uPrelude.terms = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨u, hu⟩ := Database.mem_terms_iff.mp ht
  simp [uPrelude, Database.empty] at hu

theorem uTgt_terms : uTgt.terms =
    uATermE.subterms ∪ uAViewE.subterms ∪ uBTermE.subterms ∪ uBViewE.subterms ∪
      uUFE.subterms := by
  simp [uTgt, uS4, uS3, uS2, uS1, uPrelude_terms, Set.union_assoc]

/-- The eight terms the run holds, enumerated. -/
private theorem uTgt_mem_cases {t : Term} (h : t ∈ uTgt.terms) :
    t = uUFE ∨ t = uBViewE ∨ t = uBTermE ∨ t = uB ∨ t = uAViewE ∨
      t = Term.app fiatName [] ∨ t = uATermE ∨ t = uA := by
  rw [uTgt_terms] at h
  simpa [uATermE, uAViewE, uBTermE, uBViewE, uUFE, uA, uB] using h

/-- Only `Database.addTerm` writes, so the state is diagonal — the encoded program asserts
no equation even here, where the source it encodes asserts one. -/
theorem uTgt_diag : uTgt.Diag := by
  have h : uPrelude.Diag := fun p hp => absurd hp (by simp [uPrelude, Database.empty])
  exact ((((h.addTerm _).addTerm _).addTerm _).addTerm _).addTerm _

/-- The target's subterm closure. -/
theorem uTgt_subtermClosed : ∀ t ∈ uTgt.terms, t.subterms ⊆ uTgt.terms := by
  intro t ht
  rw [uTgt_terms] at ht ⊢
  rcases ht with (((h | h) | h) | h) | h <;> intro s hs <;>
    first
      | exact Or.inl (Or.inl (Or.inl (Or.inl (Term.subterms_subset_of_mem h hs))))
      | exact Or.inl (Or.inl (Or.inl (Or.inr (Term.subterms_subset_of_mem h hs))))
      | exact Or.inl (Or.inl (Or.inr (Term.subterms_subset_of_mem h hs)))
      | exact Or.inl (Or.inr (Term.subterms_subset_of_mem h hs))
      | exact Or.inr (Term.subterms_subset_of_mem h hs)

theorem uTgt_mem_viewA : uAViewE ∈ uTgt.terms := by
  rw [uTgt_terms]
  exact Or.inl (Or.inl (Or.inl (Or.inr (Term.self_mem_subterms _))))

theorem uTgt_mem_viewB : uBViewE ∈ uTgt.terms := by
  rw [uTgt_terms]
  exact Or.inl (Or.inr (Term.self_mem_subterms _))

theorem uTgt_mem_uf : uUFE ∈ uTgt.terms := Database.mem_addTerm _ _

theorem uTgt_mem_A : uA ∈ uTgt.terms :=
  uTgt_subtermClosed _ uTgt_mem_viewA
    (Term.arg_subterms (show uA ∈ [uA, Term.app fiatName []] by simp)
      (Term.self_mem_subterms _))

theorem uTgt_mem_B : uB ∈ uTgt.terms :=
  uTgt_subtermClosed _ uTgt_mem_viewB
    (Term.arg_subterms (show uB ∈ [uB, Term.app fiatName []] by simp)
      (Term.self_mem_subterms _))

theorem uTgt_mem_fiat : Term.app fiatName [] ∈ uTgt.terms :=
  uTgt_subtermClosed _ uTgt_mem_viewA
    (Term.arg_subterms (show Term.app fiatName [] ∈ [uA, Term.app fiatName []] by simp)
      (Term.self_mem_subterms _))

/-- **The two view rows `uTgt` holds**, pinned: of the eight terms, three are too short to be
a view entry at all, the two term-relation rows are one column wide, and the `@UF` row goes by
name (`viewName_ne_ufName`) — its width is a nullary view entry's plus one. -/
private theorem uTgt_mem_view {f : FnName} {cs : List Term} {e pf : Term}
    (hmem : Term.app (viewName f) (cs ++ [e, pf]) ∈ uTgt.terms) :
    (f = "A" ∧ cs = [] ∧ e = uA) ∨ (f = "B" ∧ cs = [] ∧ e = uB) := by
  rcases uTgt_mem_cases hmem with h' | h' | h' | h' | h' | h' | h' | h' <;>
      simp only [uUFE, uBViewE, uBTermE, uAViewE, uATermE, uA, uB, Term.app.injEq] at h' <;>
    [skip; skip; skip; skip; skip; skip; skip; skip]
  · exact absurd h'.1 viewName_ne_ufName
  · refine Or.inr ⟨viewName_inj h'.1, ?_⟩
    obtain rfl : cs = [] := by
      have hl : (cs ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨rfl, (show e = uB ∧ pf = Term.app fiatName [] by simpa [uB] using h'.2).1⟩
  · have hl : (cs ++ [e, pf]).length = 1 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · refine Or.inl ⟨viewName_inj h'.1, ?_⟩
    obtain rfl : cs = [] := by
      have hl : (cs ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨rfl, (show e = uA ∧ pf = Term.app fiatName [] by simpa [uA] using h'.2).1⟩
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · have hl : (cs ++ [e, pf]).length = 1 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega
  · have hl : (cs ++ [e, pf]).length = 0 := by rw [h'.2]; rfl
    simp only [List.length_append, List.length_cons] at hl
    omega

/-- The same read through `Database.Out`, which on a diagonal state is a lookup. -/
private theorem uTgt_out_view {f : FnName} {cs : List Term} {e pf : Term}
    (ho : uTgt.Out (viewName f) cs [e, pf]) :
    (f = "A" ∧ cs = [] ∧ e = uA) ∨ (f = "B" ∧ cs = [] ∧ e = uB) := by
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : cs = bs :=
    List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag uTgt_diag h)
  exact uTgt_mem_view hmem

/-- **`Database.ViewsSound` holds at `uTgt`**: the two rows the builds wrote, each
`entrySound_build` at a term the source holds. -/
theorem uTgt_viewsSound : uTgt.ViewsSound uSrcD := by
  intro f cs e pf ho
  rcases uTgt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact entrySound_build uSrcD_wf uSrcD_mem_A
  · exact entrySound_build uSrcD_wf uSrcD_mem_B

/-! #### The run, and the head's `union` at it -/

set_option maxHeartbeats 2000000 in
-- Fifteen `cmdEffect` reductions at a state that grows by a `Function.update` each time, as
-- `satProgram_programStep`; the default budget is short.
/-- The fifteen declaration and rule commands, stepped: each a `cmdEffect` and a reflexive
merge phase. -/
theorem uPreludeStep : ProgramStep Database.empty uEncodedPrelude uPrelude := by
  iterate 14 refine .cons ⟨_, rfl, .refl⟩ ?_
  exact .cons ⟨uPrelude, rfl, .refl⟩ .nil

set_option maxHeartbeats 2000000 in
-- Each `set` decides `Signature.IsCtor` through the whole eleven-deep declaration chain, and
-- the last one runs two primitives on top of that.
/-- The five `set`s. The last one is the `@UF` edge, and stepping it is where
`ordering-max`/`ordering-min` are actually run: they pick `(B)` for the key and `(A)` for the
value, which is what makes `uUFE` the row. -/
theorem uSetsStep : ProgramStep uPrelude uEncodedSets uTgt :=
  .cons ⟨uS1, rfl, .refl⟩ (.cons ⟨uS2, rfl, .refl⟩ (.cons ⟨uS3, rfl, .refl⟩
    (.cons ⟨uS4, rfl, .refl⟩ (.cons ⟨uTgt, rfl, .refl⟩ .nil))))

/-- **And the encoded run is reachable up to its rebuild**, which is every command of
`encode uProgram` but the last (`uEncoded_eq`). -/
theorem uProgram_programStep_prefix :
    ProgramStep Database.empty uEncodedPrefix uTgt := uPreludeStep.append uSetsStep

/-- The rule the prelude installed is the encoding of the source rule's query. -/
theorem uEncRule_query_eq : (encodeQuery uSrcRule.query 0).1 = uEncRule.query := rfl

/-- What the encoded query matched under: the view read's two generated columns. The source
query has no variable of its own, so this is all of it. -/
def uSubst : Env := [("@v0", uA), ("@v1", .app fiatName [])]

/-- The one emitted atom matches, at `(A)`'s view row. -/
theorem uTgt_validSubst :
    ValidSubst uTgt (.values [.var "@v0", .var "@v1"] (viewName "A") []) uSubst := by
  refine ⟨⟨List.Perm.refl _, ?_⟩, .values uTgt_mem_viewA rfl rfl (Database.mem_addTerm _ _)⟩
  intro b hb
  simp only [uSubst, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact uTgt_mem_A
  · exact uTgt_mem_fiat

/-- **So the encoded query matches** — `cong_headUnion`'s target-side premise, inhabited at a
state the encoded program reaches. -/
theorem uTgt_validQuerySubst :
    ValidQuerySubst uTgt (encodeQuery uSrcRule.query 0).1 uSubst :=
  ⟨[uSubst], .cons uTgt_validSubst .nil, .single _⟩

theorem uSrcRule_noValues : ∀ p ∈ uSrcRule.query, p.NoValues := by
  intro p hp
  obtain rfl : p = .expr (.app "A" []) := by simpa [uSrcRule] using hp
  trivial

theorem uSrcRule_grounded : ∀ p ∈ uSrcRule.query, p.Grounded := by
  intro p hp
  obtain rfl : p = .expr (.app "A" []) := by simpa [uSrcRule] using hp
  intro l
  simp

/-- Vacuously — the query has no variable. `Query.VarsKeyed` is exercised non-vacuously at
`wProgram`; what this program is for is the *head*. -/
theorem uSrcRule_varsKeyed : Query.VarsKeyed uSrcRule.query := by
  intro v hv
  simp [uSrcRule, Query.vars, Pattern.vars, Expr.vars, Expr.varsList] at hv

/-- **And the program is inside the encoder's declared domain.** A `union` in a rule head is
`Action.NoSet`, and the query's one pattern is neither a bare literal nor a bare variable. -/
theorem uProgram_encodeDomain : uProgram.EncodeDomain where
  ctorsOnly := by
    intro c hc
    simp only [uProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h <;> simp_all [Cmd.CtorDecl, wADecl]
  setLegal := by decide
  noPrim := by decide
  -- `String.isPrefixOf` does not reduce under `decide`'s evaluator; the kernel's does.
  noAt := by decide +kernel
  queryEncodable := by
    intro c hc
    simp only [uProgram, List.mem_cons] at hc
    rcases hc with rfl | rfl | rfl | rfl | h
    · trivial
    · trivial
    · exact ⟨fun p hp => ⟨uSrcRule_grounded p hp, uSrcRule_noValues p hp⟩, uSrcRule_varsKeyed⟩
    · trivial
    · exact absurd h (by simp)
  noLitUnion := Or.inr (by decide)
  headsDeclared := by decide
  aritiesAgree := by decide
  headsScoped := by decide

/-- **`cong_headUnion` at a non-reflexive equation.**

Every hypothesis discharged at the reachable pair, and the conclusion is `Cong` between two
terms that are *not* equal — which is what `cong_headUnion_witness` cannot check and what the
lemma exists for. `hfired` is the source's own assertion of the pair (`uSrcD_mem_eq`), and
both operands' naming expressions are the operands themselves (`encodeBuild_fst`), evaluated
in the target at the substitution the encoded query matched under.

`ho` is taken at `Or.inl`, so the conclusion is the edge in the orientation `(A) = (B)`;
`Or.inr` gives the other, which is what `ordering-max` leaves open. -/
theorem cong_headUnion_union_witness :
    uProgram.EncodeDomain ∧ ProgramStep Database.empty uProgram uSrcD ∧
      ProgramStep Database.empty uEncodedPrefix uTgt ∧
      ¬ uSrcD.Diag ∧ uA ≠ uB ∧ Cong uSrcD uA uB := by
  refine ⟨uProgram_encodeDomain, uProgramStep_src, uProgram_programStep_prefix,
    uSrcD_not_diag, uA_ne_uB, ?_⟩
  refine cong_headUnion (q := uSrcRule.query) (n := 0) (m₁ := 0) (m₂ := 0)
    uSrcD_termsBuild uTgt_viewsSound uTgt_diag uTgt_subtermClosed
    (by simp [Database.GlobalsAgree, uSrcD, uSrcBase, Database.empty])
    uSrcRule_noValues uSrcRule_grounded uSrcRule_varsKeyed uTgt_validQuerySubst
    (e₁ := .app "A" []) (e₂ := .app "B" []) (t₁ := uA) (t₂ := uB)
    (fun g hg _ => ?_) (fun v hv => ?_) rfl rfl
    (fun _ _ _ _ => uSrcD_mem_eq) (Or.inl ⟨rfl, rfl⟩)
  · have hg' : g = "A" ∨ g = "B" := by
      simpa [Expr.fns, Expr.fnsList] using hg
    rcases hg' with rfl | rfl <;>
      exact ⟨wADecl, by simp [uSrcD, uSrcBase, uSrcSig], rfl⟩
  · simp [Expr.vars, Expr.varsList] at hv

/-! #### What the rebuild is for, at the state that needs it

`Database.UnionsRead` — obligation `assert`'s `union` half — is **false** at `uTgt`, and
`Database.ViewLeader.ufClosed` is exactly what fails there: the `@UF` edge is written and
nothing has followed it, so `(A)` reads only `(A)` and `(B)` reads only `(B)`, which leaves the
edge's two ends no common `lead`. `Database.UnionsJoined` — the `union`'s own write, at ids —
holds on both sides of the firing. One firing of `uRebuildB` repairs the rest, and the two
states either side of it are what say the two properties are load-bearing separately rather
than decoration. -/

/-- **What `uTgt` reads a source term as**: itself, and nothing else. Stated at an application
because `uA` and `uB` are the two source terms and both are; a literal's id is the literal
(`ViewRepr.eq_of_lit`), which is neither. -/
private theorem uTgt_viewRepr {g : FnName} {bs : List Term} {e : Term}
    (h : ViewRepr uTgt (.app g bs) e) :
    (Term.app g bs = uA ∧ e = uA) ∨ (Term.app g bs = uB ∧ e = uB) := by
  match h with
  | @ViewRepr.app _ f as es e pf hl ho =>
    rcases uTgt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain rfl : as = [] := by cases hl with | nil => rfl
      exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl : as = [] := by cases hl with | nil => rfl
      exact Or.inr ⟨rfl, rfl⟩

/-- **`Database.UnionsRead` fails at `uTgt`.** The equation `(A) = (B)` is asserted by the
source and the two terms share no id here: the `@UF` edge is present and unfollowed, so this
is the obligation the rebuild — and nothing else — discharges. -/
theorem uTgt_not_unionsRead : ¬ uTgt.UnionsRead uSrcD := by
  intro h
  obtain ⟨e, h₁, h₂⟩ := h uA uB uSrcD_mem_eq uA_ne_uB
  rcases uTgt_viewRepr h₁ with ⟨-, h₁'⟩ | ⟨h₁', -⟩
  · rcases uTgt_viewRepr h₂ with ⟨h₂', -⟩ | ⟨-, h₂'⟩
    · exact uA_ne_uB h₂'.symm
    · exact uA_ne_uB (h₁'.symm.trans h₂')
  · exact uA_ne_uB h₁' 

/-- `(@Trans @Fiat @Fiat)`: the row's own proof composed with the edge's. -/
def uTransE : Term := .app transName [.app fiatName [], .app fiatName []]

/-- `@BView() ↦ (A, @Trans @Fiat @Fiat)`, the row `uRebuildB` writes at `uTgt`. -/
def uBView2E : Term := .app (viewName "B") [uA, uTransE]

/-- **`uTgt` plus that one row.** Not a state `ProgramStep` reaches — the command that would
reach it is the `Cmd.saturate` no state satisfies — but the row is exactly the one the
rebuild rule fires and writes there (`uRebuilt_mem_ruleResults`). -/
def uRebuilt : Database := uTgt.addTerm uBView2E

theorem uRebuilt_diag : uRebuilt.Diag := uTgt_diag.addTerm _

/-- The two terms the firing adds, and everything else is `uTgt`'s. -/
private theorem uRebuilt_mem_cases {t : Term} (h : t ∈ uRebuilt.terms) :
    t = uBView2E ∨ t = uTransE ∨ t ∈ uTgt.terms := by
  rw [uRebuilt, Database.addTerm_terms] at h
  rcases h with h | h
  · exact Or.inr (Or.inr h)
  · have h' : t = uBView2E ∨ t = uTransE ∨ t = Term.app fiatName [] ∨ t = uA := by
      simpa [uBView2E, uTransE, uA] using h
    rcases h' with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr uTgt_mem_fiat)
    · exact Or.inr (Or.inr uTgt_mem_A)

/-- **The three view rows `uRebuilt` holds.** `(B)`'s key now carries two e-classes, which is
the "view tables are not functional" phenomenon appearing here for the first time in a state
this file steps to. -/
private theorem uRebuilt_out_view {f : FnName} {cs : List Term} {e pf : Term}
    (ho : uRebuilt.Out (viewName f) cs [e, pf]) :
    (f = "A" ∧ cs = [] ∧ e = uA) ∨ (f = "B" ∧ cs = [] ∧ (e = uB ∨ e = uA)) := by
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : cs = bs :=
    List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag uRebuilt_diag h)
  rcases uRebuilt_mem_cases hmem with h' | h' | h'
  · simp only [uBView2E, Term.app.injEq] at h'
    refine Or.inr ⟨viewName_inj h'.1, ?_⟩
    obtain rfl : cs = [] := by
      have hl : (cs ++ [e, pf]).length = 2 := by rw [h'.2]; rfl
      simp only [List.length_append, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨rfl, Or.inr (show e = uA ∧ pf = uTransE by simpa using h'.2).1⟩
  · simp only [uTransE, Term.app.injEq] at h'
    exact absurd h'.1 viewName_ne_transName
  · exact (uTgt_mem_view h').imp (fun h => h) fun h => ⟨h.1, h.2.1, Or.inl h.2.2⟩

/-- **And the one `@UF` row**, which is the only three-column term either state holds. -/
private theorem uRebuilt_out_uf {t p pf : Term} (ho : uRebuilt.Out ufName [t] [p, pf]) :
    t = uB ∧ p = uA := by
  obtain ⟨bs, hcl, hmem⟩ := ho
  obtain rfl : [t] = bs :=
    List.forall₂_eq_eq_eq ▸ (hcl.toForall₂.imp fun _ _ h => Cong.eq_of_diag uRebuilt_diag h)
  rcases uRebuilt_mem_cases hmem with h' | h' | h'
  · simp only [uBView2E, Term.app.injEq] at h'
    exact absurd h'.1.symm viewName_ne_ufName
  · simp [uTransE] at h'
  · rcases uTgt_mem_cases h' with h'' | h'' | h'' | h'' | h'' | h'' | h'' | h'' <;>
      simp_all [uUFE, uBViewE, uBTermE, uAViewE, uATermE, uA, uB, ufName, viewName, termName,
        fiatName]

/-- **`Database.ViewsSound` survives the rebuild's re-keying**, and here it needs the source's
*non-reflexive* congruence for the first time: the row `uRebuildB` wrote claims that `(B)`'s
view holds `(A)`, which is `EntrySound` at `Cong uSrcD (B) (A)` — the `union`'s own equation,
symmetrised. Every earlier witness discharged `EntrySound` at a reflexive `Cong`. -/
theorem uRebuilt_viewsSound : uRebuilt.ViewsSound uSrcD := by
  intro f cs e pf ho
  rcases uRebuilt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, (rfl | rfl)⟩
  · exact entrySound_build uSrcD_wf uSrcD_mem_A
  · exact entrySound_build uSrcD_wf uSrcD_mem_B
  · exact ⟨[], uSrcD_mem_B, .nil, (Cong.assert uSrcD_mem_eq).symm⟩

theorem uRebuilt_mem_viewA : uAViewE ∈ uRebuilt.terms := by
  rw [uRebuilt, Database.addTerm_terms]; exact Or.inl uTgt_mem_viewA

theorem uRebuilt_mem_viewB : uBViewE ∈ uRebuilt.terms := by
  rw [uRebuilt, Database.addTerm_terms]; exact Or.inl uTgt_mem_viewB

theorem uRebuilt_mem_uf : uUFE ∈ uRebuilt.terms := by
  rw [uRebuilt, Database.addTerm_terms]; exact Or.inl uTgt_mem_uf

theorem uRebuilt_mem_B : uB ∈ uRebuilt.terms := by
  rw [uRebuilt, Database.addTerm_terms]; exact Or.inl uTgt_mem_B

/-- **Every equation `uSrcD` asserts is the `union`'s pair or reflexive**: `Database.addTerm`
writes only the diagonal, and `Database.addEq` writes the one pair on top of it. -/
private theorem uSrcD_eq_or_diag {a b : Term} (hab : (a, b) ∈ uSrcD.eqs) :
    ((a, b) = (uA, uB)) ∨ a = b := by
  rw [uSrcD, Database.addEq_eqs] at hab
  rcases hab with h | h
  · exact Or.inl h
  · have hd : uSrcBase.Diag := fun p hp => absurd hp (by simp [uSrcBase, Database.empty])
    exact Or.inr (((hd.addTerm uA).addTerm uB) (a, b) h)

/-- **`Database.UnionsJoined` holds at `uRebuilt`, non-vacuously**: the source's one
non-reflexive equation, the two endpoints' own build rows as their ids, and the `@UF` row the
encoded `union` wrote between them — keyed at `ordering-max` and so in the `Or.inr` orientation.

The clause reads *ids* and not the endpoints themselves, so this witness answers with the ids
`(A)` and `(B)`; where the two come apart is a rule head's `union` at a non-leader
substitution, which `Encoding/Correspond.lean`'s `ncProgram` is the state for. -/
theorem uRebuilt_unionsJoined : uRebuilt.UnionsJoined uSrcD := by
  intro a b hab hne
  rcases uSrcD_eq_or_diag hab with h | h
  · obtain ⟨rfl, rfl⟩ : a = uA ∧ b = uB := by simpa using h
    exact ⟨uA, uB, Term.app fiatName [],
      .app .nil ⟨[], .nil, uRebuilt_mem_viewA⟩, .app .nil ⟨[], .nil, uRebuilt_mem_viewB⟩,
      Or.inr ⟨[uB], .cons uRebuilt_mem_B .nil, uRebuilt_mem_uf⟩⟩
  · exact absurd h hne

/-- **What `uRebuilt` reads a source term as**, after the rebuild's one firing: `(A)` still
only `(A)`, and `(B)` now `(B)` *or* `(A)` — the row that firing wrote. -/
private theorem uRebuilt_viewRepr {g : FnName} {bs : List Term} {e : Term}
    (h : ViewRepr uRebuilt (.app g bs) e) :
    (Term.app g bs = uA ∧ e = uA) ∨ (Term.app g bs = uB ∧ (e = uB ∨ e = uA)) := by
  match h with
  | @ViewRepr.app _ f as es e pf hl ho =>
    rcases uRebuilt_out_view ho with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, hE⟩
    · obtain rfl : as = [] := by cases hl with | nil => rfl
      exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl : as = [] := by cases hl with | nil => rfl
      exact Or.inr ⟨rfl, hE⟩

/-- The union-find representative at `uRebuilt`: `(B)`'s class is `(A)`'s and nothing else
moves. -/
def uLead (t : Term) : Term := if t = uB then uA else t

theorem uLead_uA : uLead uA = uA := by simp [uLead, uA, uB]

theorem uLead_uB : uLead uB = uA := by simp [uLead]

theorem uLead_lit (l : Lit) : uLead (.lit l) = .lit l := by simp [uLead, uB]

/-- **`Database.ViewLeaderRows` holds at `uRebuilt`, with three of its four clauses doing
work.** Two ids, an edge between them, and a term that reads both — which is what the
degenerate witness (`satTarget_viewLeaderRows`: the identity `lead`, and no `@UF` row at all)
cannot exhibit.

* the first clause is asked at `(B)`, which reads `(B)` and whose `lead` is `(A)`: the row
  `uRebuildB` wrote is what answers it;
* the second at `(B)`'s two ids, which is the only term in the tree with two;
* `ufClosed` at the one `@UF` row, whose ends are `(B)` and `(A)`.
* `rowLead` is the one that is degenerate here, and `uRebuilt_out_view` is why: both source
  terms are nullary, so every key is the empty tuple and `lead` moves it nowhere.
  `Encoding/Correspond.lean`'s `ncTgt_viewLeaderRows` is that clause at positive arity, where
  the key the `union` moved is `((B))` and the row sits at `((A))`.

`uTgt_not_viewLeader` is the first three one firing earlier, where they fail. -/
theorem uRebuilt_viewLeaderRows : uRebuilt.ViewLeaderRows := by
  have hAA : ViewRepr uRebuilt uA uA := .app .nil ⟨[], .nil, uRebuilt_mem_viewA⟩
  have hBA : ViewRepr uRebuilt uB uA := .app .nil ⟨[], .nil, Database.mem_addTerm _ _⟩
  refine ⟨uLead, ?_, ?_, ?_, ?_⟩
  · intro t e h
    cases t with
    | lit l => rw [h.eq_of_lit, uLead_lit]; exact .lit
    | app g bs =>
      rcases uRebuilt_viewRepr h with ⟨ht, rfl⟩ | ⟨ht, (rfl | rfl)⟩
      · rw [ht, uLead_uA]; exact hAA
      · rw [ht, uLead_uB]; exact hBA
      · rw [ht, uLead_uA]; exact hBA
  · intro t e₁ e₂ h₁ h₂
    cases t with
    | lit l => rw [h₁.eq_of_lit, h₂.eq_of_lit]
    | app g bs =>
      rcases uRebuilt_viewRepr h₁ with ⟨-, rfl⟩ | ⟨-, (rfl | rfl)⟩ <;>
          rcases uRebuilt_viewRepr h₂ with ⟨-, rfl⟩ | ⟨-, (rfl | rfl)⟩ <;>
        simp [uLead_uA, uLead_uB]
  · intro x y pf ho
    obtain ⟨rfl, rfl⟩ := uRebuilt_out_uf ho
    rw [uLead_uB, uLead_uA]
  · intro f es e pf ho
    rcases uRebuilt_out_view ho with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;>
      exact ⟨e, pf, by simpa using ho⟩

@[inherit_doc uRebuilt_viewLeaderRows]
theorem uRebuilt_viewLeader : uRebuilt.ViewLeader := uRebuilt_viewLeaderRows.toViewLeader

/-- **And `Database.ViewJoined` holds here**, out of the reduction: the weakened form of the
four clauses above, at the state with the real `@UF` edge. `uRebuilt_ufJoin_BA` and
`uRebuilt_ids_B` are its two interesting clauses at named instances, and `uTgt_not_viewJoined`
is `ufJoin` failing one firing earlier — so the weakening still needs the rebuild. -/
theorem uRebuilt_viewJoined : uRebuilt.ViewJoined := uRebuilt_viewLeaderRows.toViewJoined

/-- **`Database.ViewJoined.ufJoin` at a real `@UF` edge**: the `union`'s own write runs between
two *distinct* terms and the absorber is `(A)`, which the rebuild's one firing put in `(B)`'s
reading. Every hypothesis is inhabited and the two ends are not equal, so the clause is not
answered by reflexivity. -/
theorem uRebuilt_ufJoin_BA :
    uRebuilt.Out ufName [uB] [uA, Term.app fiatName []] ∧ uB ≠ uA ∧
      ∃ e, uRebuilt.Absorbs uB e ∧ uRebuilt.Absorbs uA e :=
  ⟨⟨[uB], .cons uRebuilt_mem_B .nil, uRebuilt_mem_uf⟩, fun h => uA_ne_uB h.symm,
   uRebuilt_viewJoined.ufJoin uB uA (Term.app fiatName [])
     ⟨[uB], .cons uRebuilt_mem_B .nil, uRebuilt_mem_uf⟩⟩

/-- **`Database.ViewJoined.ids` at the one term with two ids**: `(B)` reads its own build entry
and the leader's, and they are distinct — which is the instance the degenerate witness
`satTarget_viewJoined` cannot exhibit. -/
theorem uRebuilt_ids_B :
    ViewRepr uRebuilt uB uB ∧ ViewRepr uRebuilt uB uA ∧ uB ≠ uA ∧
      ∃ e, uRebuilt.Absorbs uB e ∧ uRebuilt.Absorbs uA e :=
  ⟨.app .nil ⟨[], .nil, uRebuilt_mem_viewB⟩, .app .nil ⟨[], .nil, Database.mem_addTerm _ _⟩,
   fun h => uA_ne_uB h.symm,
   uRebuilt_viewJoined.ids uB uB uA (.app .nil ⟨[], .nil, uRebuilt_mem_viewB⟩)
     (.app .nil ⟨[], .nil, Database.mem_addTerm _ _⟩)⟩

/-- **`Database.RebuildClosedStrong` at `uRebuilt`, with two of its three clauses doing work**,
and `Database.RebuildClosed.of_strong` carrying it to the residue's own form.

`eclass` at the one `@UF` edge: `(A)` is read by `(B)`, which is what the rebuild's single
firing put there. `edged` at the one term with two ids, joined by that same edge — the clause
that `Database.ViewLeaderRows` has no counterpart for, which is why this is proved from the
definition and not through `Database.ViewLeaderRows.toViewJoined`. `column` is degenerate for
the reason `rowLead` is: both source terms are nullary, so every key is the empty tuple and
there is no column to move.

`Encoding/Correspond.lean`'s `satTarget_rebuildClosedStrong` is the state with no edge at all,
`uTgt_not_rebuildClosed` is this one firing earlier, and `cxStale_not_rebuildClosedStrong` is
the state where `eclass` separates the two forms — a superseded edge, which this one is not. -/
theorem uRebuilt_rebuildClosedStrong : uRebuilt.RebuildClosedStrong := by
  have hstep : uRebuilt.UFStep uB uA :=
    ⟨Term.app fiatName [], ⟨[uB], .cons uRebuilt_mem_B .nil, uRebuilt_mem_uf⟩⟩
  have hBA : ViewRepr uRebuilt uB uA := .app .nil ⟨[], .nil, Database.mem_addTerm _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro a b ⟨pf, ho⟩
    obtain ⟨rfl, rfl⟩ := uRebuilt_out_uf ho
    intro t ht
    cases t with
    | lit l => exact absurd ht.eq_of_lit (by simp [uB])
    | app g bs =>
        rcases uRebuilt_viewRepr ht with ⟨-, h'⟩ | ⟨h', -⟩
        · exact absurd h'.symm uA_ne_uB
        · rw [h']; exact hBA
  · intro t e₁ e₂ h₁ h₂
    cases t with
    | lit l =>
        refine ⟨e₁, .refl, ?_⟩
        rw [h₂.eq_of_lit, h₁.eq_of_lit]
        exact .refl
    | app g bs =>
        refine ⟨uA, ?_, ?_⟩
        · rcases uRebuilt_viewRepr h₁ with ⟨-, rfl⟩ | ⟨-, (rfl | rfl)⟩
          exacts [.refl, hstep.toReach, .refl]
        · rcases uRebuilt_viewRepr h₂ with ⟨-, rfl⟩ | ⟨-, (rfl | rfl)⟩
          exacts [.refl, hstep.toReach, .refl]
  · intro f es ds e pf ho hl
    rcases uRebuilt_out_view ho with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;>
      (cases hl; exact ⟨e, pf, ho⟩)

/-- **And every chain terminates at `uRebuilt` in at most one step**: the `union`'s edge is the
only one the state records, and `(A)` is where it stops. This is the hypothesis
`Database.RebuildClosed.of_strong_ufRoot` adds over `Database.RebuildClosed.of_strong`, and it
is what names the point the rooted `edged` clause answers with. -/
theorem uRebuilt_exists_ufRoot (a : Term) :
    ∃ r, uRebuilt.UFReach a r ∧ uRebuilt.UFRoot r := by
  have hno : ∀ x b, x ≠ uB → ¬ uRebuilt.UFStep x b := by
    rintro x b hx ⟨pf, ho⟩
    exact hx (uRebuilt_out_uf ho).1
  by_cases h : a = uB
  · subst h
    have hstep : uRebuilt.UFStep uB uA :=
      ⟨Term.app fiatName [], ⟨[uB], .cons uRebuilt_mem_B .nil, uRebuilt_mem_uf⟩⟩
    exact ⟨uA, hstep.toReach, fun b => hno uA b uA_ne_uB⟩
  · exact ⟨a, .refl, fun b => hno a b h⟩

@[inherit_doc uRebuilt_rebuildClosedStrong]
theorem uRebuilt_rebuildClosed : uRebuilt.RebuildClosed uRebuilt.UFRoot :=
  Database.RebuildClosed.of_strong_ufRoot uRebuilt_rebuildClosedStrong uRebuilt_exists_ufRoot

/-- **And `Database.ViewLeader` fails at `uTgt`**, which is where `Database.UnionsRead` fails
too: the edge is written and unfollowed, so `(A)`'s only `lead` is `(A)` and `(B)`'s is `(B)`,
and `ufClosed` asks the two to be equal. This is the clause the rebuild discharges, isolated
from the `union`'s own write — which holds on both sides of the firing. -/
theorem uTgt_not_viewLeader : ¬ uTgt.ViewLeader := by
  rintro ⟨lead, hmem, -, huf⟩
  have hA : ViewRepr uTgt uA uA := .app .nil ⟨[], .nil, uTgt_mem_viewA⟩
  have hB : ViewRepr uTgt uB uB := .app .nil ⟨[], .nil, uTgt_mem_viewB⟩
  have hlA : lead uA = uA := by
    rcases uTgt_viewRepr (hmem uA uA hA) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h uA_ne_uB
  have hlB : lead uB = uB := by
    rcases uTgt_viewRepr (hmem uB uB hB) with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm uA_ne_uB
    · exact h
  exact uA_ne_uB ((hlB.symm.trans (huf uB uA (Term.app fiatName [])
    ⟨[uB], .cons uTgt_mem_B .nil, uTgt_mem_uf⟩)).trans hlA).symm

/-- **And so does the weakened form**, which is what says the weakening is not into vacuity:
`Database.ViewJoined.ufJoin` asks only for a common *absorber* of the edge's two ends, and one
firing before the rebuild there is none. `(A)` reads only `(A)` and `(B)` only `(B)`, so an
absorber of `(A)` is `(A)` — read off the clause at `(A)` itself — and an absorber of `(B)` is
`(B)`. The e-class rebuild rule is therefore still the whole content of the clause after the
weakening, and it is `pathCompressRule` and nothing else that dropped out. -/
theorem uTgt_not_viewJoined : ¬ uTgt.ViewJoined := by
  intro h
  have hA : ViewRepr uTgt uA uA := .app .nil ⟨[], .nil, uTgt_mem_viewA⟩
  have hB : ViewRepr uTgt uB uB := .app .nil ⟨[], .nil, uTgt_mem_viewB⟩
  obtain ⟨e, kA, kB⟩ := h.ufJoin uB uA (Term.app fiatName [])
    ⟨[uB], .cons uTgt_mem_B .nil, uTgt_mem_uf⟩
  have heB : e = uB := by
    rcases uTgt_viewRepr (kA uB hB) with ⟨h', -⟩ | ⟨-, h'⟩
    · exact absurd h'.symm uA_ne_uB
    · exact h'
  have heA : e = uA := by
    rcases uTgt_viewRepr (kB uA hA) with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h'
    · exact absurd h' uA_ne_uB
  exact uA_ne_uB (heA.symm.trans heB)

/-- **And so does `Database.RebuildClosed`**, through the reduction: `eclass` at the edge the
`union` wrote is exactly the firing that has not happened yet, and `Database.ViewJoined.ufJoin`
is that clause with the absorber read off the edge's far end. This is the check that the
per-rule restatement of the residue is not vacuous either — one rebuild firing later
`uRebuilt_rebuildClosed` holds, and here it cannot. -/
theorem uTgt_not_rebuildClosed {Rooted : Term → Prop} : ¬ uTgt.RebuildClosed Rooted :=
  fun h => uTgt_not_viewJoined h.toViewJoined

/-- **And so does the strong form**, through the weakening: `Database.RebuildClosed.of_strong`
is the reduction, so the state that refutes the weak clause refutes the strong one too. This
is what keeps `Database.RebuildClosedStrong` on record as a *strengthening* — it is refuted
here for the reason the weak form is, one rebuild firing early, and separately at an `execM`
target for a reason the weak form survives (`execM_rebuildClosed`). -/
theorem uTgt_not_rebuildClosedStrong : ¬ uTgt.RebuildClosedStrong :=
  fun h => uTgt_not_rebuildClosed (Database.RebuildClosed.of_strong h)

/-- **`Database.ViewsCover` holds at `uRebuilt` too**, so all three of the forward half's
properties are discharged at one state, and at the state with the `union` rather than at the
degenerate one. Both source terms are nullary, so the shared tuple is the empty one and the
clause is the two build rows; `ncTgt_shared_FB` is the same clause at positive arity, where the
tuple it answers with is not the one handed in. -/
theorem uRebuilt_viewsCover : uRebuilt.ViewsCover uSrcD where
  shared := by
    intro f as bs ht hl
    rcases uSrcD_mem_cases ht with h | h <;>
        (simp only [uA, uB, Term.app.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;> cases hl
    · exact ⟨[], _, _, .nil, .nil, ⟨[], .nil, uRebuilt_mem_viewA⟩⟩
    · exact ⟨[], _, _, .nil, .nil, ⟨[], .nil, uRebuilt_mem_viewB⟩⟩

/-- **So `Database.UnionsRead` holds at `uRebuilt`**, through the reduction — which is
therefore exercised at a state with a real edge and a non-diagonal source, not only at the
diagonal. -/
theorem uRebuilt_unionsRead : uRebuilt.UnionsRead uSrcD :=
  unionsRead_of_unionsJoined uRebuilt_viewLeader uRebuilt_unionsJoined

/-- **And the forward half's whole argument runs there**: `cong_sameClass_of_state` at the three
properties above, over a source that derives an equation between *distinct* terms. Nothing in
this is vacuous — the hypothesis is the `union`'s own equation and the conclusion is an id the
rebuild's firing put in both readings. -/
theorem uRebuilt_cong_sameClass : Cong uSrcD uA uB ∧ SameClass uRebuilt uA uB :=
  ⟨Cong.assert uSrcD_mem_eq,
   cong_sameClass_of_state uSrcD_wf uRebuilt_viewLeader uRebuilt_viewsCover
     uRebuilt_unionsRead (Cong.assert uSrcD_mem_eq)⟩

/-- **And its conclusion is inhabited there**: the two endpoints share the id `(A)`. -/
theorem uRebuilt_sameClass : SameClass uRebuilt uA uB :=
  uRebuilt_unionsRead uA uB uSrcD_mem_eq uA_ne_uB

/-! #### And the row is the rebuild's own

`uRebuilt` is `uTgt` plus one row, and this is what says which row: the e-class rebuild rule
for `B`, at the substitution `uTgt`'s two rows admit, evaluates to exactly it. So the witness
above is not a hand-picked state — it is one firing of `encode`'s own maintenance rule, and
`uRebuilt_contained_runRules` places it inside the round `Cmd.saturate rebuildRuleset` starts
with. -/

/-- What the view atom of `uRebuildB` binds: `(B)`'s row. -/
def uRSubst1 : Env := [("@e", uB), ("@p", .app fiatName [])]

/-- And what its `@UF` atom binds. `@e` is bound here too — the atom's key is `.var "@e"`,
which `Pattern.freeVars` counts as free at an empty environment. -/
def uRSubst2 : Env := [("@x", uA), ("@q", .app fiatName []), ("@e", uB)]

@[inherit_doc uRSubst1] def uRSubst : Env := uRSubst1 ++ uRSubst2

theorem uTgt_validSubst_view :
    ValidSubst uTgt (.values [.var "@e", .var "@p"] (viewName "B") []) uRSubst1 := by
  refine ⟨⟨List.Perm.refl _, ?_⟩, .values uTgt_mem_viewB rfl rfl (Database.mem_addTerm _ _)⟩
  intro b hb
  simp only [uRSubst1, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact uTgt_mem_B
  · exact uTgt_mem_fiat

theorem uTgt_validSubst_uf :
    ValidSubst uTgt (.values [.var "@x", .var "@q"] ufName [.var "@e"]) uRSubst2 := by
  refine ⟨⟨List.Perm.refl _, ?_⟩, .values uTgt_mem_uf rfl rfl (Database.mem_addTerm _ _)⟩
  intro b hb
  simp only [uRSubst2, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact uTgt_mem_A
  · exact uTgt_mem_fiat
  · exact uTgt_mem_B

/-- **The rebuild rule's query matches at `uTgt`**, the two atoms joined on `@e`. -/
theorem uTgt_validQuerySubst_rebuild : ValidQuerySubst uTgt uRebuildB.query uRSubst :=
  ⟨[uRSubst1, uRSubst2], .cons uTgt_validSubst_view (.cons uTgt_validSubst_uf .nil),
    .step ⟨by
      intro b hb t ht
      simp only [uRSubst1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Option.some.inj ht
      · exact absurd ht (by simp [uRSubst2, Env.lookup]), rfl⟩ (.single _)⟩

/-- **And its head writes `uBView2E`.** The e-class column moves to `(A)`, the `@UF` edge's
target, and the proof column is the row's own composed with the edge's. -/
theorem uRebuilt_evalLocalActions :
    evalLocalActions uTgt uRebuildB.actions uRSubst = some uRebuilt := rfl

/-- The rule is one of the four the prelude installed. -/
theorem uRebuildB_mem_rules : uRebuildB ∈ uTgt.rules := by
  rw [uTgt_rules]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

@[inherit_doc uRebuilt_evalLocalActions]
theorem uRebuilt_mem_ruleResults : uRebuilt ∈ RuleResults uTgt uRebuildB :=
  ⟨uRSubst, uTgt_validQuerySubst_rebuild, uRebuilt_evalLocalActions⟩

/-- **So `uRebuilt` is inside the first round of the rebuild ruleset at `uTgt`.** Not the
whole round — `RunRules` unions every firing of every rule — but the part `Database.UnionsRead`
needs, which is what makes the witness above a state the rebuild is *going* to. -/
theorem uRebuilt_contained_runRules :
    uRebuilt.Contained (RunRules rebuildRuleset uTgt) :=
  Database.Contained.mem_sUnion
    (show uRebuilt ∈ {d | ∃ r ∈ uTgt.rules, r.ruleset = rebuildRuleset ∧
      d ∈ RuleResults uTgt r} from ⟨uRebuildB, uRebuildB_mem_rules, rfl,
        uRebuilt_mem_ruleResults⟩)

/-! ### The finding: the rebuild after a `union` has no fixpoint

`satProgram_programStep` says `ProgramStep Database.empty (encode P) tgt` is satisfiable, and
it is — at a `P` that only *builds*. As soon as `P` asserts an equation between distinct
terms it is not, and the reason is the proof tower `Encoding/Encode.lean`'s `Rebuilt`
docstring describes for a *self*-collision, which `identityVals := some 1` disarms. A
collision the e-class rebuild rule creates is not a self-collision, and nothing disarms it:

1. The `union` writes `@UF(B) ↦ (A, @Fiat)`, keyed at `ordering-max`, which is the e-class
   column of `(B)`'s own view row.
2. `uRebuildB` re-keys that row to `@BView() ↦ (A, @Trans @Fiat @Fiat)`, and the row it
   displaced **stays** — nothing is ever removed from `terms`.
3. The two rows now collide at one key with different *counted* columns, so `MergeConflict`
   holds and `mergeBody` writes `@UF(B) ↦ (A, @Trans (@Sym @Fiat) (@Trans @Fiat q))` — one
   composition larger than the `q` it started from.
4. And that new edge feeds step 2 again, through the *stale* row, forever.

`uf_row_succ` is one turn of that crank, stated at any state where the rebuild ruleset has
saturated; `uTgt_saturate_infinite` iterates it. So the specification can only reach a state
holding infinitely many terms, which is what `Cmd.saturate`'s divergence looks like in a
fixpoint semantics — `Spec/Syntax.lean`'s `Cmd.NoSaturate` names exactly this failure mode
("a ruleset that keeps adding terms has no fixpoint"). This is why the run above stops at
`uEncodedPrefix`, and it is a property of `encode` and the specification's monotone `terms`,
not of this program: any source `union` between two distinct built terms puts the edge of
step 1 on a view e-class, because `encodeBuild` gives every built application a view row
whose e-class column is the application itself. -/

/-- `@UF(B) ↦ (A, q)`: the union-find row at `(B)`, carrying the proof `q`. -/
def uUFRow (q : Term) : Term := .app ufName [uB, uA, q]

theorem uUFRow_fiat : uUFRow (.app fiatName []) = uUFE := rfl

/-- What one turn of the tower does to that proof: `@Trans (@Sym @Fiat) (@Trans @Fiat q)`,
which is `mergeBody`'s `@Trans (@Sym hi_pf) lo_pf` at the two colliding rows. -/
def uStepPf (q : Term) : Term :=
  .app transName [.app symName [.app fiatName []], .app transName [.app fiatName [], q]]

/-- **One turn of the crank.** At any state where the rebuild ruleset has saturated, which is
what `Cmd.saturate rebuildRuleset` demands: `uRebuildB` fires against the stale row and the
merge phase settles the collision it makes, and the settlement is a strictly larger `@UF` row
at the same key and the same parent.

Every hypothesis is a fact about `uTgt` that a saturating run preserves — its signature, its
empty environment, its rules, and the rows — so `uTgt_saturate_infinite` is this iterated.
`identityVals := some 1` is what makes the *new* `@UF` row no further conflict, and it is
exactly what does not stop this one: the counted column moves from `(B)` to `(A)`. -/
theorem uf_row_succ {d : Database} (hrun : RunRules rebuildRuleset d = d)
    (hmerge : MergeSaturated d) (henv : d.env = []) (hsig : d.sig = uSig)
    (hrule : uRebuildB ∈ d.rules) (hstale : uBViewE ∈ d.terms) (hA : uA ∈ d.terms)
    (hB : uB ∈ d.terms) (hfiat : Term.app fiatName [] ∈ d.terms)
    {q : Term} (hq : uUFRow q ∈ d.terms) (hqt : q ∈ d.terms) :
    uUFRow (uStepPf q) ∈ d.terms ∧ uStepPf q ∈ d.terms := by
  obtain ⟨dsig, deqs, denv, drules⟩ := d
  subst henv
  subst hsig
  -- Step 2: the e-class rule fires against the stale row, at the edge carrying `q`.
  have hev : Term.app (viewName "B") [uA, .app transName [.app fiatName [], q]] ∈
      Database.terms ⟨uSig, deqs, [], drules⟩ := by
    have hσ₁ : ValidSubst ⟨uSig, deqs, [], drules⟩
        (.values [.var "@e", .var "@p"] (viewName "B") []) uRSubst1 := by
      refine ⟨⟨List.Perm.refl _, ?_⟩,
        .values (ts := []) (us := [uB, .app fiatName []]) hstale rfl rfl
          (Database.mem_addTerm _ _)⟩
      intro b hb
      simp only [uRSubst1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hB
      · exact hfiat
    have hσ₂ : ValidSubst ⟨uSig, deqs, [], drules⟩
        (.values [.var "@x", .var "@q"] ufName [.var "@e"])
        [("@x", uA), ("@q", q), ("@e", uB)] := by
      refine ⟨⟨List.Perm.refl _, ?_⟩,
        .values (ts := [uB]) (us := [uA, q]) hq rfl rfl (Database.mem_addTerm _ _)⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact hA
      · exact hqt
      · exact hB
    have hc := (runRules_eq_self_iff rebuildRuleset ⟨uSig, deqs, [], drules⟩).mp hrun
      uRebuildB hrule rfl _
      ⟨uRSubst1 ++ [("@x", uA), ("@q", q), ("@e", uB)],
        ⟨[uRSubst1, [("@x", uA), ("@q", q), ("@e", uB)]], .cons hσ₁ (.cons hσ₂ .nil),
          .step ⟨by
            intro b hb t ht
            simp only [uRSubst1, List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl
            · exact Option.some.inj ht
            · exact absurd ht (by simp [Env.lookup]), rfl⟩ (.single _)⟩,
        rfl⟩
    exact Cong.assert (hc.eqs (Or.inr ⟨_, Term.self_mem_subterms _, rfl⟩))
  -- Step 3: the collision the new row makes, settled — and the settlement is the tower.
  obtain ⟨S, hs, hmem⟩ : ∃ S, MergeStep ⟨uSig, deqs, [], drules⟩ S ∧
      ∀ x ∈ (uUFRow (uStepPf q)).subterms, (x, x) ∈ S.eqs :=
    ⟨_, .collide (f := viewName "B") (decl := viewDecl 0) (as := []) (bs := [])
      (a := [uB, .app fiatName []]) (b := [uA, .app transName [.app fiatName [], q]])
      (body := mergeBody) (res := mergeResult) rfl rfl
      (by simp [MergeConflict, FnDecl.unchangedWidth, viewDecl, uA, uB]) rfl rfl hstale hev
      .nil rfl rfl,
      fun x hx => Or.inl (Or.inr ⟨x, hx, rfl⟩)⟩
  obtain rfl := hmerge _ hs
  exact ⟨Cong.assert (hmem _ (Term.self_mem_subterms _)),
    Cong.assert (hmem _ (Term.arg_subterms (by simp) (Term.self_mem_subterms _)))⟩

/-! #### `Cmd.saturate` of the *source* ruleset inherits it, and by a second mechanism

`encodeQueryExpr` emits `.values [freshVar n₁, freshVar (n₁ + 1)] (viewName f) es`, so a read
binds the **proof column** as an output variable, and `ValidSubst.values` asks only that
`Term.app (viewName f) (es ++ [x, pf]) ∈ d.terms`. There is therefore one substitution per
distinct recorded `(e-class, proof)` pair at that key: **a rule's firing count is the number
of proofs at the matched row, not the number of e-node facts it stands for.** The head mints
`@Rule_i` at that argument list, and `@Rule_i p ≠ @Rule_i q` whenever `p ≠ q`, so each of
those firings writes a term the state lacked.

So wherever the proof set at a matched view row is unbounded — which is what
`uTgt_saturate_tower` produces — `RunRules` over the *source* ruleset has no fixpoint either,
and normalising proof terms cannot reach it: a normal form is still one term per reduced
proof, and no law relates `@Rule_i p` to `@Rule_i q`.

**It compounds the tower rather than standing on its own, and that is worth being exact
about.** The multiplicity is structural and holds at every state. The unboundedness is not: a
view key gains a second output pair only when two rows collide there, `encodeBuild` writes
every view row as the key's own application under `fiatE`, and so nothing but the re-keying
rules above ever creates a view collision. With those rules withheld the source ruleset does
reach a fixpoint. Hence no compiled witness here: the unconditional statement is false, and
the conditional one adds nothing to `uf_row_succ`. -/

/-- Rounds of a ruleset move neither the environment nor the rules: `RunRules` is a
`Database.sUnion`, which takes both from its argument, and `MergeStep` restores both. -/
theorem runReach_envRules {R : RulesetName} {db d : Database}
    (h : Relation.ReflTransGen (RunStep R) db d) : d.env = db.env ∧ d.rules = db.rules := by
  refine RunReach.induction (P := fun x => x.env = db.env ∧ x.rules = db.rules)
    (fun x x' hp hstep => ?_) h ⟨rfl, rfl⟩
  obtain ⟨he, hr⟩ := MergeClosure.envRules hstep
  exact ⟨he.trans hp.1, hr.trans hp.2⟩

/-- The tower of proofs the crank builds, from the `@Fiat` the `union` wrote. -/
def uTower : Nat → Term
  | 0 => .app fiatName []
  | n + 1 => uStepPf (uTower n)

/-- **Every one of them is a `@UF` row the state holds.** The hypotheses of `uf_row_succ`,
transported along the rounds: the signature (`RunReach.sig`), the environment and the rules
(`runReach_envRules`), and the rows (`RunReach.contained`). -/
theorem uTgt_saturate_tower {d : Database} (h : SaturateReach rebuildRuleset uTgt d) :
    ∀ n, uUFRow (uTower n) ∈ d.terms ∧ uTower n ∈ d.terms := by
  have hcon : uTgt.terms ⊆ d.terms := (RunReach.contained h.1).terms
  have hsig : d.sig = uSig := (RunReach.sig h.1).trans uTgt_sig
  have henv : d.env = [] := (runReach_envRules h.1).1.trans uTgt_env
  have hrule : uRebuildB ∈ d.rules := by
    rw [(runReach_envRules h.1).2]; exact uRebuildB_mem_rules
  intro n
  induction n with
  | zero => exact ⟨hcon (uUFRow_fiat ▸ uTgt_mem_uf), hcon uTgt_mem_fiat⟩
  | succ n ih =>
    exact uf_row_succ h.2.1 h.2.2 henv hsig hrule (hcon uTgt_mem_viewB) (hcon uTgt_mem_A)
      (hcon uTgt_mem_B) (hcon uTgt_mem_fiat) ih.1 ih.2

/-- Each turn is strictly larger than the last, which is the whole of why the tower has no
top. -/
theorem sizeOf_lt_uStepPf (q : Term) : sizeOf q < sizeOf (uStepPf q) := by
  simp only [uStepPf, Term.app.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
  omega

theorem uTower_injective : Function.Injective uTower := by
  have hm : StrictMono fun n => sizeOf (uTower n) :=
    strictMono_nat_of_lt_succ fun n => sizeOf_lt_uStepPf (uTower n)
  exact fun a b hab => hm.injective (congrArg sizeOf hab)

/-- **So `Cmd.saturate rebuildRuleset` can only reach a state holding infinitely many terms** —
an injection from `Nat` into them, which is the statement rather than `Set.Infinite` because
this file's imports carry no cardinality API, and
the specification's run of `encode uProgram` stops one command short of finishing.

This is the finding. `satProgram_programStep` remains true — a program that only builds
reaches its target — and this is what happens the moment a program asserts an equation
between distinct terms, which is every program `Database.UnionsRead` is about. The two facts
together say the specification's `ProgramStep` is available for the encoded program exactly
where the obligation it would discharge is vacuous.

**Read as an implication, and its antecedent is what is in doubt.** The content is
`uf_row_succ` and `uTgt_saturate_tower`: *if* a state satisfies the fixpoint condition
`Cmd.saturate rebuildRuleset` demands, it holds an injective image of `Nat`. Concluding "so
there is no such state" needs one more step — that rounds from `Database.empty` reach only
finitely many terms — which is not formalized here and is not needed: what the run above
needed was a state to step *to*, and this says any such state is not one a finite chain of
rounds from a finite state produces. -/
theorem uTgt_saturate_infinite {d : Database} (h : SaturateReach rebuildRuleset uTgt d) :
    ∃ f : Nat → Term, Function.Injective f ∧ ∀ n, f n ∈ d.terms :=
  ⟨fun n => uUFRow (uTower n),
    fun a b hab => uTower_injective (by
      simpa only [uUFRow, Term.app.injEq, List.cons.injEq, true_and, and_true] using hab),
    fun n => (uTgt_saturate_tower h n).1⟩

@[inherit_doc uTgt_saturate_infinite]
theorem uTgt_cmdStep_saturate_infinite {d : Database}
    (h : CmdStep uTgt (.saturate rebuildRuleset) d) :
    ∃ f : Nat → Term, Function.Injective f ∧ ∀ n, f n ∈ d.terms :=
  uTgt_saturate_infinite (cmdStep_saturate_iff.mp h)

/-- **The finding, at the program.** `uEncoded_eq` splits `encode uProgram` into the twenty
commands `uProgram_programStep_prefix` steps and this one. -/
theorem uProgram_last_command_infinite {d : Database}
    (h : ProgramStep uTgt [.saturate rebuildRuleset] d) :
    ∃ f : Nat → Term, Function.Injective f ∧ ∀ n, f n ∈ d.terms := by
  cases h with
  | cons hc hrest =>
    cases hrest with
    | nil => exact uTgt_cmdStep_saturate_infinite hc

end Egglog
