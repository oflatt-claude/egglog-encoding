import EgglogSemantics.Impl.Closure
import EgglogSemantics.Spec.Match

/-!
# An executable interpreter

`Spec/Step.lean`'s `RunRules` is a function but not a computation: it unions over a set
of substitutions carved out by a predicate. This runs the constructor fragment computably,
so programs can actually be executed — which is what makes the model testable against the
Rust (`PLAN.md`, "Differential testing"). `Proofs/Interp.lean`'s `exec_programStep` is the
equation between the two, in both directions.

`FDatabase`'s components are `List`s, not `Finset`s, for one blunt reason:
`Finset.toList` is noncomputable, so anything that has to *enumerate* a `Finset` cannot
be compiled. Duplicates in the lists are harmless — the denotation is the set of members,
and `closureF` dedups through `List.toFinset` where the closure needs a `Finset`.

The e-matching enumerator differs from the spec in two respects, both deliberately. The
spec takes one substitution per pattern and joins them (`Env.UnionAll`); the enumerator
assigns the *whole query's* free variables at once and then
restricts to each pattern with `Env.canon`. The two agree up to `Env.Agree`, which by
`evalLocalActions_agree` is all `RunRules` can see. And it assigns from
`FDatabase.valueTerms` rather than from `terms`, which is a *strict* refinement — see
there.
-/

namespace Egglog
/-! ### The table index

`Spec/` has no rows: a merge function's entry at the key `a…` with value columns `v…` is
the term `f(a…, v…)`, and a constructor's is `f(a…)`. An implementation cannot work from
that alone, because egglog's tables are not append-only — an insert *replaces* the
resident entry and a rebuild *moves* one — and reconstructing which entries are still
current by scanning a monotone term set is exactly the work a table exists to avoid.

`FDatabase.rows` is therefore an **index**: a derived structure, re-keyed by
`FDatabase.rebuild` and deleted from by `FDatabase.mergeOneOriented`, over a `terms` that
never shrinks. `FDatabase.toDatabase` drops it, so neither the re-keying nor the deletion
moves the denotation. -/
/-- One tuple of one function's table: `fn args… ↦ out…`.

`out` is a *list*, one entry per value column: egglog's tables are multi-column, and the
encoding depends on it — `@UF_<Sort>` carries a parent *and* a proof.

**A row's entry term is `fn(args… ++ out…)`**, which is the one thing the index and the
denotation have to agree on. A constructor's `FnDecl.entryWidth` is its `arity`, so a
constructor has *no* value column and its row is `⟨f, as, []⟩`, whose entry term is the
application `f(as)` itself — which is what makes its functional dependency plain
congruence. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  out : List Term
  deriving DecidableEq

/-- The constructor entries among `t`'s subterms, each mapping its own children to itself,
in `subtermList`'s order.

A **declared merge function**'s application is an entry term `f(a…, v…)` that already
carries its value columns, and `FDatabase.addRow` indexes that one directly; synthesising
`⟨f, a… ++ v…, [f(a…, v…)]⟩` for it as well would give `f` a second, bogus key class. So
those are filtered out, and everything else — a declared constructor, or a name nobody
declared — is recorded exactly as before. `Expr.eval` builds no application of a merge
function, so on a term the evaluator produced the filter removes nothing. -/
def Term.ctorRowList (sig : Signature) (t : Term) : List Row :=
  t.subtermList.filterMap fun s =>
    match s with
    | .app f as => if (sig.mergeOf f).isSome then none else some ⟨f, as, []⟩
    | .lit _ => none

/-! ### Finite databases -/
/-- The executable counterpart of `Database`. Every component is a `List`; membership,
not multiplicity or order, is what it denotes. -/
structure FDatabase where
  sig : Signature
  terms : List Term
  /-- The table index. Not a component of the denotation — see "The table index" above. -/
  rows : List Row
  eqs : List (Term × Term)
  env : Env
  rules : List Rule

namespace FDatabase
/-- The spec database an `FDatabase` denotes. The refinement theorems are stated against
this.

**`terms` becomes the diagonal.** A `Database` has no term field — `t` is present exactly
when `t = t` is derivable — so the list contributes one reflexive equation per member and
`Database.terms` reads them back out. `toDatabase_terms` is that bridge, and it is what
every refinement theorem rests on.

**An equation is kept only where the list holds both of its sides**, which is what makes
that bridge unconditional rather than an invariant to be maintained. `Cong` can reach
`Cong db t t` by `symm` and `trans` from a *non*-reflexive pair, so an equation naming a
term the list does not hold would put a term in the denotation that the interpreter cannot
see. The restriction is not a weakening — `closureTotal` already imposes it on `eqsF`, so
this is the denotation agreeing with the computation, and it removes nothing from a
database the interpreter built: `EqsInTerms` below.

`rows` is simply dropped: every row is also an entry term in `terms`, put there by
`addRow` and never taken out, so the index carries nothing the denotation does not already
have. Synthesising the entry terms *here* instead would not work — `closureF`'s candidate
universe is `terms`, so an entry that is not in the list is congruent to nothing. -/
def toDatabase (d : FDatabase) : Database where
  sig := d.sig
  eqs := {p | p.1 = p.2 ∧ p.1 ∈ d.terms} ∪
    {p | p ∈ d.eqs ∧ p.1 ∈ d.terms ∧ p.2 ∈ d.terms}
  env := d.env
  rules := {r | r ∈ d.rules}

/-- Every term a derivation over the denotation mentions is one the list holds. Immediate
from `toDatabase`'s restriction on `eqs`: `assert` is the only rule that introduces a term,
and `congr`'s two self-congruence premises carry the memberships for it. -/
theorem toDatabase_cong_mem {d : FDatabase} {a b : Term} (h : Cong d.toDatabase a b) :
    a ∈ d.terms ∧ b ∈ d.terms := by
  match h with
  | .assert hm =>
    rcases hm with ⟨he, hd⟩ | ⟨_, h₁, h₂⟩
    · refine ⟨hd, ?_⟩
      have he' : a = b := he
      exact he' ▸ hd
    · exact ⟨h₁, h₂⟩
  | .symm h => exact (toDatabase_cong_mem h).symm
  | .trans h₁ h₂ => exact ⟨(toDatabase_cong_mem h₁).1, (toDatabase_cong_mem h₂).2⟩
  | .congr hm₁ hm₂ _ => exact ⟨(toDatabase_cong_mem hm₁).1, (toDatabase_cong_mem hm₂).1⟩

/-- **The denotation holds exactly the terms the list does.** -/
theorem toDatabase_terms (d : FDatabase) : d.toDatabase.terms = {t | t ∈ d.terms} := by
  ext t
  exact ⟨fun h => (toDatabase_cong_mem h).1, fun h => Cong.assert (Or.inl ⟨rfl, h⟩)⟩

/-- The initial database. -/
def empty : FDatabase where
  sig := fun _ => none
  terms := []
  rows := []
  eqs := []
  env := []
  rules := []

/-- Insert `t` and all of its subterms.

Deduplicated on insertion. That is invisible to `toDatabase`, but not to performance: a
round's `union` copies every operand's terms, so without it the list length multiplies
each round and the per-substitution `List.toFinset` in `closureF` goes quadratic on it. -/
def addTerm (t : Term) (d : FDatabase) : FDatabase :=
  { d with terms := (t.subtermList ++ d.terms).dedup,
           rows := (Term.ctorRowList d.sig t ++ d.rows).dedup }

/-- `addTerm` over a list. -/
def addTerms (ts : List Term) (d : FDatabase) : FDatabase :=
  ts.foldl (fun e t => e.addTerm t) d

/-- `(set (f as…) vs)`, computed: the entry term `f(as…, vs…)` — which is all
`Spec/Eval.lean`'s `evalAction` records — plus the index row.

The entry term is what keeps the index derived. `rows` is re-keyed and deleted from while
`terms` is not, so a row that has moved or gone is still an entry term the denotation
holds, and `Database.Out` reads it from every congruent key. -/
def addRow (f : FnName) (as vs : List Term) (d : FDatabase) : FDatabase :=
  let d := d.addTerm (.app f (as ++ vs))
  { d with rows := (⟨f, as, vs⟩ :: d.rows).dedup }

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (d : FDatabase) : FDatabase :=
  { (d.addTerm a).addTerm b with eqs := ((a, b) :: d.eqs).dedup }

/-- Union two databases, taking the signature, environment and rules from the left.
`Database.sUnion`, computed, at the two-operand shape `execRunRules` folds with. -/
def union (d₁ d₂ : FDatabase) : FDatabase :=
  { d₁ with terms := (d₁.terms ++ d₂.terms).dedup, rows := (d₁.rows ++ d₂.rows).dedup,
            eqs := (d₁.eqs ++ d₂.eqs).dedup }

/-! ### What `toDatabase` restricts by

`toDatabase` keeps an equation only where `terms` holds both of its sides, and
`closureTotal` imposes the same restriction on `eqsF`. Neither loses anything: `empty`
satisfies the condition, the four writers below preserve it, and they are the only ones —
every `set`, `union` and rule firing goes through them, and `Impl/Merge.lean` reaches
`eqs` and `terms` only through `addTerm` and `execActions`, a merge pass otherwise
rewriting `rows` alone. -/
/-- Every equation names terms the list holds. -/
def EqsInTerms (d : FDatabase) : Prop := ∀ p ∈ d.eqs, p.1 ∈ d.terms ∧ p.2 ∈ d.terms

theorem empty_eqsInTerms : EqsInTerms empty := by simp [EqsInTerms, empty]

/-- `addTerm` only grows `terms`. -/
theorem EqsInTerms.addTerm {d : FDatabase} (h : d.EqsInTerms) (t : Term) :
    (d.addTerm t).EqsInTerms := by
  intro p hp
  simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
  exact ⟨Or.inr (h p hp).1, Or.inr (h p hp).2⟩

/-- `addRow` is `addTerm` on the entry term. -/
theorem EqsInTerms.addRow {d : FDatabase} (h : d.EqsInTerms) (f : FnName) (as vs : List Term) :
    (FDatabase.addRow f as vs d).EqsInTerms := h.addTerm _

/-- **The one writer that introduces a pair**, and it inserts both sides. -/
theorem EqsInTerms.addEq {d : FDatabase} (h : d.EqsInTerms) (a b : Term) :
    (FDatabase.addEq a b d).EqsInTerms := by
  have hself : ∀ t : Term, t ∈ t.subtermList := fun t => by
    cases t <;> simp [Term.subtermList]
  intro p hp
  simp only [FDatabase.addEq, List.mem_dedup, List.mem_cons] at hp
  simp only [FDatabase.addEq, FDatabase.addTerm, List.mem_dedup, List.mem_append]
  rcases hp with rfl | hp
  · exact ⟨Or.inr (Or.inl (hself a)), Or.inl (hself b)⟩
  · exact ⟨Or.inr (Or.inr (h p hp).1), Or.inr (Or.inr (h p hp).2)⟩

/-- `union` concatenates `eqs` and `terms` together. -/
theorem EqsInTerms.union {d₁ d₂ : FDatabase} (h₁ : d₁.EqsInTerms) (h₂ : d₂.EqsInTerms) :
    (d₁.union d₂).EqsInTerms := by
  intro p hp
  simp only [FDatabase.union, List.mem_dedup, List.mem_append] at hp ⊢
  rcases hp with hp | hp
  · exact ⟨Or.inl (h₁ p hp).1, Or.inl (h₁ p hp).2⟩
  · exact ⟨Or.inr (h₂ p hp).1, Or.inr (h₂ p hp).2⟩

/-- `terms` as a `Finset`, for the closure. -/
def termsF (d : FDatabase) : Finset Term := d.terms.toFinset

/-- `eqs` as a `Finset`. -/
def eqsF (d : FDatabase) : Finset (Term × Term) := d.eqs.toFinset

/-- The interpreter's invariant, stated on the denotation so that every `Database.WF`
lemma transfers through the `toDatabase_*` bridges. -/
def WF (d : FDatabase) : Prop := d.toDatabase.WF

/-- The congruence closure of `d`, computed. -/
def closureF (d : FDatabase) : Finset (Term × Term) := closureTotal d.termsF d.eqsF

/-- The terms a rule variable may be bound to: everything `terms` holds except a **merge
function's entry term**.

`terms` holds both the values the program built and the entries it recorded, and an entry
is not a value: `Dist(a…, v…)` names no e-class, it records that `Dist` at `a…` reads
`v…`. Two reasons to keep the enumerator off them. `assignments` is `|terms| ^ |vars|` by
construction, so every entry term multiplies the search; and a substitution binding a
variable to one would make `(Hit x)` build a term whose child is a table entry, which
egglog has no way to express.

This is **stricter than the specification**. `Spec/Match.lean`'s `ValidEnv` asks only that
each bound term be in `db.terms`, and deliberately does not say which of the two kinds it
is, so a spec-side substitution may bind an entry term where this enumerator will not
produce one. Firing on fewer substitutions is the safe direction — the interpreter's
result stays a state the spec reaches — but it is a refinement and not an equality, so it
is one-directional where `exec_programStep` used to be two. -/
def valueTerms (d : FDatabase) : List Term :=
  d.terms.filter fun t => match t with
    | .app f _ => (d.sig.mergeOf f).isNone
    | .lit _ => true

/-- Whether two tuples are pointwise congruent. Compares a row's key and value columns
against a pattern's operands (`patternHolds`, `Pattern.values`) and two colliding rows'
keys (`Impl/Merge.lean`, `mergeOne`). -/
def congrTuple (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

end FDatabase
/-! ### Enumerating substitutions -/
/-- Every assignment of `vars` to `terms`, with the domain in `vars`' order. -/
def assignments (terms : List Term) : List Var → List Env
  | [] => [[]]
  | v :: vs => terms.flatMap fun t => (assignments terms vs).map fun σ => (v, t) :: σ

/-- `σ` cut down to `vars` and put in `vars`' order. Used both to canonicalize a
substitution the spec produced and to restrict a query substitution to one pattern. -/
def Env.canon (vars : List Var) (σ : Env) : Env :=
  vars.filterMap fun v => (Env.lookup v σ).map fun t => (v, t)

/-! ### E-matching -/
/-- The free variables of a query: the variables the enumerator assigns. -/
def Query.freeVars (q : Query) (σ : Env) : List Var :=
  q.foldr (fun p acc => p.freeVars σ ∪ acc) []

/-- `Matches`'s side conditions for one pattern, computed: the pattern's instance
is congruent — in the database extended with it — to a witness the database already
holds. The instance is added because a pattern operand may denote a term the program
never built.

The witness is a term, except at a **merge function's** entry atom, where it is a *row*
and the key and value operands are added instead. The index is what says which of that
function's recorded entries is current, and nothing else does. It says nothing about a
constructor: a constructor's entry is its own application, so the atom asks about the
term `f(a…, v…)` like any other instance, and a row — which fixes one key/value split
where the term admits every split — would answer a different question.

It compares with `closureF`, which computes exactly the specification's `Cong`. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .values vs f as =>
    match Expr.evalList d.sig vs (d.env ++ σ), Expr.evalList d.sig as (d.env ++ σ) with
    | some us, some ts =>
      if (d.sig.mergeOf f).isSome then
        let cl := ((d.addTerms ts).addTerms us).closureF
        d.rows.any fun r =>
          decide (r.fn = f) && FDatabase.congrTuple cl ts r.args
            && FDatabase.congrTuple cl us r.out
      else
        let t := Term.app f (ts ++ us)
        let cl := (d.addTerm t).closureF
        decide (∃ w ∈ d.terms, (w, t) ∈ cl)
    | _, _ => false
  | .expr e =>
    match e.eval d.sig (d.env ++ σ) with
    | none => false
    | some t =>
      let cl := (d.addTerm t).closureF
      decide (∃ w ∈ d.terms, (w, t) ∈ cl)
  | .eq e₁ e₂ =>
    match e₁.eval d.sig (d.env ++ σ), e₂.eval d.sig (d.env ++ σ) with
    | some t₁, some t₂ =>
      let cl := ((d.addTerm t₁).addTerm t₂).closureF
      decide ((t₁, t₂) ∈ cl) && decide (∃ w ∈ d.terms, (w, t₁) ∈ cl)
    | _, _ => false

/-- The substitutions satisfying a whole query. Assigns from `FDatabase.valueTerms`, not
from `terms`: a variable is bound to a value the program built, never to a table entry. -/
def matchQuery (d : FDatabase) (q : Query) : List Env :=
  (assignments d.valueTerms (Query.freeVars q d.env)).filter fun σ =>
    q.all fun p => patternHolds d p (Env.canon (p.freeVars d.env) σ)

/-! ### Hoisting the closure out of the candidate loop

`patternHolds` computes `(d.addTerms ts).closureF` where `ts` is the pattern *instance*, so
the closure is nominally per-substitution and `matchQuery` pays one per candidate. It is
nominal: `addTerms` only ever *adds* to `terms` and never touches `eqs`, and `closureF`
reads nothing else, so a candidate whose instance the database already holds — every
subterm of it — gets `d`'s own closure back. That is the common case and on an encoded
program it is every case: a view atom's operands are the variables' bindings, which
`assignments` drew from `valueTerms`.

So the closure is computed **once per query** and reused wherever the instance adds
nothing. What that is worth: the encoded `assoc-1`'s five-variable rule enumerates 7776
candidates, and `matchQuery` took 39.4 s on it — of which 15 ms was the enumeration, the
substitutions and the row scans, and the rest one closure per candidate. All 7776 instances
were already held.

`csimp` is what redirects the executable. Every theorem in `Proofs/` is stated and proved
over `matchQuery`, whose definition is untouched; `matchQueryFast_eq` is the only new
obligation, and it is an equality on the nose. -/
/-- Whether the database already holds every subterm of every one of `ts`, which is when
`addTerms ts` leaves `termsF` — and so `closureF` — alone. -/
def FDatabase.holdsAll (d : FDatabase) (ts : List Term) : Bool :=
  ts.all fun t => t.subtermList.all fun s => decide (s ∈ d.terms)

/-- `(d.addTerms ts).closureF`, given `d`'s own closure `cl` to reuse where `ts` adds
nothing. `closureWith_eq` is the equation; nothing else should call this with a `cl` that is
not `d.closureF`. -/
def FDatabase.closureWith (cl : Finset (Term × Term)) (d : FDatabase) (ts : List Term) :
    Finset (Term × Term) :=
  if d.holdsAll ts then cl else (d.addTerms ts).closureF

/-- `addTerm` only grows `terms`. -/
theorem FDatabase.mem_terms_addTerm {d : FDatabase} {t s : Term} (h : s ∈ d.terms) :
    s ∈ (d.addTerm t).terms := by
  simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append]
  exact Or.inr h

/-- **A term the database already holds adds nothing to the candidate universe.** -/
theorem FDatabase.termsF_addTerm_of_mem {d : FDatabase} {t : Term}
    (h : ∀ s ∈ t.subtermList, s ∈ d.terms) : (d.addTerm t).termsF = d.termsF := by
  ext s
  simp only [FDatabase.termsF, FDatabase.addTerm, List.mem_toFinset, List.mem_dedup,
    List.mem_append]
  exact ⟨fun hs => hs.elim (h s) id, Or.inr⟩

/-- …and so nothing to the closure, `addTerm` not touching `eqs`. -/
theorem FDatabase.closureF_addTerm_of_mem {d : FDatabase} {t : Term}
    (h : ∀ s ∈ t.subtermList, s ∈ d.terms) : (d.addTerm t).closureF = d.closureF := by
  unfold FDatabase.closureF
  rw [FDatabase.termsF_addTerm_of_mem h]
  rfl

/-- `addTerms` over a list the database already holds, likewise. -/
theorem FDatabase.closureF_addTerms_of_mem {ts : List Term} : ∀ {d : FDatabase},
    (∀ t ∈ ts, ∀ s ∈ t.subtermList, s ∈ d.terms) →
    (d.addTerms ts).closureF = d.closureF := by
  induction ts with
  | nil => intro _ _; rfl
  | cons t ts ih =>
    intro d h
    have hstep : ∀ u ∈ ts, ∀ s ∈ u.subtermList, s ∈ (d.addTerm t).terms := fun u hu s hs =>
      FDatabase.mem_terms_addTerm (h u (List.mem_cons_of_mem _ hu) s hs)
    calc (d.addTerms (t :: ts)).closureF = ((d.addTerm t).addTerms ts).closureF := rfl
      _ = (d.addTerm t).closureF := ih hstep
      _ = d.closureF := FDatabase.closureF_addTerm_of_mem (h t (List.mem_cons_self ..))

/-- `addTerms` over a concatenation is `addTerms` twice. -/
theorem FDatabase.addTerms_append (d : FDatabase) (ts us : List Term) :
    d.addTerms (ts ++ us) = (d.addTerms ts).addTerms us :=
  List.foldl_append ..

/-- **What the reuse is allowed to be.** -/
theorem FDatabase.closureWith_eq (d : FDatabase) (ts : List Term) :
    d.closureWith d.closureF ts = (d.addTerms ts).closureF := by
  unfold FDatabase.closureWith
  split
  · rename_i h
    simp only [FDatabase.holdsAll, List.all_eq_true, decide_eq_true_eq] at h
    exact (FDatabase.closureF_addTerms_of_mem h).symm
  · rfl

/-- `patternHolds` with the closure taken as a parameter. -/
def patternHoldsWith (cl : Finset (Term × Term)) (d : FDatabase) (p : Pattern) (σ : Env) :
    Bool :=
  match p with
  | .values vs f as =>
    match Expr.evalList d.sig vs (d.env ++ σ), Expr.evalList d.sig as (d.env ++ σ) with
    | some us, some ts =>
      if (d.sig.mergeOf f).isSome then
        let cl' := d.closureWith cl (ts ++ us)
        d.rows.any fun r =>
          decide (r.fn = f) && FDatabase.congrTuple cl' ts r.args
            && FDatabase.congrTuple cl' us r.out
      else
        let t := Term.app f (ts ++ us)
        let cl' := d.closureWith cl [t]
        decide (∃ w ∈ d.terms, (w, t) ∈ cl')
    | _, _ => false
  | .expr e =>
    match e.eval d.sig (d.env ++ σ) with
    | none => false
    | some t =>
      let cl' := d.closureWith cl [t]
      decide (∃ w ∈ d.terms, (w, t) ∈ cl')
  | .eq e₁ e₂ =>
    match e₁.eval d.sig (d.env ++ σ), e₂.eval d.sig (d.env ++ σ) with
    | some t₁, some t₂ =>
      let cl' := d.closureWith cl [t₁, t₂]
      decide ((t₁, t₂) ∈ cl') && decide (∃ w ∈ d.terms, (w, t₁) ∈ cl')
    | _, _ => false

/-- At `d`'s own closure it is `patternHolds`, on the nose. -/
theorem patternHoldsWith_eq (d : FDatabase) (p : Pattern) (σ : Env) :
    patternHoldsWith d.closureF d p σ = patternHolds d p σ := by
  have h1 : ∀ t : Term, d.closureWith d.closureF [t] = (d.addTerm t).closureF := fun t =>
    FDatabase.closureWith_eq d [t]
  have h2 : ∀ ts us : List Term,
      d.closureWith d.closureF (ts ++ us) = ((d.addTerms ts).addTerms us).closureF := by
    intro ts us
    rw [FDatabase.closureWith_eq, FDatabase.addTerms_append]
  have h3 : ∀ t₁ t₂ : Term,
      d.closureWith d.closureF [t₁, t₂] = ((d.addTerm t₁).addTerm t₂).closureF := fun t₁ t₂ =>
    FDatabase.closureWith_eq d [t₁, t₂]
  cases p with
  | expr e =>
    cases he : e.eval d.sig (d.env ++ σ) with
    | none => simp only [patternHoldsWith, patternHolds, he]
    | some t => simp only [patternHoldsWith, patternHolds, he, h1]
  | eq e₁ e₂ =>
    cases he₁ : e₁.eval d.sig (d.env ++ σ) with
    | none => simp only [patternHoldsWith, patternHolds, he₁]
    | some t₁ =>
      cases he₂ : e₂.eval d.sig (d.env ++ σ) with
      | none => simp only [patternHoldsWith, patternHolds, he₁, he₂]
      | some t₂ => simp only [patternHoldsWith, patternHolds, he₁, he₂, h3]
  | values vs f as =>
    cases hv : Expr.evalList d.sig vs (d.env ++ σ) with
    | none => simp only [patternHoldsWith, patternHolds, hv]
    | some us =>
      cases ha : Expr.evalList d.sig as (d.env ++ σ) with
      | none => simp only [patternHoldsWith, patternHolds, hv, ha]
      | some ts =>
        simp only [patternHoldsWith, patternHolds, hv, ha, h1, h2]

/-- `matchQuery` with the closure computed once, as a parameter. -/
def matchQueryWith (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  (assignments d.valueTerms (Query.freeVars q d.env)).filter fun σ =>
    q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars d.env) σ)

/-- **The fast path.** `matchQuery` with one congruence closure per query instead of one
per candidate. Taking `cl` through `matchQueryWith`'s parameter rather than a `let` is what
keeps it shared: a `let` used once inside the filter's closure is one the compiler may
inline back into it. -/
def matchQueryFast (d : FDatabase) (q : Query) : List Env :=
  matchQueryWith d.closureF d q

/-- At `d`'s own closure, `matchQueryWith` is `matchQuery`. -/
theorem matchQueryWith_eq (d : FDatabase) (q : Query) :
    matchQueryWith d.closureF d q = matchQuery d q := by
  simp only [matchQueryWith, matchQuery, patternHoldsWith_eq]

/-- **The fast path is the slow path**, on the nose — not up to `Env.Agree`, not up to
list permutation. -/
theorem matchQueryFast_eq (d : FDatabase) (q : Query) : matchQueryFast d q = matchQuery d q :=
  matchQueryWith_eq d q

/-! ### Pruning the candidate cross product

`matchQueryWith` assigns every free variable before it checks anything, so a query of `n`
variables enumerates `|valueTerms| ^ n` candidates however early its patterns decide.
Nothing of a candidate reaches a pattern's check but the pattern's **own** variables —
`patternHolds` is applied to `Env.canon (p.freeVars d.env) σ` and reads no more of `σ` — so
a prefix that already falsifies a pattern falsifies every extension of it, and those
extensions need never be built.

`matchPrune` is that: the same enumeration, in the same order, with each pattern checked at
the depth that binds its last variable. `matchPrune_eq` is the equality, on the nose, so the
enumerator's order — which decides row age and so a merge's `old`/`new` — is untouched.

**It is an asymptotic win with a constant-factor cost, and both are measured.** Encoding
adds a proof variable per view read, and pruning is what keeps that variable inside its own
atom's block instead of multiplying the whole search: at a 300 s budget the in-domain sweep
goes from 14 cases to 20, and at 60 s from 10 to 12. The cost is the readiness test at every
node, which mid-sized cases paid without earning it back — `up-thin` ran in 73 s unpruned
and 90 s pruned, the curated `actions` in 177 s and 235 s. What removes the exponent rather
than trimming it is a join over the index — binding a value column *from the rows* instead
of guessing it — which this approximates and does not replace. "Joining over the row index"
below is that join, and it keeps every node of this enumeration: `matchJoin` is `matchPrune`
with each level's candidate list narrowed, and `matchJoin_eq` is the equality between
them. -/
/-- The patterns a substitution already decides: those whose free variables it binds. -/
def Query.decided (d : FDatabase) (pre : Env) (q : Query) : Query :=
  q.filter fun p => (p.freeVars d.env).all fun v => decide (v ∈ Env.dom pre)

/-- `lookup` reads past an extension that cannot rebind. `Proofs/Database.lean`'s
`Env.lookup_append_of_mem` is the same fact; `Impl/` does not import `Proofs/`, and the
`csimp` below has to be registered before the callers this file compiles. -/
private theorem lookup_append_dom {v : Var} {σ₁ σ₂ : Env} (h : v ∈ Env.dom σ₁) :
    Env.lookup v (σ₁ ++ σ₂) = Env.lookup v σ₁ := by
  induction σ₁ with
  | nil => simp [Env.dom] at h
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases hv : v = w
    · simp [Env.lookup, hv]
    · simp only [Env.dom, List.map_cons, List.mem_cons] at h
      simp [Env.lookup, hv, ih (h.resolve_left hv)]

/-- A pattern's operand environment does not move once its variables are bound. -/
theorem Env.canon_append_of_dom {vars : List Var} {pre σ : Env}
    (h : ∀ v ∈ vars, v ∈ Env.dom pre) : Env.canon vars (pre ++ σ) = Env.canon vars pre := by
  induction vars with
  | nil => rfl
  | cons w ws ih =>
    have hw := lookup_append_dom (σ₂ := σ) (h w List.mem_cons_self)
    have hws := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
    simp only [Env.canon, List.filterMap_cons, hw] at *
    rw [hws]

/-- `filter` distributes over `flatMap`. -/
private theorem filter_flatMap {α β : Type} (p : β → Bool) (f : α → List β) (l : List α) :
    (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

/-- `filter` past a `map`, as the composed predicate. -/
private theorem filter_map_comp {α β : Type} (p : β → Bool) (f : α → β) (l : List α) :
    (l.map f).filter p = (l.filter fun a => p (f a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

/-- The enumeration of `vs` out of `ts`, extending `pre`, with every decided pattern checked
as it is decided.

`ts` is a parameter rather than `d.valueTerms`, for the reason the closure is one: it would
otherwise be recomputed at every node of the tree, and filtering `terms` through the
signature costs more than the pruning saves. -/
def matchPrune (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (ts : List Term)
    (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars d.env) pre) then [[]]
      else []
  | v :: vs =>
      ts.flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHoldsWith cl d p (Env.canon (p.freeVars d.env) pre') then
          (matchPrune cl d q ts pre' vs).map fun σ => (v, t) :: σ
        else []

/-- **Pruning drops exactly the candidates the final filter would have.** -/
theorem matchPrune_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query)
    (ts : List Term) :
    ∀ (vs : List Var) (pre : Env), matchPrune cl d q ts pre vs
      = (assignments ts vs).filter fun σ =>
          q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars d.env) (pre ++ σ)) := by
  intro vs
  induction vs with
  | nil =>
    intro pre
    simp [matchPrune, assignments, List.filter_cons, List.append_nil]
  | cons v vs ih =>
    intro pre
    rw [matchPrune, assignments, filter_flatMap]
    refine List.flatMap_congr fun t _ => ?_
    rw [filter_map_comp]
    by_cases hg : (Query.decided d (pre ++ [(v, t)]) q).all fun p =>
        patternHoldsWith cl d p (Env.canon (p.freeVars d.env) (pre ++ [(v, t)]))
    · rw [if_pos hg, ih (pre ++ [(v, t)])]
      congr 1
      refine List.filter_congr fun σ _ => ?_
      simp only [List.append_assoc, List.singleton_append]
    · -- the prefix already falsifies a pattern, so no extension of it survives
      have hnil : ((assignments ts vs).filter fun σ =>
          q.all fun p => patternHoldsWith cl d p
            (Env.canon (p.freeVars d.env) (pre ++ (v, t) :: σ))) = [] := by
        rw [Bool.not_eq_true, List.all_eq_false] at hg
        obtain ⟨p, hp, hfail⟩ := hg
        obtain ⟨hpq, hdecB⟩ := List.mem_filter.mp hp
        have hdec : ∀ w ∈ p.freeVars d.env, w ∈ Env.dom (pre ++ [(v, t)]) := fun w hw =>
          of_decide_eq_true (List.all_eq_true.mp hdecB w hw)
        refine List.filter_eq_nil_iff.mpr fun σ _ hall => hfail ?_
        have hp' := List.all_eq_true.mp hall p hpq
        rw [show pre ++ (v, t) :: σ = (pre ++ [(v, t)]) ++ σ by simp,
          Env.canon_append_of_dom hdec] at hp'
        exact hp'
      rw [if_neg hg, hnil, List.map_nil]

/-- `matchQueryWith`, pruned. -/
def matchQueryPruned (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  matchPrune cl d q d.valueTerms [] (Query.freeVars q d.env)

theorem matchQueryPruned_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) :
    matchQueryPruned cl d q = matchQueryWith cl d q := by
  rw [matchQueryPruned, matchPrune_eq, matchQueryWith]
  simp

/-- The pruned enumeration is `matchQueryWith`. Compiled code goes to `matchQueryJoin`
below, which narrows this one's candidate lists and is proved equal through it. -/
theorem matchQueryWith_eq_pruned : @matchQueryWith = @matchQueryPruned := by
  funext cl d q
  exact (matchQueryPruned_eq cl d q).symm

/-! ### Joining over the row index

Pruning stops an enumeration once a pattern has decided against it. What it cannot do is
stop the enumeration from *proposing* a binding no entry supports, and that is where the
exponent lives: a view read's two value columns are guessed out of `valueTerms` and then
checked against `rows`, when the rows are what those columns may be. `up-thin`'s rebuild
rule has five variables and the view it reads holds two entries, and the enumeration
proposes every fifth power of `valueTerms` to find them.

`matchJoin` reverses that at every level. Enumerating `v` under the prefix `pre`, each
entry atom is looked up in the index first — the rows of its function that `pre` has not
already ruled out — and the candidates for `v` are cut down to the terms one of *those*
rows admits in the column `v` sits in. Everything else is `matchPrune`: the same
enumeration order, the same readiness check at every node, the same final filter, and so
`matchJoin_eq` is an equality on the nose and not up to `Env.Agree`.

**The variable order is not ours to choose.** `matchQuery` emits its substitutions in
`assignments`' order and that order is observable — it decides row age, and so a merge's
`old`/`new` — so the join cannot reorder the loops to put a driving atom first. It narrows
in place instead, which is enough because the order `Query.freeVars` produces already
groups an atom's variables together: an encoded query reads children before parents, so by
the time an atom's own columns are enumerated its keys are bound, and the rows consistent
with those keys are few.

**Where the index may not speak.** A row admits a candidate up to congruence, so the
narrowing has to compare with the same closure `patternHoldsWith` will — and it does not
always have one. `closureWith` *grows* the closure when the atom's instance names a term
the database does not hold, and against a larger closure a candidate this filter rejects
might have been accepted. So the narrowing is confined to where the two provably coincide:
every operand a variable or a literal, every determined operand's value held, and every
candidate held (`held`, computed once per query). An atom outside that narrows nothing,
which is `matchPrune`'s behaviour and what the equality falls back to. -/
/-- What a join reads off one operand: a literal's own term, or a variable's binding.
`none` at an operand the prefix has yet to determine, and at an application — whose value
is a term the database need not hold. -/
def joinOperand (ρ : Env) : Expr → Option Term
  | .lit l => some (.lit l)
  | .var w => Env.lookup w ρ
  | .app _ _ => none

/-- `joinOperand` over an atom's operand list. -/
def joinKnown (ρ : Env) (es : List Expr) : List (Option Term) := es.map (joinOperand ρ)

/-- Whether every operand is one a join can read. An application is not: the enumeration
may never have built its value, and an atom whose instance the database does not hold is
checked against a closure this filter does not have. -/
def joinDrivable (es : List Expr) : Bool :=
  es.all fun e => match e with | .app _ _ => false | _ => true

/-- Whether a row is consistent with what the operands are known to be: at every determined
operand, the row's column there is congruent to it. An undetermined operand says nothing,
which is what makes this the partial `FDatabase.congrTuple`. -/
def joinConsistent (cl : Finset (Term × Term)) (ks : List (Option Term)) (xs : List Term) :
    Bool :=
  ks.length == xs.length && (ks.zip xs).all fun p =>
    match p.1 with
    | none => true
    | some t => decide ((t, p.2) ∈ cl)

/-- One atom, ready to narrow. -/
structure JoinAtom where
  /-- The atom's free variables — `Pattern.freeVars`, computed once. -/
  vars : List Var
  /-- The value-column operands. -/
  outs : List Expr
  /-- The key-column operands. -/
  keys : List Expr
  /-- The entries the prefix has not ruled out, rescanned for every candidate. -/
  rows : List Row

/-- `p` as a narrowing step for `v`, or `none` where the index cannot speak: a pattern that
is not an entry read; a **constructor**, whose atom is a term lookup and not a row scan; an
operand a join cannot read; an atom `v` does not occur in; or a determined operand naming a
term the database does not hold, which is exactly when `closureWith` would move the closure
out from under the comparison. -/
def joinPlan (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env) (v : Var) :
    Pattern → Option JoinAtom
  | .values vs f as =>
      let vars := (Pattern.values vs f as).freeVars d.env
      if (d.sig.mergeOf f).isSome && joinDrivable as && joinDrivable vs
          && decide (v ∈ vars) then
        let ρ := d.env ++ Env.canon vars pre
        let ka := joinKnown ρ as
        let kv := joinKnown ρ vs
        if d.holdsAll ((ka ++ kv).filterMap id) then
          some ⟨vars, vs, as,
            d.rows.filter fun r =>
              (r.fn == f) && joinConsistent cl ka r.args && joinConsistent cl kv r.out⟩
        else none
      else none
  | _ => none

/-- Whether the atom's surviving entries still admit `v ↦ t`. -/
def JoinAtom.keeps (a : JoinAtom) (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env)
    (v : Var) (t : Term) : Bool :=
  let ρ := d.env ++ Env.canon a.vars (pre ++ [(v, t)])
  a.rows.any fun r =>
    joinConsistent cl (joinKnown ρ a.keys) r.args
      && joinConsistent cl (joinKnown ρ a.outs) r.out

/-- The candidates for `v` under `pre`: `ts`, narrowed by every atom the index can drive.

**Atoms are applied fewest surviving entries first**, which is what `List.all`'s
short-circuit turns into a saving: the most constraining atom rejects a candidate before
any other atom's entries are scanned for it, and an atom with no surviving entry empties
the level outright. `held` is `d.holdsAll ts`, computed once per query — a candidate the
database does not hold would again be compared against the wrong closure. -/
def joinCands (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (held : Bool)
    (ts : List Term) (pre : Env) (v : Var) : List Term :=
  if held then
    let plans := (q.filterMap (joinPlan cl d pre v)).mergeSort fun a b =>
      decide (a.rows.length ≤ b.rows.length)
    ts.filter fun t => plans.all fun a => a.keeps cl d pre v t
  else ts

/-- `matchPrune`'s enumeration, with each variable's candidates read off the index. -/
def matchJoin (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (ts : List Term)
    (held : Bool) (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars d.env) pre) then [[]]
      else []
  | v :: vs =>
      (joinCands cl d q held ts pre v).flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHoldsWith cl d p (Env.canon (p.freeVars d.env) pre') then
          (matchJoin cl d q ts held pre' vs).map fun σ => (v, t) :: σ
        else []

/-! #### That the narrowing drops nothing

One direction is all that is needed and all that is true: a candidate some full
substitution satisfies the query on is one every atom's entries admit, so the filter keeps
it. The converse — that a candidate the filter keeps satisfies anything — is false and is
not asked for; the final check is still `patternHoldsWith`'s. -/
/-- `lookup` reads past a prefix that binds. -/
private theorem lookup_append_some {w : Var} {t : Term} {σ₁ σ₂ : Env}
    (h : Env.lookup w σ₁ = some t) : Env.lookup w (σ₁ ++ σ₂) = some t := by
  induction σ₁ with
  | nil => simp [Env.lookup] at h
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [List.cons_append, Env.lookup] at h ⊢
    by_cases hw : w = u
    · simp only [if_pos hw] at h ⊢; exact h
    · simp only [if_neg hw] at h ⊢; exact ih h

/-- `lookup` reads past a prefix that does not bind. -/
private theorem lookup_append_none {w : Var} {σ₁ σ₂ : Env} (h : Env.lookup w σ₁ = none) :
    Env.lookup w (σ₁ ++ σ₂) = Env.lookup w σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [List.cons_append, Env.lookup] at h ⊢
    by_cases hw : w = u
    · simp only [if_pos hw] at h; exact absurd h (by simp)
    · simp only [if_neg hw] at h ⊢; exact ih h

/-- **`Env.canon` is a restriction and nothing else**: it forgets the variables outside
`vars` and moves none of the others. `Proofs/Interp.lean`'s `Env.lookup_canon` is the
membership half of this; `Impl/` does not import `Proofs/`, and the narrowing below needs
the other half — that a variable outside `vars` is *not* bound — as well. -/
theorem Env.lookup_canon_eq (vars : List Var) (ρ : Env) (w : Var) :
    Env.lookup w (Env.canon vars ρ) = if w ∈ vars then Env.lookup w ρ else none := by
  induction vars with
  | nil => simp [Env.canon, Env.lookup]
  | cons u us ih =>
    simp only [Env.canon, List.filterMap_cons]
    cases hu : Env.lookup u ρ with
    | none =>
      by_cases hw : w = u
      · subst hw; simp only [Env.canon] at ih; simp [ih, hu]
      · simp only [Env.canon] at ih; simp [ih, hw]
    | some s =>
      by_cases hw : w = u
      · subst hw; simp [Env.lookup, hu]
      · simp only [Env.canon] at ih
        simp [Env.lookup, hw, ih]

/-- A binding `lookup` finds is one the list holds. -/
private theorem mem_of_lookup {w : Var} {t : Term} {σ : Env} (h : Env.lookup w σ = some t) :
    (w, t) ∈ σ := by
  induction σ with
  | nil => simp [Env.lookup] at h
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [Env.lookup] at h
    by_cases hw : w = u
    · subst hw
      rw [if_pos rfl, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · simp only [if_neg hw] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `assignments` binds from its own list. -/
private theorem assignments_snd {ts : List Term} : ∀ {vs : List Var} {σ : Env},
    σ ∈ assignments ts vs → ∀ b ∈ σ, b.2 ∈ ts := by
  intro vs
  induction vs with
  | nil => intro σ hσ b hb; simp only [assignments, List.mem_singleton] at hσ; simp [hσ] at hb
  | cons v vs ih =>
    intro σ hσ b hb
    simp only [assignments, List.mem_flatMap, List.mem_map] at hσ
    obtain ⟨t, ht, τ, hτ, rfl⟩ := hσ
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ht
    · exact ih hτ b hb

/-- Restriction to `vars` preserves an extension. -/
private theorem lookup_canon_mono {E : Env} {vars : List Var} {ρ ρ' : Env}
    (h : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) (w : Var) (y : Term)
    (hw : Env.lookup w (E ++ Env.canon vars ρ) = some y) :
    Env.lookup w (E ++ Env.canon vars ρ') = some y := by
  cases hE : Env.lookup w E with
  | some z => rw [lookup_append_some hE] at hw ⊢; exact hw
  | none =>
    rw [lookup_append_none hE] at hw ⊢
    rw [Env.lookup_canon_eq] at hw ⊢
    by_cases hm : w ∈ vars
    · rw [if_pos hm] at hw ⊢; exact h w y hw
    · rw [if_neg hm] at hw; exact absurd hw (by simp)

/-- `Expr.evalList` at a cons. -/
private theorem evalList_cons {sig : Signature} {e : Expr} {es : List Expr} {ρ : Env}
    {ks : List Term} (h : Expr.evalList sig (e :: es) ρ = some ks) :
    ∃ x ks', Expr.eval sig e ρ = some x ∧ Expr.evalList sig es ρ = some ks' ∧ ks = x :: ks' := by
  revert h
  simp only [Expr.evalList]
  cases he : Expr.eval sig e ρ with
  | none => simp
  | some x =>
    cases hl : Expr.evalList sig es ρ with
    | none => simp
    | some ks' =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq]
      intro h
      exact ⟨x, ks', rfl, rfl, h.symm⟩

/-- `holdsAll` is a `List.all`. -/
private theorem holdsAll_of_mem {d : FDatabase} {L : List Term} {x : Term}
    (h : d.holdsAll L = true) (hx : x ∈ L) : d.holdsAll [x] = true := by
  simp only [FDatabase.holdsAll, List.all_eq_true] at h ⊢
  intro s hs
  simp only [List.mem_singleton] at hs
  subst hs
  exact h _ hx

private theorem holdsAll_of_forall {d : FDatabase} {L : List Term}
    (h : ∀ x ∈ L, d.holdsAll [x] = true) : d.holdsAll L = true := by
  simp only [FDatabase.holdsAll, List.all_eq_true] at h ⊢
  intro x hx
  exact h x hx x (by simp)

/-- **Every operand's value is a term the database holds**, given that the determined ones
are and that the enumeration binds only from a list that is. This is what makes
`closureWith` return the closure the filter compared with. -/
private theorem joinKnown_holds {d : FDatabase} {ρ ρ' : Env}
    (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y)
    (hnew : ∀ w y, Env.lookup w ρ = none → Env.lookup w ρ' = some y →
      d.holdsAll [y] = true) :
    ∀ {es : List Expr} {ks : List Term}, joinDrivable es = true →
      Expr.evalList d.sig es ρ' = some ks →
      d.holdsAll ((joinKnown ρ es).filterMap id) = true →
      ∀ x ∈ ks, d.holdsAll [x] = true := by
  intro es
  induction es with
  | nil => intro ks _ hev _ x hx; simp only [Expr.evalList, Option.some.injEq] at hev
           subst hev; simp at hx
  | cons e es ih =>
    intro ks hdr hev hk x hx
    obtain ⟨y, ks', hey, hes, rfl⟩ := evalList_cons hev
    simp only [joinDrivable, List.all_cons, Bool.and_eq_true] at hdr
    have hknown : d.holdsAll ((joinKnown ρ es).filterMap id) = true := by
      refine holdsAll_of_forall fun z hz => holdsAll_of_mem hk ?_
      simp only [joinKnown, List.map_cons, List.filterMap_cons] at hz ⊢
      cases hop : joinOperand ρ e with
      | none => simpa [hop] using hz
      | some w => simp only [id]; exact List.mem_cons_of_mem _ hz
    have hhead : d.holdsAll [y] = true := by
      match e with
      | .app _ _ => simp at hdr
      | .lit l =>
        simp only [Expr.eval, Option.some.injEq] at hey
        subst hey
        refine holdsAll_of_mem hk ?_
        simp only [joinKnown, List.map_cons, List.filterMap_cons, joinOperand, id]
        exact List.mem_cons_self ..
      | .var w =>
        simp only [Expr.eval] at hey
        cases hw : Env.lookup w ρ with
        | none => exact hnew w y hw hey
        | some z =>
          have hzy : z = y := by
            have h' := hmono w z hw
            rw [hey] at h'
            exact (Option.some.injEq .. ▸ h').symm
          subst hzy
          refine holdsAll_of_mem hk ?_
          simp only [joinKnown, List.map_cons, List.filterMap_cons, joinOperand, hw, id]
          exact List.mem_cons_self ..
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hhead
    · exact ih hdr.2 hes hknown x hx

/-- `congrTuple` at a cons. -/
private theorem congrTuple_cons {cl : Finset (Term × Term)} {x : Term} {ks xs : List Term}
    (h : FDatabase.congrTuple cl (x :: ks) xs = true) :
    ∃ y xs', xs = y :: xs' ∧ (x, y) ∈ cl ∧ FDatabase.congrTuple cl ks xs' = true := by
  cases xs with
  | nil => simp [FDatabase.congrTuple] at h
  | cons y xs' =>
    simp only [FDatabase.congrTuple, List.length_cons, beq_iff_eq, Nat.add_right_cancel_iff,
      List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨y, xs', rfl, h.2.1, h.1, h.2.2⟩

/-- **What the index is asked is implied by what the atom will be asked.** A row congruent
to the whole instance is consistent with the part of it the prefix has determined. -/
private theorem joinConsistent_of_congrTuple {cl : Finset (Term × Term)} {d : FDatabase}
    {ρ ρ' : Env} (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) :
    ∀ {es : List Expr} {ks xs : List Term}, joinDrivable es = true →
      Expr.evalList d.sig es ρ' = some ks →
      FDatabase.congrTuple cl ks xs = true →
      joinConsistent cl (joinKnown ρ es) xs = true := by
  intro es
  induction es with
  | nil =>
    intro ks xs _ hev hct
    simp only [Expr.evalList, Option.some.injEq] at hev
    subst hev
    simp only [FDatabase.congrTuple, List.length_nil, beq_iff_eq, Bool.and_eq_true] at hct
    cases xs with
    | nil => simp [joinConsistent, joinKnown]
    | cons _ _ => simp at hct
  | cons e es ih =>
    intro ks xs hdr hev hct
    obtain ⟨y, ks', hey, hes, rfl⟩ := evalList_cons hev
    obtain ⟨z, xs', rfl, hzy, hct'⟩ := congrTuple_cons hct
    simp only [joinDrivable, List.all_cons, Bool.and_eq_true] at hdr
    have htail := ih hdr.2 hes hct'
    have hhead : ∀ s, joinOperand ρ e = some s → (s, z) ∈ cl := by
      intro s hs
      match e with
      | .app _ _ => simp [joinOperand] at hs
      | .lit l =>
        simp only [joinOperand, Option.some.injEq] at hs
        simp only [Expr.eval, Option.some.injEq] at hey
        subst hs; subst hey; exact hzy
      | .var w =>
        simp only [joinOperand] at hs
        simp only [Expr.eval] at hey
        have := hmono w s hs
        rw [hey] at this
        cases (Option.some.injEq .. ▸ this)
        exact hzy
    simp only [joinKnown, List.map_cons, joinConsistent, List.length_cons, beq_iff_eq,
      List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at htail ⊢
    refine ⟨?_, ?_, ?_⟩
    · omega
    · cases hop : joinOperand ρ e with
      | none => simp
      | some s => simpa using hhead s hop
    · exact htail.2

/-- What `joinPlan` promises when it produces an atom. -/
private theorem joinPlan_values {cl : Finset (Term × Term)} {d : FDatabase} {pre : Env}
    {v : Var} {vs as : List Expr} {f : FnName} {a : JoinAtom}
    (h : joinPlan cl d pre v (.values vs f as) = some a) :
    joinDrivable as = true ∧ joinDrivable vs = true ∧
      a.vars = (Pattern.values vs f as).freeVars d.env ∧ a.keys = as ∧ a.outs = vs ∧
      d.holdsAll ((joinKnown (d.env ++ Env.canon a.vars pre) as).filterMap id) = true ∧
      d.holdsAll ((joinKnown (d.env ++ Env.canon a.vars pre) vs).filterMap id) = true ∧
      ∀ r ∈ d.rows, r.fn = f →
        joinConsistent cl (joinKnown (d.env ++ Env.canon a.vars pre) as) r.args = true →
        joinConsistent cl (joinKnown (d.env ++ Env.canon a.vars pre) vs) r.out = true →
        r ∈ a.rows := by
  simp only [joinPlan] at h
  split at h
  · rename_i hg
    split at h
    · rename_i hh
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hg
      refine ⟨hg.1.1.2, hg.1.2, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · refine holdsAll_of_forall fun z hz => holdsAll_of_mem hh ?_
        simp only [List.filterMap_append]
        exact List.mem_append_left _ hz
      · refine holdsAll_of_forall fun z hz => holdsAll_of_mem hh ?_
        simp only [List.filterMap_append]
        exact List.mem_append_right _ hz
      · intro r hr hf h1 h2
        exact List.mem_filter.mpr ⟨hr, by simp [hf, h1, h2]⟩
    · simp at h
  · simp at h

/-- What `patternHoldsWith` promises at a **merge function's** entry atom. -/
private theorem patternHoldsWith_values {cl : Finset (Term × Term)} {d : FDatabase}
    {vs as : List Expr} {f : FnName} {σ : Env} (hm : (d.sig.mergeOf f).isSome = true)
    (h : patternHoldsWith cl d (.values vs f as) σ = true) :
    ∃ us ks, Expr.evalList d.sig vs (d.env ++ σ) = some us ∧
      Expr.evalList d.sig as (d.env ++ σ) = some ks ∧
      ∃ r ∈ d.rows, r.fn = f ∧
        FDatabase.congrTuple (d.closureWith cl (ks ++ us)) ks r.args = true ∧
        FDatabase.congrTuple (d.closureWith cl (ks ++ us)) us r.out = true := by
  simp only [patternHoldsWith] at h
  cases hv : Expr.evalList d.sig vs (d.env ++ σ) with
  | none => rw [hv] at h; simp at h
  | some us =>
    cases ha : Expr.evalList d.sig as (d.env ++ σ) with
    | none => rw [hv, ha] at h; simp at h
    | some ks =>
      rw [hv, ha] at h
      simp only [hm, if_pos, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨r, hr, ⟨hf, h1⟩, h2⟩ := h
      exact ⟨us, ks, rfl, rfl, r, hr, hf, h1, h2⟩

/-- **The narrowing keeps every candidate a full substitution supports.** -/
theorem joinCands_mem {cl : Finset (Term × Term)} {d : FDatabase} {q : Query} {held : Bool}
    {ts : List Term} {pre : Env} {v : Var} {t : Term} {σ : Env}
    (hheld : held = true → ∀ u ∈ ts, d.holdsAll [u] = true)
    (htm : t ∈ ts) (hσ : ∀ b ∈ σ, b.2 ∈ ts)
    (hall : (q.all fun p => patternHoldsWith cl d p
        (Env.canon (p.freeVars d.env) (pre ++ [(v, t)] ++ σ))) = true) :
    t ∈ joinCands cl d q held ts pre v := by
  simp only [joinCands]
  split
  · rename_i hb
    refine List.mem_filter.mpr ⟨htm, List.all_eq_true.mpr fun a ha => ?_⟩
    have ha' : a ∈ q.filterMap (joinPlan cl d pre v) :=
      ((List.mergeSort_perm _ _).mem_iff).mp ha
    obtain ⟨p, hp, hpa⟩ := List.mem_filterMap.mp ha'
    have hph := List.all_eq_true.mp hall p hp
    match p, hpa, hph with
    | .expr _, hpa, _ => simp [joinPlan] at hpa
    | .eq _ _, hpa, _ => simp [joinPlan] at hpa
    | .values vs f as, hpa, hph =>
      obtain ⟨hda, hdv, hav, hak, hao, hka, hkv, hrow⟩ := joinPlan_values hpa
      have hm : (d.sig.mergeOf f).isSome = true := by
        simp only [joinPlan] at hpa
        split at hpa
        · rename_i hg; simp only [Bool.and_eq_true] at hg; exact hg.1.1.1
        · simp at hpa
      obtain ⟨us, ks, hev, hek, r, hr, hrf, hcm1, hcm2⟩ := patternHoldsWith_values hm hph
      -- the three environments: the node's, the candidate's, and the full substitution's
      set vars := (Pattern.values vs f as).freeVars d.env with hvars
      set ρ₀ := d.env ++ Env.canon vars pre with hρ₀
      set ρ₁ := d.env ++ Env.canon vars (pre ++ [(v, t)]) with hρ₁
      set ρ₂ := d.env ++ Env.canon vars (pre ++ [(v, t)] ++ σ) with hρ₂
      have mono₀ : ∀ w y, Env.lookup w ρ₀ = some y → Env.lookup w ρ₂ = some y := by
        rw [hρ₀, hρ₂]
        exact lookup_canon_mono fun w y hw => lookup_append_some (lookup_append_some hw)
      have mono₁ : ∀ w y, Env.lookup w ρ₁ = some y → Env.lookup w ρ₂ = some y := by
        rw [hρ₁, hρ₂]
        exact lookup_canon_mono fun w y hw => lookup_append_some hw
      have hnew : ∀ w y, Env.lookup w ρ₀ = none → Env.lookup w ρ₂ = some y →
          d.holdsAll [y] = true := by
        intro w y h0 h2
        have hE : Env.lookup w d.env = none := by
          cases hE : Env.lookup w d.env with
          | none => rfl
          | some z => rw [hρ₀, lookup_append_some hE] at h0; simp at h0
        rw [hρ₀, lookup_append_none hE, Env.lookup_canon_eq] at h0
        rw [hρ₂, lookup_append_none hE, Env.lookup_canon_eq] at h2
        by_cases hmv : w ∈ vars
        · rw [if_pos hmv] at h0 h2
          rw [List.append_assoc, lookup_append_none h0, List.singleton_append,
            Env.lookup] at h2
          by_cases hwv : w = v
          · rw [if_pos hwv, Option.some.injEq] at h2
            subst h2; exact hheld hb t htm
          · rw [if_neg hwv] at h2
            exact hheld hb y (hσ (w, y) (mem_of_lookup h2))
        · rw [if_neg hmv] at h2; simp at h2
      -- every operand's value is held, so the atom's closure is the one the filter used
      have hks : ∀ x ∈ ks, d.holdsAll [x] = true := by
        rw [hav] at hka
        exact joinKnown_holds mono₀ hnew hda hek hka
      have hus : ∀ x ∈ us, d.holdsAll [x] = true := by
        rw [hav] at hkv
        exact joinKnown_holds mono₀ hnew hdv hev hkv
      have hcl : d.closureWith cl (ks ++ us) = cl := by
        rw [FDatabase.closureWith, if_pos]
        refine holdsAll_of_forall fun x hx => ?_
        rcases List.mem_append.mp hx with hx | hx
        · exact hks x hx
        · exact hus x hx
      rw [hcl] at hcm1 hcm2
      -- the row survives the prefix, so it is one of the atom's, and it admits `t`
      have hin : r ∈ a.rows := by
        refine hrow r hr hrf ?_ ?_
        · rw [hav]
          exact joinConsistent_of_congrTuple mono₀ hda hek hcm1
        · rw [hav]
          exact joinConsistent_of_congrTuple mono₀ hdv hev hcm2
      refine List.any_eq_true.mpr ⟨r, hin, ?_⟩
      rw [hak, hao, hav]
      refine Bool.and_eq_true .. ▸ ⟨?_, ?_⟩
      · exact joinConsistent_of_congrTuple mono₁ hda hek hcm1
      · exact joinConsistent_of_congrTuple mono₁ hdv hev hcm2
  · exact htm

/-- `filter` past a `flatMap` that is empty wherever the filter rejects. -/
private theorem flatMap_filter_eq {α β : Type} (P : α → Bool) (F : α → List β) :
    ∀ l : List α, (∀ t ∈ l, P t = false → F t = []) →
      (l.filter P).flatMap F = l.flatMap F := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    by_cases hx : P x
    · simp only [List.filter_cons, if_pos hx, List.flatMap_cons]
      rw [ih fun t ht => h t (List.mem_cons_of_mem _ ht)]
    · simp only [Bool.not_eq_true] at hx
      rw [List.filter_cons, if_neg (by simp [hx]), List.flatMap_cons,
        h x List.mem_cons_self hx, List.nil_append]
      exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- **The join is the pruned enumeration**, on the nose: the same substitutions, in the
same order. -/
theorem matchJoin_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query)
    (ts : List Term) (held : Bool) (hheld : held = true → ∀ u ∈ ts, d.holdsAll [u] = true) :
    ∀ (vs : List Var) (pre : Env),
      matchJoin cl d q ts held pre vs = matchPrune cl d q ts pre vs := by
  intro vs
  induction vs with
  | nil => intro pre; rfl
  | cons v vs ih =>
    intro pre
    rw [matchJoin, matchPrune]
    simp only [ih]
    simp only [joinCands]
    split
    · rename_i hb
      refine flatMap_filter_eq _ _ ts fun t ht hp => ?_
      split
      · rename_i hg
        refine List.map_eq_nil_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun τ hτ => ?_)
        rw [matchPrune_eq] at hτ
        obtain ⟨hτa, hτp⟩ := List.mem_filter.mp hτ
        have := joinCands_mem (held := held) hheld ht (assignments_snd hτa) hτp
        simp only [joinCands, if_pos hb, List.mem_filter] at this
        rw [this.2] at hp
        exact Bool.noConfusion hp
      · rfl
    · rfl

/-- `matchQueryWith`, joined. `d.holdsAll d.valueTerms` is computed **once** here rather
than at every node, which is the reason `matchJoin` takes it as a parameter. -/
def matchQueryJoin (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  matchJoin cl d q d.valueTerms (d.holdsAll d.valueTerms) [] (Query.freeVars q d.env)

theorem matchQueryJoin_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) :
    matchQueryJoin cl d q = matchQueryWith cl d q := by
  rw [matchQueryJoin,
    matchJoin_eq cl d q d.valueTerms (d.holdsAll d.valueTerms)
      (fun h u hu => holdsAll_of_mem h hu)]
  exact matchQueryPruned_eq cl d q

/-- **The join is `matchQuery`**: at `d`'s own closure it produces the same substitutions,
in the same order, binding the same variables in the same order. Not up to `Env.Agree`, not
up to permutation — which is what lets every theorem in `Proofs/` keep its statement and its
proof while the executable changes underneath. -/
theorem matchQueryJoin_eq_matchQuery (d : FDatabase) (q : Query) :
    matchQueryJoin d.closureF d q = matchQuery d q :=
  (matchQueryJoin_eq d.closureF d q).trans (matchQueryWith_eq d q)

/-- **What points compiled code at the join** — every caller of `matchQueryWith`, which
after the `csimp` below is every caller of `matchQuery` too. `matchQueryPruned` is a step in
its equality rather than a rival: `matchJoin` runs `matchPrune`'s enumeration and checks
what it checks, and only the candidate list at each node is different. -/
@[csimp] theorem matchQueryWith_eq_join : @matchQueryWith = @matchQueryJoin := by
  funext cl d q
  exact (matchQueryJoin_eq cl d q).symm

/-- What points compiled code at the fast path. `execRunRulesFast` below shares one closure
across a round's rules and so calls `matchQueryWith` directly; this is what every *other*
caller of `matchQuery` gets. -/
@[csimp] theorem matchQuery_eq_matchQueryFast : @matchQuery = @matchQueryFast := by
  funext d q
  exact (matchQueryFast_eq d q).symm

/-! ### Running -/
/-- `evalAction`, computed. -/
def execAction (d : FDatabase) : Action → Option FDatabase
  | .expr e => (e.eval d.sig d.env).map fun t => d.addTerm t
  | .letBind v e => (e.eval d.sig d.env).map fun t =>
      { d.addTerm t with env := (v, t) :: d.env }
  | .union e₁ e₂ =>
      (e₁.eval d.sig d.env).bind fun t₁ => (e₂.eval d.sig d.env).bind fun t₂ =>
        if t₁.isLit || t₂.isLit then none else some (d.addEq t₁ t₂)
  | .set f args out => (Expr.evalList d.sig args d.env).bind fun as =>
      (Expr.evalList d.sig out d.env).map fun vs => d.addRow f as vs

/-- `evalActions`, computed. -/
def execActions (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (execAction d a).bind fun d' => execActions d' as

/-- `evalLocalActions`, computed. -/
def execLocalActions (d : FDatabase) (as : List Action) (σ : Env) : Option FDatabase :=
  (execActions { d with env := d.env ++ σ } as).map fun d' =>
    { d' with env := d.env, rules := d.rules }

/-- One firing of `r` on `σ`, unioned into `acc`; nothing if the actions get stuck, which
for a well-scoped rule they do not. -/
def fireInto (d : FDatabase) (r : Rule) (acc : FDatabase) (σ : Env) : FDatabase :=
  match execLocalActions d r.actions σ with
  | some d' => acc.union d'
  | none => acc

/-- Every firing of `r`, unioned into `acc`. -/
def fireRule (d : FDatabase) (acc : FDatabase) (r : Rule) : FDatabase :=
  (matchQuery d r.query).foldl (fireInto d r) acc

/-- One round of the ruleset `R`: every rule *of `R`* on every matching substitution, all
read off the pre-state. -/
def execRunRules (R : RulesetName) (d : FDatabase) : FDatabase :=
  (d.rules.filter fun r => r.ruleset == R).foldl (fireRule d) d

/-! #### One closure per round

Every rule of a round matches against the *same* pre-state, so the closure
`matchQueryFast` computes once per query can be computed once per **round** instead. On the
encoded `both-2` at 53 terms that is 0.5 s per rule against six rules a round. Same
discipline as above: `execRunRules`' definition is untouched and `csimp` is what redirects
the executable. -/
/-- `fireRule` with the closure taken as a parameter. -/
def fireRuleWith (cl : Finset (Term × Term)) (d : FDatabase) (acc : FDatabase) (r : Rule) :
    FDatabase :=
  (matchQueryWith cl d r.query).foldl (fireInto d r) acc

theorem fireRuleWith_eq (d : FDatabase) : fireRuleWith d.closureF d = fireRule d := by
  funext acc r
  simp only [fireRuleWith, fireRule, matchQueryWith_eq]

/-- **The fast round.** One congruence closure, shared by every rule of the ruleset. -/
def execRunRulesFast (R : RulesetName) (d : FDatabase) : FDatabase :=
  (d.rules.filter fun r => r.ruleset == R).foldl (fireRuleWith d.closureF d) d

theorem execRunRulesFast_eq (R : RulesetName) (d : FDatabase) :
    execRunRulesFast R d = execRunRules R d := by
  rw [execRunRulesFast, execRunRules, fireRuleWith_eq]

@[csimp] theorem execRunRules_eq_execRunRulesFast : @execRunRules = @execRunRulesFast := by
  funext R d
  exact (execRunRulesFast_eq R d).symm

/-- Whether two states agree on the fields a round can change. `sig` is a function, and
`env`/`rules` no round touches. -/
def FDatabase.sameData (d e : FDatabase) : Bool :=
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs

/-- Rounds of `R`, as a relation to descend: `x` is the round after `y`, and `y` had not
settled. It is well founded at `d` exactly when `R` saturates from `d`. -/
def FDatabase.RunRel (R : RulesetName) (x y : FDatabase) : Prop :=
  execRunRules R y = x ∧ ¬ y.sameData (execRunRules R y) = true

/-- Rounds of `R` until nothing changes. Takes a **termination witness**, not fuel, so it is
total on the states where the ruleset saturates and loses nothing — `Impl/Merge.lean`'s
`mergeSaturate` pattern, one level up. `exec` runs `runSaturateF` instead, because no
witness is available at runtime: whether a ruleset saturates at a given state is not
something the caller can supply. -/
def FDatabase.runSaturate (R : RulesetName) (d : FDatabase)
    (h : Acc (FDatabase.RunRel R) d) : FDatabase :=
  Acc.rec (motive := fun _ _ => FDatabase)
    (fun x _ ih =>
      if he : x.sameData (execRunRules R x) = true then x
      else ih (execRunRules R x) ⟨rfl, he⟩) h

/-- Rounds of `R` until nothing changes, bounded by fuel that **fails** rather than
returning a prefix — `Impl/Merge.lean`'s `mergeSaturateF` pattern, one level up and for
its reason: a ruleset that really does diverge makes the run `none`, which the difftest
reports as a mismatch, rather than presenting a half-run state as a saturation.

This is what `exec` runs, and `runSaturateF_eq_runSaturate` is the price: it agrees with
`runSaturate` whenever it answers at all, and answers less often. -/
def FDatabase.runSaturateF (R : RulesetName) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (execRunRules R d) then some d else none
  | n + 1, d =>
      if d.sameData (execRunRules R d) then some d
      else FDatabase.runSaturateF R n (execRunRules R d)

/-- `runSaturateF` with the round computed **once**. Its `n + 1` branch names
`execRunRules R d` twice, which the compiler has no reason to share, so every non-final
round of a saturation was searched twice over. -/
def FDatabase.runSaturateFast (R : RulesetName) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (execRunRules R d) then some d else none
  | n + 1, d =>
      let e := execRunRules R d
      if d.sameData e then some d else FDatabase.runSaturateFast R n e

theorem FDatabase.runSaturateFast_eq (R : RulesetName) (n : Nat) (d : FDatabase) :
    FDatabase.runSaturateFast R n d = FDatabase.runSaturateF R n d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [FDatabase.runSaturateFast, FDatabase.runSaturateF, ih]

@[csimp] theorem FDatabase.runSaturateF_eq_fast :
    @FDatabase.runSaturateF = @FDatabase.runSaturateFast := by
  funext R n d
  exact (FDatabase.runSaturateFast_eq R n d).symm

/-- Rounds a run allows before declaring a ruleset divergent. Unlike `mergeFuel` this
bounds no structural quantity: rounds add terms rather than shrink a class, so a
terminating ruleset can need arbitrarily many and `exec_programStep` has to say so. -/
def runFuel : Nat := 64

/-- `CmdStep`, computed. -/
def execCmd (d : FDatabase) : Cmd → Option FDatabase
  | .action a => execAction d a
  | .rule r => some { d with rules := r :: d.rules }
  | .run R => some (execRunRules R d)
  | .saturate R => d.runSaturateF R runFuel
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- `ProgramStep`, computed. -/
def execProgram (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | c :: cs => (execCmd d c).bind fun d' => execProgram d' cs

/-- Run a program from the initial database. -/
def exec (p : Program) : Option FDatabase := execProgram FDatabase.empty p

/-- What one firing contributes. -/
def Fired (d : FDatabase) (r : Rule) (σ : Env) (d' : FDatabase) : Prop :=
  execLocalActions d r.actions σ = some d'

/-! ### Row counts

What `egglog/tests/files.rs` snapshots is one row per distinct *canonical* argument
tuple. On this side that is the number of congruence classes of `f`-applications, which
is what a differential test compares. -/
/-- Whether two argument lists are pointwise related by `cl`. -/
def congrArgs (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- The argument lists of `d`'s `f`-applications, which for a **constructor** are its
entries' key tuples. -/
def FDatabase.argLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.terms.filterMap fun t =>
    match t with
    | .app g as => if g = f then some as else none
    | _ => none

/-- The number of rows egglog's table for a **constructor** `f` would hold: one per
congruence class of argument lists. Each list is mapped to its whole class and the
distinct classes counted, so no representative has to be chosen — there is no order on
`Term` to choose one by.

Constructors only. A merge function's entry term is `f(a…, v…)`, so `argLists` returns
key *and* value columns for one and this would count classes of the pair rather than rows
of the table. `Impl/Merge.lean`'s `keyRowCount` is the one that reads the index and counts
key classes; it agrees with this on a constructor and is what the differential test
runs. -/
def FDatabase.rowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let args := (d.argLists f).toFinset
  (args.image fun as => args.filter fun bs => congrArgs cl as bs).card

/-- The per-function row counts, as `files.rs` prints them. -/
def FDatabase.rowCounts (d : FDatabase) (fs : List FnName) : List (FnName × Nat) :=
  fs.map fun f => (f, d.rowCount f)

end Egglog
