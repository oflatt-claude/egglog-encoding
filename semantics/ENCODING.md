# M11, the proof encoding — parked

`Encoding/Encode.lean` defines the encoding. Its theorems and their vacuity witnesses are
**deleted**; this file is what survives of them, and it exists so the design is not
re-attempted with the same defects.

The Lean is recoverable at commit `0836127`:

```
git show 0836127:semantics/EgglogSemantics/Encoding/Proofs.lean   # 13 statements, all sorry
git show 0836127:semantics/EgglogSemantics/Encoding/Rebuilt.lean  # the vacuity witnesses
```

They were deleted rather than carried through the `Spec/` simplification work: both are
row-shaped throughout — `Spec/` has no rows now, a function entry is a term — the
statements are known defective, and porting proofs of nothing is not worth the maintenance.

## Two findings, both machine-checked before deletion

### 1. `Rebuilt` is unsatisfiable at the states `encode` runs to

`Rebuilt P d` is the saturation hypothesis `encode_complete`, `encode_simulation` and
`encode_simulation_of_domain` all carry. It is satisfiable for some states and not for the ones
that matter. Two source programs differing only in *which* term is built:

* `P₁ = (f 1) (union 1 2)` — the union's larger endpoint `2` is not a view key, so the
  rebuild has nothing to move. `Rebuilt P₁ d₁` holds.
* `P₀ = (f 2) (union 1 2)` — the larger endpoint **is** the view key. The column-0 rebuild
  rule has a firing that writes a row the state lacks, and neither an action nor a merge
  step can ever write it, because `encode P₀` emits no `Cmd.run`. `¬ Rebuilt P₀ d₀`.

The general form: **any** state satisfying `Rebuilt` must already hold every re-keyed view
row. A hypothesis nothing reachable satisfies makes the three theorems it guards vacuous.

**The recorded fix does not work.** Appending `(run)` to `encode`'s output does not
suffice: the number of rounds needed to re-key grows with term depth, so no fixed number
of `(run)` commands saturates for all inputs. A correct fix has to either run to
saturation or state completeness against a genuinely reachable condition.

### 2. `CongOn` cannot express existence

`CongOn db ts a b` is definitionally `Cong (db.addTerms ts) a b`, so
`CongOn db [a, a] a a` holds for **every** database and **every** term — no
well-formedness, no membership, no signature, no program. The witness, `congOn_refl`, was one
line.

**It survived `Cong` losing its `refl` rule**, which is worth checking rather than
assuming, since that deletion is what re-examined every other reflexivity guard
(`Scratch/NonVacuity.lean`). `Database.addTerm` writes a reflexive *equation* per subterm,
so `(a, a) ∈ (db.addTerms [a, a]).eqs` and `Cong.assert` reads it straight back.

Five of the M11 statements conclude `CongOn`, so each says nothing wherever its two terms
coincide. That is not a corner case. `encodeBuild` emits
`.set (viewName f) es [.app f es]` — an **identity** view row, key and output denoting the
same term — for every application it encodes. So `encode_rows_sound`'s second conjunct, at
the most common row in the target, reduces to `congOn_refl` and is dischargeable without
looking at the source, the program, the target, or the row. Likewise
`encode_proof_view_rows_check` at a two-column identity row, and
`encode_rows_sound`'s first conjunct at a `@UF` row whose key is its own parent — which
every interned term is until something unions it.

**Do not "fix" this by replacing `CongOn` with `Cong`.** `CongOn` is the right relation
for the job it was introduced for: after `(Add 1 2)` and `(union 1 2)` the rebuild re-keys
`@AddView [1,1] ↦ Add[1,2]`, and `CongOn src [Add 1 1, Add 1 2] (Add 1 1) (Add 1 2)` is a
true, non-vacuous claim that `Cong src` cannot even state, because `Add 1 1` was never
built and every term `Cong src` relates is one `src` holds (`eqsInTerms_free`). The defect
is confined to the diagonal. Two repairs that keep what `CongOn` is for:

* **conjoin membership** — `k ∈ src.terms ∧ p ∈ src.terms ∧ Cong src k p`. This is what
  makes the diagonal say something, and it is now *definitional*: `Database.terms` is
  `{t | Cong db t t}`, so `Cong src a a` and `a ∈ src.terms` are the same proposition.
* **split the cases** — `CongOn` only where the rebuild has re-keyed, `Cong` elsewhere.

## The lesson worth keeping

Both defects were invisible while the statements carried `sorry`. A statement nothing
discharges can be trivially true without anyone noticing, and two of thirteen were. Before
proving an M11 statement, check that it is not already provable for the wrong reason —
`#print axioms` on a hypothesis-free proof of the conclusion is the cheap test.

A third of the same kind is recorded but unswept: the remaining eleven statements were
never checked for vacuity.

## What survives

`Encoding/Encode.lean` — `encode`, `encodeBuild`, `maintenanceRules`, `Rebuilt`,
`EncodeDomain`, `viewName`/`termName`/`ufName`. The encoder's definitions are unchanged and
depend on none of the deleted files. Note that `Rebuilt` as defined there is the predicate
finding 1 refutes; it is kept because re-deriving M11 will want to state something in its
place, not because it is right, and its docstring now says so.

**A third obstacle, not a defect of these statements but of what they are stated over.**
`mergeBody`/`mergeResult` — the `:merge` shared by `@UF` and every view — are built from
`ordering-min`/`ordering-max`, and those are **not congruence-stable** in this model, because
`Term.blt` is a structural order and no function of the term can be. A simulation theorem has to
either carry that as a hypothesis or restrict its transported positions to primitive-free
expressions; it is already blocking two `sorry`s in `Proofs/Merge.lean`. `MERGE.md`, "The
representative deviation".

**The M11 side condition, restated.** `encode` emits no `union`, so the target asserts no
equality between distinct terms — which used to be written "`Cong` on the target degenerates
to syntactic equality". That is wrong now, and it is the cheap kind of wrong to leave lying
around: `Cong` has no `refl` rule, so the target relation is the **identity on the terms the
target holds**, and it relates nothing else at all. The condition still holds exactly, and
for one less reason than before — `Cong` reads `eqs` and nothing else, so no table of the
target can add a derivation. Checked by reading the encoder: it emits only `.set` and
`.letBind`, never `.union`, so from `Database.empty` the target's `eqs` really is
diagonal-only. Any restatement gets this for free; it is the one M11 side condition that
survived both the congruence collapse and the deletion.

The proof checker was never written. `CHECKER.md` scopes it; `Checks` was an opaque
stand-in in the deleted statements.
