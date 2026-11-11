import EgglogSemantics.Slotted.Target.Values
import Mathlib.Data.List.Defs

/-!
# The primitive catalogue

The computations the paper's slotted rules use, as functions on the canonical values of
`Values.lean`: the renaming algebra (`img`, `dom`, `⁻¹`, `∘`, `|_A`, `id_A`, application),
the slot set algebra, `Perm`, the Collide union `align`, the Migrate extension `extend`, the
binder name `mint`, the successor `succ` of a row generation, finite permutations for membership witnesses, and the e-matching operations `fresh`, `distinct`/`cliques`, `identity`, `unify`,
`final-refine` and `anchor` over frames. A **frame** is a renaming on
placeholders that sends each placeholder to the least member of its block; the cliques are a
list of slot sets whose members must stay in distinct blocks.

`Prim.eval` evaluates one application of a primitive name to canonical arguments, `none`
off its domain; `Prim.norm?` is the primitive step, reducing every primitive application of a
term bottom-up; `Prim.elements` reads a set-valued result for the membership pattern.
-/

namespace Egglog.Slotted.Target

/-! ### Slot set and renaming operations on decoded values -/

def setUnion (A B : List Slot) : SlotSet := canonSlots (A ++ B)
def setInter (A B : List Slot) : SlotSet := canonSlots (A.filter (· ∈ B))
def setDiff (A B : List Slot) : SlotSet := canonSlots (A.filter (· ∉ B))

/-- Two renamings denote the same function. -/
def renEq (m m' : Renaming) : Bool := encodeRen m == encodeRen m'

/-- `π ∈ Perm(A)`: a well-formed renaming with domain and image `A`. -/
def isPerm (π : Renaming) (A : List Slot) : Bool :=
  decide π.WF && canonSlots π.dom == canonSlots A && canonSlots π.img == canonSlots A

/-- The union of renamings, defined when they agree on common keys and the result is
injective: the correspondence the Collide rule assembles from its children. -/
@[blueprint "def:slotted-align"
  (statement := /--
  \[
  \operatorname{align}(m_1,\ldots,m_n)=\textstyle\bigcup_i m_i
  \quad\text{if this union is a partial injection; undefined otherwise.}
  \]
  -/)
  (latexEnv := "paperfragment")]
def align (ms : List Renaming) : Option Renaming :=
  ms.flatten.foldlM (fun acc p =>
    match acc.apply p.1 with
    | some v => if v = p.2 then some acc else none
    | none => if p.2 ∈ acc.img then none else some (acc ++ [p])) []

/-- `extend(m, S, B)`: `m` extended to every slot of `S`, the new keys receiving the least
canonical names outside `img(m) ∪ B` and each other. -/
def extend (m : Renaming) (S B : List Slot) : Renaming :=
  let missing := (canonSlots S).filter (· ∉ m.dom)
  m ++ missing.zip (freshNames missing.length (m.img ++ B))

/-- `mint(L)`: the least canonical name outside `L`, for a binder refreshed in a node. -/
def mint (L : List Slot) : Slot := (freshNames 1 L).headD (canonicalName 0)

/-- Every permutation of the finite support. The compiler materializes membership
witnesses for these maps so ordinary target disequality can test symmetry nonmembership. -/
def permutations (A : List Slot) : List Renaming :=
  let A := canonSlots A
  A.permutations.map (A.zip ·)

/-! ### Frames -/

/-- The block of a placeholder: its representative under the frame, itself if unknown. -/
def frameRep (F : Renaming) (p : Slot) : Slot := (F.apply p).getD p

/-- Merge the blocks of two placeholders, keeping the smaller representative. -/
def frameMerge (F : Renaming) (a b : Slot) : Renaming :=
  let ra := frameRep F a
  let rb := frameRep F b
  if ra = rb then F else
    let lo := if decide (ra ≤ rb) then ra else rb
    let hi := if decide (ra ≤ rb) then rb else ra
    F.map fun pr => (pr.1, if pr.2 = hi then lo else pr.2)

/-- No clique has two members in one block. -/
def frameConsistent (F : Renaming) (C : List (List Slot)) : Bool :=
  C.all fun K => (K.dedup.map (frameRep F)).dedup.length == K.dedup.length

/-- Merge the pairs in turn and check the cliques; the placeholders must be known. -/
def unifyPairs (F : Renaming) (pairs : List (Slot × Slot)) (C : List (List Slot)) :
    Option Renaming :=
  if pairs.all (fun p => p.1 ∈ F.dom && p.2 ∈ F.dom) then
    let F' := pairs.foldl (fun acc p => frameMerge acc p.1 p.2) F
    if frameConsistent F' C then some F' else none
  else none

/-- `unify(F, m, m′, C)`: identify `m(t)` with `m′(t)` for every common key `t`. -/
def unify (F : Renaming) (m m' : Renaming) (C : List (List Slot)) : Option Renaming :=
  unifyPairs F (m.dom.filterMap fun t => do pure (← m.apply t, ← m'.apply t)) C

/-- The set partitions of a list. -/
def partitions {α : Type} : List α → List (List (List α))
  | [] => [[]]
  | x :: xs => (partitions xs).flatMap fun P => ([x] :: P) :: insertions x P
where
  /-- `x` put into one of the groups. -/
  insertions (x : α) : List (List α) → List (List (List α))
    | [] => []
    | g :: gs => ((x :: g) :: gs) :: (insertions x gs).map (g :: ·)

/-- `final-refine(F, C, D)`: every consistent coarsening of `F` that merges blocks touched by
`D`, the frame itself first. -/
def refine (F : Renaming) (C : List (List Slot)) (D : List Slot) : List Renaming :=
  let touched := canonSlots (D.map (frameRep F))
  (partitions touched).filterMap fun P =>
    let F' := P.foldl (fun acc g => match g with
      | [] => acc
      | r :: rs => rs.foldl (fun acc' r' => frameMerge acc' r r') acc) F
    if frameConsistent F' C then some F' else none

/-- `anchor(q, ν)`: name the blocks of the frame `q`, giving the block of `ν(s)` the name
`s` and every other block a fresh canonical name outside `dom(ν)`. -/
def anchor (q : Renaming) (ν : Renaming) : Option Renaming := do
  let A := ν.dom
  let named ← ν.foldlM (fun (acc : List (Slot × Slot)) sp =>
    if sp.2 ∈ q.dom then
      let r := frameRep q sp.2
      match acc.lookup r with
      | some s => if s = sp.1 then some acc else none
      | none => some (acc ++ [(r, sp.1)])
    else none) []
  let reps := canonSlots q.img
  let unnamed := reps.filter fun r => (named.lookup r).isNone
  let fresh := freshNames unnamed.length (A ++ named.map Prod.snd)
  let names := named ++ unnamed.zip fresh
  q.mapM fun pr => (names.lookup pr.2).map fun s => (pr.1, s)

/-! ### The catalogue -/

/-- The names of the primitive functions, including the value heads. -/
def primNames : List FnName :=
  [setName, renName, pairName, rensName, setsName, trueName, falseName,
   "@img", "@dom", "@inv", "@comp", "@restrict", "@id", "@apply",
   "@union", "@inter", "@diff", "@elem", "@isPerm", "@align", "@extend", "@mint", "@succ",
   "@perms", "@fresh", "@cliques", "@identity", "@unify", "@unify1", "@refine",
   "@anchor"]

/-- Whether a head is a primitive. -/
def isPrimName (f : FnName) : Bool := f ∈ primNames

namespace Prim

/-- One application of a primitive to canonical arguments; `none` off its domain. -/
def eval (f : FnName) (args : List Term) : Option Term :=
  if f = setName then (args.mapM decodeSlot).map encodeSet
  else if f = pairName then
    match args with
    | [a, b] => do let _ ← decodeSlot a; let _ ← decodeSlot b; pure (.app pairName [a, b])
    | _ => none
  else if f = renName then do
    -- A frame is a renaming value too, and frames are not injective: only functionality is
    -- required of the value form.
    let m : Renaming ← args.mapM decodePair
    if (m.map Prod.fst).Nodup then pure (encodeRen m) else none
  else if f = rensName then (args.mapM decodeRen).map encodeRens
  else if f = setsName then (args.mapM decodeSet).map encodeSets
  else if f = trueName || f = falseName then if args.isEmpty then some (.app f []) else none
  else match f, args with
  | "@img", [m] => (decodeRen m).map fun m => encodeSet m.img
  | "@dom", [m] => (decodeRen m).map fun m => encodeSet m.dom
  | "@inv", [m] => do
      let m ← decodeRen m
      if m.WF then pure (encodeRen m.inv) else none
  | "@comp", [m, m'] => do pure (encodeRen ((← decodeRen m).comp (← decodeRen m')))
  | "@restrict", [m, A] => do pure (encodeRen ((← decodeRen m).restrict (← decodeSet A)))
  | "@id", [A] => (decodeSet A).map fun A => encodeRen (Renaming.id (canonSlots A))
  | "@apply", [m, s] => do pure (Term.slot (← (← decodeRen m).apply (← decodeSlot s)))
  | "@union", [A, B] => do pure (encodeSet (setUnion (← decodeSet A) (← decodeSet B)))
  | "@inter", [A, B] => do pure (encodeSet (setInter (← decodeSet A) (← decodeSet B)))
  | "@diff", [A, B] => do pure (encodeSet (setDiff (← decodeSet A) (← decodeSet B)))
  | "@elem", [s, A] => do pure (encodeBool (decide ((← decodeSlot s) ∈ (← decodeSet A))))
  | "@isPerm", [π, A] => do pure (encodeBool (isPerm (← decodeRen π) (← decodeSet A)))
  | "@align", ms => do pure (encodeRen (← align (← ms.mapM decodeRen)))
  | "@extend", [m, S, B] => do
      let m ← decodeRen m
      if m.WF then pure (encodeRen (extend m (← decodeSet S) (← decodeSet B))) else none
  | "@mint", [L] => (decodeSet L).map fun L => Term.slot (mint L)
  | "@succ", [.lit (.int k)] => some (.lit (.int (k + 1)))
  | "@perms", [A] => (decodeSet A).map fun A => encodeRens (permutations A)
  | "@fresh", [S, U] => do
      let S := canonSlots (← decodeSet S)
      pure (encodeRen (S.zip (freshPlaceholders S.length (← decodeSet U))))
  | "@cliques", As => (As.mapM decodeSet).map encodeSets
  | "@identity", [A] => (decodeSet A).map fun A => encodeRen (Renaming.id (canonSlots A))
  | "@unify", [F, m, m', C] => do
      pure (encodeRen (← unify (← decodeRen F) (← decodeRen m) (← decodeRen m') (← decodeSets C)))
  | "@unify1", [F, p, p', C] => do
      pure (encodeRen (← unifyPairs (← decodeRen F) [(← decodeSlot p, ← decodeSlot p')]
        (← decodeSets C)))
  | "@refine", [F, C, D] => do
      pure (encodeRens (refine (← decodeRen F) (← decodeSets C) (← decodeSet D)))
  | "@anchor", [q, ν] => do pure (encodeRen (← anchor (← decodeRen q) (← decodeRen ν)))
  | _, _ => none

/-- The elements a set-valued result ranges over: the renamings of a list, the slots of a
set. -/
def elements : Term → Option (List Term)
  | .app f args => if f = rensName || f = setName then some args else none
  | _ => none

mutual

/-- The primitive step: every primitive application reduced to its value, bottom-up. -/
def norm? : Term → Option Term
  | .lit l => some (.lit l)
  | .app f args =>
    (normList? args).bind fun args' => if isPrimName f then eval f args' else some (.app f args')

def normList? : List Term → Option (List Term)
  | [] => some []
  | t :: ts => (norm? t).bind fun t' => (normList? ts).map (t' :: ·)

end

end Prim

end Egglog.Slotted.Target
