import EgglogSemantics.SourceProof.Checker

namespace Egglog.Resugar

open SourceProof (Claim Node Certificate Context)

structure Builder where
  nodes : List Node := []

def Builder.claims (b : Builder) : List Claim := b.nodes.map Node.claim

def Builder.find (b : Builder) (c : Claim) : Option Nat :=
  (b.nodes.zipIdx.find? fun ni => ni.1.claim == c).map Prod.snd

/-- Reuse established claims; validate each new source justification. -/
def Builder.add (P : Program) (C : Context) (b : Builder)
    (c : Claim) (reason : SourceProof.Reason) : Option (Nat × Builder) :=
  match b.find c with
  | some i => some (i, b)
  | none =>
    let n : Node := ⟨c, reason⟩
    if SourceProof.checkNode P C b.claims n then
      some (b.nodes.length, ⟨b.nodes ++ [n]⟩)
    else none

def Builder.symm (P : Program) (C : Context) (b : Builder) (i : Nat) :
    Option (Nat × Builder) := do
  let c ← b.claims[i]?
  b.add P C ⟨c.rhs, c.lhs⟩ (.symm i)

def Builder.trans (P : Program) (C : Context) (b : Builder) (i j : Nat) :
    Option (Nat × Builder) := do
  let a ← b.claims[i]?
  let z ← b.claims[j]?
  if a.rhs != z.lhs then none else b.add P C ⟨a.lhs, z.rhs⟩ (.trans i j)

def Builder.congr (P : Program) (C : Context) (b : Builder) (i k j : Nat) :
    Option (Nat × Builder) := do
  let a ← b.claims[i]?
  let z ← b.claims[j]?
  let .app f args := a.rhs | none
  if args[k]? != some z.lhs then none else
    b.add P C ⟨a.lhs, .app f (args.set k z.rhs)⟩ (.congr i k j)

def Builder.orient (P : Program) (C : Context) (b : Builder) (i : Nat) (c : Claim) :
    Option (Nat × Builder) := do
  let a ← b.claims[i]?
  if a == c then some (i, b) else
    if a.lhs == c.rhs && a.rhs == c.lhs then b.symm P C i else none

def contains (c : Claim) (t : Term) : Bool :=
  decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

/-- Recover subterm existence from a source derivation, without a new proof axiom. -/
def support (P : Program) (C : Context) :
    Nat → Builder → Nat → Term → Option (Nat × Builder)
  | 0, _, _, _ => none
  | fuel + 1, b, i, t => do
    let n ← b.nodes[i]?
    if !contains n.claim t then none else do
      if let some j := b.find ⟨t, t⟩ then some (j, b) else
        if n.claim.lhs == t then do
          let (j, next) ← b.symm P C i
          next.trans P C i j
        else if n.claim.rhs == t then do
          let (j, next) ← b.symm P C i
          next.trans P C j i
        else match n.reason with
        | .fiat => b.add P C ⟨t, t⟩ .fiat
        | .rule command σ ps => b.add P C ⟨t, t⟩ (.rule command σ ps)
        | .symm j => support P C fuel b j t
        | .trans j k | .congr j _ k =>
          support P C fuel b j t <|> support P C fuel b k t
        | .merge _ _ _ => none

def witness (P : Program) (C : Context) (b : Builder) (t : Term) :
    List Nat → Option (Nat × Builder)
  | [] => none
  | i :: is => support P C (b.nodes.length + 1) b i t <|> witness P C b t is

def Builder.finish (P : Program) (C : Context) (b : Builder) (i : Nat) (c : Claim) :
    Option (Nat × Builder) :=
  b.orient P C i c <|>
    if c.lhs == c.rhs then support P C (b.nodes.length + 1) b i c.lhs else none

end Egglog.Resugar
