import EgglogSemantics.SourceProof.Format

namespace Egglog.SourceProof

mutual

def valueOk (sig : Signature) : Term → Bool
  | .lit _ => true
  | .app f args => (sig f).any fun d =>
      (Prim.ofName f).isNone && d.merge.isNone && args.length == d.arity &&
        valuesOk sig args

def valuesOk (sig : Signature) : List Term → Bool
  | [] => true
  | t :: ts => valueOk sig t && valuesOk sig ts

end

/-- Function entries are allowed only at the root. -/
def atomOk (sig : Signature) : Term → Bool
  | .lit _ => true
  | .app f args => (sig f).any fun d =>
      (Prim.ofName f).isNone && args.length == d.entryWidth && valuesOk sig args

def reflClaims (t : Term) : List Claim :=
  t.subtermList.map fun s => ⟨s, s⟩

/-- Only facts produced by this action, including constructed subterms. -/
def actionFacts (sig : Signature) (σ : Env) : Action → Option (List Claim)
  | .expr e => do
      let t ← e.evalAtom sig σ
      if atomOk sig t then some (reflClaims t) else none
  | .union a b => do
      let x ← a.eval sig σ
      let y ← b.eval sig σ
      if valueOk sig x && valueOk sig y && !(x.isLit || y.isLit) then
        some (⟨x, y⟩ :: ⟨y, x⟩ :: (reflClaims x ++ reflClaims y))
      else none

def actionsFacts (sig : Signature) (σ : Env) : List Action → Option (List Claim)
  | [] => some []
  | a :: as => do
      let fs ← actionFacts sig σ a
      let rest ← actionsFacts sig σ as
      some (fs ++ rest)

structure Context where
  sig : Signature
  globals : List Claim

def Context.empty : Context := ⟨fun _ => none, []⟩

def Context.step (C : Context) : Cmd → Option Context
  | .decl f d =>
      if (C.sig f).isSome || (Prim.ofName f).isSome then none
      else some { C with sig := Function.update C.sig f (some d) }
  | .action a => (actionFacts C.sig [] a).map fun fs =>
      { C with globals := C.globals ++ fs }
  | _ => some C

/-- No rule execution or merge computation contributes a `Fiat` fact. -/
def contextOf (P : Program) : Option Context := P.foldlM Context.step Context.empty

end Egglog.SourceProof
