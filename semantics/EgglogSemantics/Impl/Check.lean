import EgglogSemantics.Spec.Scope

/-!
# The front end's static checks

Arity and value-position checks for the model's atom syntax. These executable checks
are consumed by the differential tests and examples. Function entries occupy complete
query or action atoms; constructors and `min` occupy value positions.
-/

namespace Egglog
/-! ### Arity

Declarations fix column counts. Constructor applications use their argument count;
function entry atoms use all key and output columns. Nested expressions and equality
or union operands are values. A merge result has one expression per output column.
-/

mutual

/-- Every application of a declared function inside `e` has its declared key arity and one
value column. A name with no entry has nothing to disagree with. -/
def Expr.arityOk : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig =>
      (match sig f with
       | none => true
       | some d => args.length == d.arity && d.outArity == 1) && Expr.arityOkList args sig
  | .min a b, sig => Expr.arityOk a sig && Expr.arityOk b sig

/-- `Expr.arityOk` over an argument list. -/
def Expr.arityOkList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.arityOk e sig && Expr.arityOkList es sig

end

/-- Complete atoms use all table columns; their children are value expressions. -/
def Expr.atomArityOk : Expr → Signature → Bool
  | .app f cols, sig =>
      (match sig f with
       | none => true
       | some d => cols.length == d.entryWidth) && Expr.arityOkList cols sig
  | .min a b, sig => Expr.arityOk a sig && Expr.arityOk b sig
  | _, _ => true

/-- A complete atom or an equality between values. -/
def Pattern.arityOk : Pattern → Signature → Bool
  | .expr e, sig => e.atomArityOk sig
  | .eq e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig

/-- A complete atom or a union between values. -/
def Action.arityOk : Action → Signature → Bool
  | .expr e, sig => e.atomArityOk sig
  | .union e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig

/-- Every action in the list. Actions do not change the signature. -/
def Actions.arityOk (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.arityOk · sig)

/-- A rule's query and head. -/
def Rule.arityOk (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.arityOk · sig) && Actions.arityOk r.actions sig

/-- A merge specification, against the declaration's `outArity` value columns. -/
def MergeSpec.arityOk : MergeSpec → Nat → Signature → Bool
  | .merge oldVars newVars body res, outArity, sig =>
      decide (MergeSpec.BindersOk (.merge oldVars newVars body res) outArity) &&
      res.length == outArity && Actions.arityOk body sig && res.all (Expr.arityOk · sig)

/-- A declaration's own value columns: a constructor has exactly one, which is egglog
forbidding it a tuple output; a merge function is checked against its result. -/
def FnDecl.arityOk (d : FnDecl) (sig : Signature) : Bool :=
  match d.merge with
  | none => d.outArity == 1
  | some m => m.arityOk d.outArity sig

/-- A command. A declaration's merge body sees the signature the declaration itself
installs, so it may write the function's own table. -/
def Cmd.arityOk : Cmd → Signature → Bool
  | .rule r, sig => r.arityOk sig
  | .check q, sig => q.all (Pattern.arityOk · sig)
  | .run _, _ => true
  | .saturate _, _ => true
  | .decl f d, sig => d.arityOk ((Cmd.decl f d).sigBind sig)

/-- Each command is checked against the signature the earlier commands leave. -/
def Program.arityOk : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.arityOk sig && Program.arityOk cs (c.sigBind sig)

/-- The executable arity check as a proposition. -/
def Program.ArityOk (p : Program) (sig : Signature) : Prop := p.arityOk sig = true

/-- The arity check from the empty signature, as `WellScoped` is the scope check from the
empty scope. -/
def WellArity (p : Program) : Prop := Program.ArityOk p (fun _ => none)

/-! ### Value positions

Entries are permitted only as complete atoms. Atom columns, equality and union operands,
and merge results contain constructor applications and `min`. Evaluation therefore
never performs a table lookup inside a value expression. Undeclared names are rejected.
-/

mutual

/-- No application inside `e` reads a row: every function it names is a declared
constructor. -/
def Expr.noLookup : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig => decide (sig.IsCtor f) && Expr.noLookupList args sig
  | .min a b, sig => Expr.noLookup a sig && Expr.noLookup b sig

/-- `Expr.noLookup` over an argument list. -/
def Expr.noLookupList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.noLookup e sig && Expr.noLookupList es sig

end

/-- A table application is an atom only at the root. Its columns are values. -/
def Expr.atomNoLookup : Expr → Signature → Bool
  | .app f cols, sig => (sig f).isSome && Expr.noLookupList cols sig
  | .min a b, sig => Expr.noLookup a sig && Expr.noLookup b sig
  | _, _ => true

/-- An action, in every expression position egglog's check walks. -/
def Action.noLookup : Action → Signature → Bool
  | .expr e, sig => e.atomNoLookup sig
  | .union e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig

/-- Every action in the list. No threading: no action changes the signature. -/
def Actions.noLookup (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.noLookup · sig)

/-- A `:merge` body and its result columns. -/
def MergeSpec.noLookup : MergeSpec → Signature → Bool
  | .merge _ _ body res, sig => Actions.noLookup body sig && res.all (Expr.noLookup · sig)

/-- Entries are complete query atoms; equality compares values. -/
def Pattern.noLookup : Pattern → Signature → Bool
  | .expr e, sig => e.atomNoLookup sig
  | .eq e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig

/-- The query and actions use the same restrictions on value positions. -/
def Rule.noLookup (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.noLookup · sig) && Actions.noLookup r.actions sig

/-- A declaration's merge body sees the declaration itself, so it can write its own table. -/
def Cmd.noLookup : Cmd → Signature → Bool
  | .rule r, sig => r.noLookup sig
  | .check q, sig => q.all (Pattern.noLookup · sig)
  | .run _, _ => true
  | .saturate _, _ => true
  | .decl f d, sig =>
      match d.merge with
      | none => true
      | some m => m.noLookup ((Cmd.decl f d).sigBind sig)

/-- Each command against the signature the earlier ones leave, as `Program.arityOk`. -/
def Program.noLookup : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.noLookup sig && Program.noLookup cs (c.sigBind sig)

/-- The executable value-position check as a proposition. -/
def Program.NoLookup (p : Program) (sig : Signature) : Prop := p.noLookup sig = true

/-- The value-position check from the empty signature. -/
def ReadsAreAtoms (p : Program) : Prop := Program.NoLookup p (fun _ => none)

end Egglog
