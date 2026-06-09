import Lean
import Batteries.Lean.Meta.UnusedNames


open Lean Elab Tactic Meta

namespace SystemE.Tactics

/-! ### Dependency tracking for faithfulness (criterion 3)

`euclid_apply` records, for each applied proposition, the COMPILER-RESOLVED fully-qualified
constant name (e.g. `Elements.Book1.proposition_11''`) together with its module and source line.
This lives here in `Util` — the common ancestor of `Solve` (where `euclid_apply` is defined) and
`Faithful` (where the sentence annotations live) — so both can reach it without an import cycle.

The criterion-3 check is then done OUTSIDE Lean: a `lake exe` dumps these entries (and the
`FaithfulEntry`s) from the compiled `.olean` as JSON, and `scripts/check_faithful.py --olean`
associates each cited `[Prop.~B.N]` with the `euclid_apply`s in the citing sentence's block
(same module, line between the previous sentence and this one) and matches them against the
resolved, BOOK-AWARE names. -/

/-- One recorded `euclid_apply` of a `proposition_*`: the resolved constant and where it occurred. -/
structure AppliedEntry where
  /-- Module the `euclid_apply` occurred in, e.g. `"Book2.Prop01"`. -/
  mod  : String
  /-- Resolved fully-qualified constant name, e.g. `"Elements.Book1.proposition_11''"`. -/
  name : String
  /-- Source line of the `euclid_apply`. -/
  line : Nat
  deriving Inhabited, Repr

/-- Persistent env extension storing all `AppliedEntry`s (folded across imports, like `faithfulExt`).
Serialized into the `.olean` so the external checker can read it back. -/
initialize appliedExt :
    SimplePersistentEnvExtension AppliedEntry (List AppliedEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/--
Return if the weak head norm form of `e` is a conjunction.
-/
private def isConjunction (e : Expr) : MetaM Bool := do
  match (← whnf e).getAppFnArgs with
  | (``And, _) => return True
  | _ => return False

/--
Return if the weak head norm form of `e` is a disjunction.
-/
private def isDisjunction (e : Expr) : MetaM Bool := do
  match (← whnf e).getAppFnArgs with
  | (``Or, _) => return True
  | _ => return False

/--
Try to eliminate a conjunction `decl` in the local context.
-/
partial def elimConjunction (decl : LocalDecl) : TacticM Unit := do
  if ¬(← isConjunction decl.type) then
    return ()

  let left  ← getUnusedUserName `left
  let right ← getUnusedUserName `right
  evalTactic $ ← `(tactic| cases ($(mkIdent decl.userName)) with | intro $(mkIdent left) $(mkIdent right) => _)

  withMainContext do
    let ctx ← getLCtx
    if let some l := ctx.findFromUserName? left then
      elimConjunction l
    if let some r := ctx.findFromUserName? right then
      elimConjunction r

/--
Try to eliminate a disjunction `decl` in the local context.
-/
partial def elimDisjunction (decl : LocalDecl) : TacticM Unit := do
  if ¬(← isDisjunction decl.type) then
    return ()

  let left  ← getUnusedUserName `left
  let right ← getUnusedUserName `right
  evalTactic $ ← `(tactic| cases ($(mkIdent decl.userName)) with | inl $(mkIdent left) => _ | inr $(mkIdent right) => _)

  withMainContext do
    let ctx ← getLCtx
    if let some l := ctx.findFromUserName? left then
      elimDisjunction l
    if let some r := ctx.findFromUserName? right then
      elimDisjunction r

/--
Destruct all conjunctions in the local context.
-/
def elimAllConjunctions : TacticM Unit :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      elimConjunction decl

/--
Destruct all conjunctions in the local context.
-/
def elimAllDisjunctions : TacticM Unit :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      elimDisjunction decl

syntax "split_ors" : tactic

elab "split_ors" : tactic => elimAllDisjunctions

def pretty (e : Expr) : MetaM Format := do
    let s ← Tactic.TryThis.delabToRefinableSyntax e
    let f ← PrettyPrinter.ppCategory `term s
    pure f

def traceUnsolved (unsolved : List Format) : TacticM Unit := do
    let unsolved := ",".intercalate (unsolved.map Format.pretty)
    logInfo s!"unsolved goals: {unsolved}"

end SystemE.Tactics
