import SystemE.Meta.Tactics.Util
import SystemE.Meta.Smt.Solver

set_option autoImplicit false

open Lean Elab Tactic Meta SystemE.Smt


namespace SystemE.Tactics

open Translation

/- Data Structure for containing various information
   for the `euclid_apply` tactic
   Basically, everything here is used for reconstructing the tactic after
   the solvers have been invoked.


   `rule` : the argument to `euclid_apply, i.e., the application of some axiom to some arguments.
    When elaborated, `rule` will be a term of type `P -> Q`, where `P` is the hole to be filled
    `hole` : The antecedent of the above implication
    `nm ` : The name we will give to the premise `hole` once it is filled
    `isConstr` : True if the instance of `euclid_apply` is "constructive", i.e. is of the form `euclid_apply rule as i`
    `ident` : The identifier to be used to construct the object if `isConstr` is true
    `smtContext` the SMT context generated from the proof state in which `euclid_apply` is invoked
-/
structure EuclidStep where
  rule : Term
  hole : Expr
  holeName : Name
  isConstr := false
  idents : Array Ident
  smtContext : Esmt := default

abbrev EuclidStepM := ReaderT EuclidStep TacticM

namespace EuclidStep

def init (g : MVarId) (hole : Expr) (rule : Term) (idents : Array Ident) : TacticM EuclidStep :=
  g.withContext do
    let n ← getUnusedUserName `aux
    return {hole := hole, holeName := n, rule := rule, isConstr := ¬ idents.isEmpty, idents := idents}

/- Add a new goal whose target is the whole to be filled.
   The original proof state will now have the hole as a premise.
 -/
def pushHole : EuclidStepM Unit := do
  let Γ ← read
  let p ← mkFreshExprMVar Γ.hole MetavarKind.natural
  let (_, mvarIdNew) ← Lean.MVarId.intro1P $ ← (← getMainGoal).assert Γ.holeName Γ.hole p
  replaceMainGoal [p.mvarId!, mvarIdNew]

/- We are now in a proof state where the hole has been filled, so we can reconstruct the tactic and apply the rule -/
private def applyHole (stx : Term) (hnm : Name) : EuclidStepM Unit := do
  let Γ ← read
  if Γ.isConstr then
    evalTactic $ ← `(tactic| obtain ⟨$Γ.idents,*, ($(mkIdent hnm))⟩ := $Γ.rule $stx)
  else
    evalTactic $ ← `(tactic| obtain ($(mkIdent hnm)) := $Γ.rule $stx)

/- invoke `applyHole` only if the hole actually exists -/
def finish : EuclidStepM Unit := do
  let Γ ← read
  withMainContext do
    match (← getLCtx).findFromUserName? Γ.holeName with
    | none =>   dbg_trace "finish: fail" ; failure
    | some d =>
      applyHole (← d.toExpr.toSyntax) (← getUnusedUserName `h) |>.run Γ
      evalTactic $ ← `(tactic| try (clear ($(mkIdent Γ.holeName))))
      evalTactic $ ← `(tactic| try aesop_destruct_products)

end EuclidStep

open EuclidStep

/-
  Solve the given subgoal (a conjunct of `Γ.hole`) using the SMT solvers.
  We call z3 first, then cvc5 if z3 fails, but this can be changed.
  Ideally, we would parallelize.

  If the goal is not proved, we return its type (for printing to the user)
-/
private def solveWithProvers (query : Esmt) (g : MVarId) : TacticM (Option Expr) := do
  let goal ← instantiateMVars (← g.getType)
  -- logInfo m!"{goal}"
  let smtQuery ← addGoal query goal
  match ← evalSmt smtQuery with
  | .unsat =>
    closeWithAxiom g
    return none
  | .sat =>
    logWarning m!"Prover returned SAT"
    failure
  | _ =>
      emitGoalAndCloseWithSorry g
      return goal

private def simpAndSplit : TacticM Syntax :=
  `(tactic| try simp_all ; try split_ands)

/--
The `euclid_finish` tactic tries to prove the current goal using various proof automation, including SMT offloading.
-/

def refersToCong (e : Expr) : MetaM Bool := do
match e.getAppFnArgs with
| (`Triangle.congruent, _) => return true
| _ => return false

def preprocess : TacticM Unit := do
  let ctx ← getLCtx
  for decl in ctx do
    if ← refersToCong decl.type then do
      let hname := decl.userName
      evalTactic $ ← `(tactic| try unfold Triangle.congruent at $(mkIdent hname):ident)
      evalTactic $ ← `(tactic| try simp at $(mkIdent hname):ident)
  -- Destruct every context conjunction (the SAME step `euclid_apply` runs, Solve.lean's `elimAllConjunctions`
  -- call below): `whnf` sees through reducible abbrevs, so a raw `distinctPointsOnLine`/`opposingSides`
  -- hypothesis (e.g. a faithful `euclid_sentence` claim `have`, which no `euclid_apply` ever destructed)
  -- is split into the primitive `onLine`/`≠` conjuncts the SMT translator can handle — instead of hitting
  -- `translateExpr`'s catch-all and aborting the whole solve with "Unexpected application …".
  elimAllConjunctions

def EuclidFinish (isApply : Bool) : TacticM Unit := do
  if !isApply then preprocess
  withMainContext do
    let subGoals ← evalTacticAt (← simpAndSplit) (← getMainGoal)
    replaceMainGoal subGoals
    if subGoals.isEmpty then
      return ()
    let ctx ← getESMTfromContext
    let mut unsolved : List Format := []
    for g in subGoals do
      if let some e ← solveWithProvers ctx g then
        unsolved := (← pretty e)::unsolved
    if ¬unsolved.isEmpty then
      traceUnsolved unsolved

syntax "euclid_finish" : tactic

elab "euclid_finish" : tactic => withMainContext <| EuclidFinish false

/-
  Invoked when `euclid_apply` has a hole to be filled.
  `hole` : The expression corresponding to the `Prop` to be filled
  `rule` : The whole argument of `euclid_apply`, e.g. `circle_from_points a b`
  `ident` : The identifier to be used if the `euclid_apply` instance is constructive
-/
private def EuclidSolve : EuclidStepM Unit := do
  pushHole
  EuclidFinish true
  finish

/-
  Main function for `euclid_apply`
-/
def EuclidApply (rule : Term) (idents : Array Ident)  : TacticM Unit := do
  if (← getGoals).length != 1 then
    throwError "euclid_apply only works when there is a single goal"
  let hnm ← getUnusedUserName `h
  let ruleExpr ← elabTerm rule none
  let τ ← inferType ruleExpr >>= instantiateMVars

  -- Faithfulness (criterion 3): record EVERY applied constant's COMPILER-RESOLVED fully-qualified
  -- name, module, and source line into `appliedExt` (no name filter). The name is already resolved
  -- by `elabTerm` above, so this adds no elaboration cost. We don't restrict to `proposition_*`/
  -- `helper_*` because `faithful_export` follows each recorded constant's TRANSITIVE dependency
  -- closure to find the `proposition_*` it (transitively) uses — so a prop cited inside ANY applied
  -- function (a `helper_<book>_step<n>`, or a function inside that function) still satisfies the
  -- citation. Pure-axiom constructions (`line_from_points`, `intersection_lines`) have empty
  -- closures, so recording them is harmless.
  if let .const declName _ := ruleExpr.getAppFn then
    let fileMap ← getFileMap
    let line := match (← getRef).getPos? with
      | some p => (fileMap.toPosition p).line
      | none   => 0
    let modName := (← getMainModule).toString
    modifyEnv fun env =>
      appliedExt.addEntry env { mod := modName, name := declName.toString, line := line }

  match τ with
  | .forallE _ hole P _ => -- τ is an arrow
    if P.hasLooseBVars then  --  τ is an ∀
      evalTactic $ ← `(tactic| obtain ($(mkIdent hnm)) := $rule)
    else  -- τ is an implication, rather than ∀
      let Γ ← init (← getMainGoal) hole rule idents
      EuclidSolve |>.run Γ
  -- If there is no implication in the rule, i.e. no antecedent/hole to be filled, then just do the construction.
  | e =>
    match e.getAppFnArgs with
    | (``Exists, _) =>  -- τ is `∃ x, ...`
      evalTactic $ ← `(tactic| obtain ⟨$idents,*, ($(mkIdent hnm))⟩ := $rule)
    | _ =>
      -- CLOSE-DIRECTLY FIRST: a fully-applied rule's conclusion may BE the current goal (the faithful
      -- wire always has helper-conclusion == node-goal). `exact $rule` then closes it directly — ZERO
      -- SMT, works for every claim shape (`∧`, `∨`, atomic, …). Citation recording already ran above
      -- (appliedExt), so this loses nothing. On failure (conclusion ≠ goal — the old-style "add a
      -- fact to context" use), fall through unchanged to the destructuring below. If `exact` closes
      -- the goal, the trailing `elimAllConjunctions` is a no-op via its empty-goals guard (Util.lean).
      -- NOTE: this requires faithful wires to carry NO trailing closer — the `(try split_ands) <;>
      -- assumption` trailer errors "no goals" once `exact` closes. wire_main regenerates wires
      -- trailer-free, so committed props must be unwired + rewired once this is live.
      evalTactic $ ← `(tactic| first
        | exact $rule
        | (obtain ⟨$(mkIdent hnm)⟩ := $rule)
        | (obtain $(mkIdent hnm) := $rule))

  elimAllConjunctions

syntax "euclid_apply" term : tactic

syntax "euclid_apply" term "as" ident : tactic

syntax "euclid_apply" term "as" "(" ident,+ ")" : tactic

syntax "euclid_assert" term : tactic

elab_rules : tactic
  | `(tactic| euclid_apply $t as $i) =>
    withMainContext $ EuclidApply t #[i]
  | `(tactic| euclid_apply $t as ($is,*)) =>
    withMainContext $ EuclidApply t is
  | `(tactic| euclid_apply $t) =>
    withMainContext $ EuclidApply t #[]

macro_rules
  | `(tactic| euclid_assert $t) => `(tactic| have : $t := by euclid_finish)

set_option systemE.trace false
set_option systemE.solverTime 300

end SystemE.Tactics
