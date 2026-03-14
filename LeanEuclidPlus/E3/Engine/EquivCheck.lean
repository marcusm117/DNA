import E3.Util.IO
import E3.Engine.Preprocess
import E3.Data.EvalCtx
import E3.Data.NewModeResults
import SystemE.Smt

open Qq
set_option autoImplicit false

-- Helper: Check if a string contains a substring
private def stringContains (haystack : String) (needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

open Lean Elab Command Tactic Meta Smt.Solver SystemE.Smt SystemE.Tactics
open E3Result

/-- Modified version of `evalSmt`used by E3. Similar to the normal usage in `euclid_*` tactics, except we include different background theoeries depending on the context -/
def evalSmt' (unsatCheck : Bool) (Γ : Option Esmt) (t : Nat) (x : EAssertion) (additionalAxioms : List String := []) : PropEvalM String := do
  let background :=
    -- if we are just checking to see whether an expression is unsatisfiable
    if unsatCheck then euclidTheory ++ euclidConstructionRulesFull
    else match Γ with
      -- if we are checking equivalence at the formula-level
      | none => euclidTheory ++ euclidConstructionRulesShort
      -- if we are checking individual clauses
      | some ctx => euclidTheory ++ SystemE.Tactics.Translation.fromEsmt ctx

  -- Add additional axioms if provided
  let backgroundWithAxioms := if additionalAxioms.isEmpty then background
    else background ++ (additionalAxioms.map Smt.Term.literalT |>.map Smt.Command.assert)

  let assertion :=  s!"{x}" |> Smt.Term.literalT |> Smt.Command.assert
  let query := addCommands (backgroundWithAxioms ++ [assertion]) *> checkSat
  let solverState ← Smt.Solver.create t

  if unsatCheck then
    IO.println s!"Running euclidConstructionRulesFull check with timeout {t}s on: {x}"
  else
    IO.println s!"Running euclidConstructionRulesShort check with timeout {t}s on: {x}"

  let result ← (StateT.run' query solverState : MetaM _)
  match result with
  | .unsat =>
    IO.println "SMT solver returned UNSAT"
    return "UNSAT"
  | .sat =>
    IO.println "SMT solver returned SAT"
    return "SAT"
  | .unknown =>
    IO.println "SMT solver returned UNKNOWN"
    return "UNKNOWN"
  | .timeout =>
    IO.println "SMT solver timed out"
    return "TIMEOUT"


/- Check `Ground <==> Test`
   Also try to check whether `Test` and `Ground` are actually unsatisfiable
-/
def checkFullIff : PropEvalM EquivResult := do
  let test ← translateTestExpr
  let testNeg : EAssertion := .neg <| test
  let ground ← translateGroundExpr
  let groundNeg : EAssertion := .neg <| ground
  let testToGround : EAssertion := .imp test ground
  let testToGroundNeg : EAssertion := .neg <| .imp test ground
  let groundToTest : EAssertion := .imp ground test
  let groundToTestNeg : EAssertion := .neg <| .imp ground test

  /- Check satisfiability of both Assertion and Negation of `Test` -/
  IO.println "============================================================"
  IO.println "Checking Test (Assertion) ..."
  let testResult ← evalSmt' true none 5 test []
  IO.println "------------------------------------------------------------"
  IO.println "Checking Test (Negation) ..."
  let testNegResult ← evalSmt' true none 5 testNeg []

  /- Check satisfiability of both Assertion and Negation of `Ground` -/
  IO.println "============================================================"
  IO.println "Checking Ground (Assertion) ..."
  let groundResult ← evalSmt' true none 5 ground []
  IO.println "------------------------------------------------------------"
  IO.println "Checking Ground (Negation) ..."
  let groundNegResult ← evalSmt' true none 5 groundNeg []

  /- Check satisfiability of both Assertion and Negation of `Test → Ground` -/
  IO.println "============================================================"
  IO.println "Checking Test → Ground (Assertion) ..."
  let testToGroundResult ← evalSmt' false none (←getEvalConfig).equivSolverTime testToGround []
  IO.println "------------------------------------------------------------"
  IO.println "Checking Test → Ground (Negation) ..."
  let testToGroundNegResult ← evalSmt' false none (←getEvalConfig).equivSolverTime testToGroundNeg []

  /- Check satisfiability of both Assertion and Negation of `Ground → Test` -/
  IO.println "============================================================"
  IO.println "Checking Ground → Test (Assertion) ..."
  let groundToTestResult ← evalSmt' true none 5 groundToTest []
  IO.println "------------------------------------------------------------"
  IO.println "Checking Ground → Test (Negation) ..."
  let groundToTestNegResult ← evalSmt' false none (←getEvalConfig).equivSolverTime groundToTestNeg []
  IO.println "============================================================"

  /- Store all results in the state -/
  modify (λ s =>
    { s with
      test := testResult,
      testNeg := testNegResult,
      ground := groundResult,
      groundNeg := groundNegResult,
      testToGround := testToGroundResult,
      testToGroundNeg := testToGroundNegResult,
      groundToTest := groundToTestResult,
      groundToTestNeg := groundToTestNegResult
    })

  /-
    Return an EquivResult structure based `testToGroundNeg` and `groundToTestNeg`
    If the result is "UNSAT", then the implication holds in that direction,
    so we return `true` for that direction.
    If otherwise, we return `false`.
  -/
  let testToGroundNegBinary := testToGroundNegResult == "UNSAT"
  let groundToTestNegBinary := groundToTestNegResult == "UNSAT"
  return { groundImpTest := groundToTestNegBinary, testImpGround := testToGroundNegBinary }

/--
  Check `Test → GroundTruth` in the approximate checker.
  This function is used for both the LHS (comparing preconditions) and RHS (comparing postconditions)
-/
def solveBwd (test ground : EAssertion) (ctx : Esmt) (assumptions : List EAssertion) : PropEvalM ImpResult := do
  let assumptions := assumptions ++ test.splitConjuncts
  let obligations := ground.splitConjuncts
  let total := obligations.length
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    let result ← evalSmt' false ctx' (← getEvalConfig).approxSolverTime (.neg goal) []
    if (result == "UNSAT") then
      solved := solved + 1
  return .mk total solved

/--
  Assuming preconditions of `GroundTruth`, prove preconditions of `Test`.
-/
def solveFwdLHS (ground test : EAssertion) (ctx : Esmt)   : PropEvalM ImpResult := do
  let assumptions := ground.splitConjuncts
  let obligations := test.splitConjuncts
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    if ← seenGoalLHS goal then
      if ← isProvenLHS goal then solved := solved + 1 else continue
    else
      let result ← evalSmt' false ctx' (← getEvalConfig).approxSolverTime (.neg goal) []
      if (result == "UNSAT") then
        addProofLHS goal true
        solved := solved + 1
      else addProofLHS goal false
  return .mk obligations.length solved

/--
  Assuming postconditions of `GroundTruth`, prove postconditions of `Test`.
-/
def solveFwdRHS (ground test : EAssertion) (ctx : Esmt)  (assumptions : List EAssertion) : PropEvalM ImpResult := do
  let assumptions := assumptions ++ ground.splitConjuncts
  let obligations := test.splitConjuncts
  let total := obligations.length
  let ctx' : Esmt := {ctx with asserts := assumptions.toArray}
  let mut solved : Nat := 0
  for goal in obligations do
    if ← seenGoalRHS goal then
      if ← isProvenRHS goal then solved := solved + 1 else continue
    else
      let result ← evalSmt' false ctx' (← getEvalConfig).approxSolverTime (.neg goal) []
      if (result == "UNSAT") then
        addProofRHS goal true
        solved := solved + 1
      else addProofRHS goal false
  return .mk total solved

/-- Check (one half of) `GroundTruth <===> Test` using the approximate checker.
    Note that this function operates on either the preconditions (LHS) or postconditions (RHS)
-/
def checkIffApprox (ground test : EAssertion) (isLHS : Bool) (assumptions : List EAssertion)  : PropEvalM (ImpResult × ImpResult) := do
  -- IO.println "checking fwd direction ..."
  let fwd ←
    if isLHS then
      solveFwdLHS ground test (← getGroundCtx)
    else
      solveFwdRHS ground test (← getGroundCtx) assumptions
  -- IO.println "checking bwd direction ..."
  let bwd ← solveBwd test ground (← getGroundCtx) assumptions
  return ⟨fwd, bwd⟩

def solvePerms
  (groundNames : List String)
  (perms : List (List String)) : PropEvalM ApproxResult := do
  let init_map ← getTestNameMap
  let mut result : ApproxResult := .mk {}
  let mut i : Nat := 0
  for perm in perms do
    -- IO.println "Checking perm ..."
    let subst : HashMap String String := HashMap.ofList <| perm.zip groundNames
    setTestNames <| ← mergeMaps init_map subst
    -- IO.println "checking LHS ..."
    let ⟨fwdLHS, bwdLHS⟩ ← checkIffApprox (← getGroundLHS) (← translateTestLHS) true []
    let mut assumptions : List EAssertion := []
    if fwdLHS.success && bwdLHS.success then
      --  IO.println "LHS proved equivalent; preconditions will be included for RHS"
       assumptions := (← getGroundLHS).splitConjuncts
    -- IO.println "checking RHS ..."
    let ⟨fwdRHS, bwdRHS⟩ ← checkIffApprox (←getGroundRHS) (← translateTestRHS) false assumptions
    result := result.addResult s!"permutation_{i}" subst fwdLHS bwdLHS fwdRHS bwdRHS
    i := i + 1
  return result

/--
  Check `GroundTruth <===> Test` using the approximate equivalence checker.
  We do some preprocessing, then handoff to  `choosePerms.py` to choose the best unifications
  (permutations) of bound variables (using a string similarity heuristic).

  For each proposed unification, we check bidirectional implications in a clause-by-clause manner.
-/
def approxChecker : PropEvalM ApproxResult := do
  let groundE ← getGroundExpr
  let guardedE := renameBVars (← getTestExpr)
  let gjson := forJson <| ← getGroundBvars
  let tjson := forJson <| .map ("grd_"++ .)  <| ← getTestBvars
  let mut ⟨rawGroundLHSExpr, _, _⟩ ← splitExpr (← groundNegative?) groundE
  if !(← inferType rawGroundLHSExpr).isProp then
    rawGroundLHSExpr := q(True)
  let rawFull : String := Format.pretty (← pretty groundE) (width := 10000)
  let guardedFull : String := Format.pretty (← pretty guardedE) (width := 10000)
  match ← permutationHeuristic (permInFile (←getInstName)) (permOutFile (←getInstName)) rawFull guardedFull tjson gjson (← getEvalConfig).nPermutations with
      | .error _ => return .mk {}
      | .ok ⟨ground, perms⟩ =>
        -- E3.clean_tmp_dir (← getInstName)
        let r ← solvePerms ground perms
        return r


/-- Helper function to filter a HashSet -/
def filterHashSet (s : HashSet String) (p : String → Bool) : HashSet String :=
  s.fold (fun acc x => if p x then acc.insert x else acc) (HashSet.empty : HashSet String)

/-- Helper function to union two HashSets -/
def unionHashSet (s1 s2 : HashSet String) : HashSet String :=
  s1.fold (init := s2) (fun acc (x : String) => acc.insert x)

/-- Helper function to collect free variables in an EAssertion -/
def collectFreeVars (expr : EAssertion) : HashSet String :=
  let rec go (expr : EAssertion) (bound : HashSet String) : HashSet String :=
    match expr with
    | .top => HashSet.empty
    | .erel r => collectRelationVars r
    | .eq a b => unionHashSet (extractVarsFromString a bound) (extractVarsFromString b bound)
    | .lt a b => unionHashSet (extractVarsFromString a bound) (extractVarsFromString b bound)
    | .lte a b => unionHashSet (extractVarsFromString a bound) (extractVarsFromString b bound)
    | .gt a b => unionHashSet (extractVarsFromString a bound) (extractVarsFromString b bound)
    | .gte a b => unionHashSet (extractVarsFromString a bound) (extractVarsFromString b bound)
    | .neg x => go x bound
    | .ex x _ p => go p (bound.insert x)
    | .all x _ p => go p (bound.insert x)
    | .or a b => unionHashSet (go a bound) (go b bound)
    | .and a b => unionHashSet (go a bound) (go b bound)
    | .imp a b => unionHashSet (go a bound) (go b bound)
  go expr HashSet.empty
where
  extractVarsFromString (s : String) (bound : HashSet String) : HashSet String :=
    -- Handle function expressions like "(AnglePPP R S U)" or "(+ RightAngle RightAngle)"
    if s.startsWith "(" then
      -- Parse function expression to extract variable names
      let tokens := s.replace "(" "" |>.replace ")" "" |>.split (· == ' ')
      -- Skip the first token (function name) and extract variable names from remaining tokens
      let varTokens := tokens.drop 1
      varTokens.foldl (fun acc token =>
        if token.length > 0 && !isConstantToken token && !bound.contains token then
          acc.insert token
        else acc) HashSet.empty
    else
      -- Simple variable name
      if !bound.contains s then HashSet.empty.insert s else HashSet.empty

  -- Helper to identify constant tokens that are not variables
  isConstantToken (token : String) : Bool :=
    token == "RightAngle" ||
    token == "+" || token == "-" || token == "*" || token == "/" ||
    token.all (fun c => c.isDigit || c == '.')  -- numeric constants

  collectRelationVars (r : ERelation) : HashSet String :=
    match r with
    | .OnL p l => (HashSet.empty.insert p).insert l
    | .OnC p c => (HashSet.empty.insert p).insert c
    | .Centre p c => (HashSet.empty.insert p).insert c
    | .InC p c => (HashSet.empty.insert p).insert c
    | .SameSide p₁ p₂ l => ((HashSet.empty.insert p₁).insert p₂).insert l
    | .Between p₁ p₂ p₃ => ((HashSet.empty.insert p₁).insert p₂).insert p₃
    | .IntersectsLL l₁ l₂ => (HashSet.empty.insert l₁).insert l₂
    | .IntersectsLC l c => (HashSet.empty.insert l).insert c
    | .IntersectsCC c₁ c₂ => (HashSet.empty.insert c₁).insert c₂

/-- Helper function to collect all quantified variables from the outer layers -/
def collectQuantifiedVars (expr : EAssertion) : List (String × String) :=
  match expr with
  | .all varName varType body => (varName, varType) :: collectQuantifiedVars body
  | _ => []

/-- Helper function to extract line name from various formats --/
def extractLineName (varName : String) : String :=
  let lower := varName.toLower
  let enoughLen4 := decide (varName.length > 4)
  let nonAlpha4 := (varName.toList.get? 4).map (fun c => if c.isAlpha then false else true) |>.getD false
  let hasLinePrefix := lower.startsWith "line"
  let hasLinePrefixNonAlpha := enoughLen4 && nonAlpha4
  let isLinePrefixWithNonAlpha := hasLinePrefix && hasLinePrefixNonAlpha
  let enoughLen1 := decide (varName.length > 1)
  let nonAlpha1 := (varName.toList.get? 1).map (fun c => if c.isAlpha then false else true) |>.getD false
  let upper1 := (varName.toList.get? 1).map (fun c => if c.isUpper then true else false) |>.getD false
  let hasLPrefix := lower.startsWith "l"
  let hasLPrefixWithUpper := enoughLen1 && upper1
  let isLPrefixWithUpper := hasLPrefix && hasLPrefixWithUpper
  let hasLPrefixNonAlpha := enoughLen1 && nonAlpha1
  let isLPrefixWithNonAlpha := hasLPrefix && hasLPrefixNonAlpha
  -- Remove common prefixes
  let noPrefix :=
    if lower.startsWith "line_" then varName.drop 5
    else if lower.startsWith "line-" then varName.drop 5
    else if isLinePrefixWithNonAlpha then varName.drop 4
    else if lower.startsWith "l_" then varName.drop 2
    else if lower.startsWith "l-" then varName.drop 2
    else if isLPrefixWithUpper then varName.drop 1
    else if isLPrefixWithNonAlpha then varName.drop 1
    else if lower.startsWith "l" && varName.length > 1 then varName.drop 1
    else varName
  -- Remove common suffixes
  let noSuffix :=
    if noPrefix.endsWith "line" then noPrefix.dropRight 4
    else if noPrefix.endsWith "_line" then noPrefix.dropRight 5
    else if noPrefix.endsWith "-line" then noPrefix.dropRight 5
    else if noPrefix.endsWith "Line" then noPrefix.dropRight 4
    else if noPrefix.endsWith "_Line" then noPrefix.dropRight 5
    else if noPrefix.endsWith "-Line" then noPrefix.dropRight 5
    else if noPrefix.endsWith "LINE" then noPrefix.dropRight 4
    else if noPrefix.endsWith "_LINE" then noPrefix.dropRight 5
    else if noPrefix.endsWith "-LINE" then noPrefix.dropRight 5
    else noPrefix
  -- Remove leading/trailing underscores or dashes
  let trimmed := noSuffix.trim
  let trimmed :=
    if trimmed.startsWith "_" then trimmed.drop 1 else trimmed
  let trimmed :=
    if trimmed.startsWith "-" then trimmed.drop 1 else trimmed
  let trimmed :=
    if trimmed.endsWith "_" then trimmed.dropRight 1 else trimmed
  let trimmed :=
    if trimmed.endsWith "-" then trimmed.dropRight 1 else trimmed
  trimmed

/-- Helper function to extract point name from various formats --/
def extractPointName (varName : String) : String :=
  let lower := varName.toLower
  let enoughLen1 := decide (varName.length > 1)
  let nonAlpha1 := (varName.toList.get? 1).map (fun c => if c.isAlpha then false else true) |>.getD false
  let upper1 := (varName.toList.get? 1).map (fun c => if c.isUpper then true else false) |>.getD false
  let hasPPrefix := lower.startsWith "p"
  let hasPPrefixWithUpper := enoughLen1 && upper1
  let isPPrefixWithUpper := hasPPrefix && hasPPrefixWithUpper
  let hasPPrefixNonAlpha := enoughLen1 && nonAlpha1
  let isPPrefixWithNonAlpha := hasPPrefix && hasPPrefixNonAlpha
  -- Remove common prefixes
  let noPrefix :=
    if lower.startsWith "point_" then varName.drop 6
    else if lower.startsWith "point-" then varName.drop 6
    else if lower.startsWith "point" then varName.drop 5
    else if lower.startsWith "pt_" then varName.drop 3
    else if lower.startsWith "pt-" then varName.drop 3
    else if lower.startsWith "pt" then varName.drop 2
    else if lower.startsWith "p_" then varName.drop 2
    else if lower.startsWith "p-" then varName.drop 2
    else if isPPrefixWithUpper then varName.drop 1
    else if isPPrefixWithNonAlpha then varName.drop 1
    else varName
  -- Remove common suffixes
  let noSuffix :=
    if noPrefix.endsWith "_point" then noPrefix.dropRight 6
    else if noPrefix.endsWith "-point" then noPrefix.dropRight 6
    else if noPrefix.endsWith "point" then noPrefix.dropRight 5
    else if noPrefix.endsWith "_pt" then noPrefix.dropRight 3
    else if noPrefix.endsWith "-pt" then noPrefix.dropRight 3
    else if noPrefix.endsWith "pt" then noPrefix.dropRight 2
    else if noPrefix.endsWith "_P" then noPrefix.dropRight 2
    else if noPrefix.endsWith "-P" then noPrefix.dropRight 2
    else if noPrefix.endsWith "P" && noPrefix.length > 1 then noPrefix.dropRight 1
    else noPrefix
  -- Remove leading/trailing underscores or dashes
  let trimmed := noSuffix.trim
  let trimmed :=
    if trimmed.startsWith "_" then trimmed.drop 1 else trimmed
  let trimmed :=
    if trimmed.startsWith "-" then trimmed.drop 1 else trimmed
  let trimmed :=
    if trimmed.endsWith "_" then trimmed.dropRight 1 else trimmed
  let trimmed :=
    if trimmed.endsWith "-" then trimmed.dropRight 1 else trimmed
  trimmed


/-- Helper: Normalize line names by sorting constituent points --/
def normalizeLineName (name : String) : String :=
  -- First, do preprocessing to extract the core name
  let preprocessed := extractLineName name

  -- Check if the preprocessed result is exactly 2 alphabetical characters
  if preprocessed.length == 2 && preprocessed.all (fun c => c.isAlpha) then
    -- Apply sorting + uppercase for 2-character alphabetical names
    let upperName := preprocessed.toUpper
    let chars := upperName.toList
    match chars with
    | [c1, c2] =>
      if c1 ≤ c2 then String.mk [c1, c2] else String.mk [c2, c1]
    | _ => upperName
  else
    -- For other cases, revert preprocessing and only apply case-insensitive normalization
    name.toUpper

/-- Helper: Normalize point names to uppercase for case-insensitive unification --/
def normalizePointName (name : String) : String :=
  name.toUpper  -- Convert to uppercase for case-insensitive unification

/-- Helper function to preprocess and normalize variable names to extract canonical forms --/
def preprocessVariableName (varName : String) (varType : String) : String :=
  if varType == "Line" then
    let extracted := extractLineName varName
    normalizeLineName extracted
  else if varType == "Point" then
    let extracted := extractPointName varName
    normalizePointName extracted
  else if varType == "Circle" then
    -- For circles name, don't do anything
    varName
  else
    -- Return a special error marker instead of panicking
    s!"ERROR: Unexpected variable type: {varType}. Expected one of: Point, Line, Circle"

/-- Helper function to check subset relationship between two variable lists -/
def checkSubset (testVars groundVars : List (String × String)) : Bool :=
  let groundSet := groundVars.foldl (fun acc var => acc.insert var) (HashSet.empty : HashSet (String × String))
  testVars.all (fun var => groundSet.contains var)

/-- Helper function to check if two variable lists have a non-empty intersection -/
def checkIntersection (testVars groundVars : List (String × String)) : Bool :=
  let groundSet := groundVars.foldl (fun acc var => acc.insert var) (HashSet.empty : HashSet (String × String))
  let intersection := testVars.filter (fun var => groundSet.contains var)
  !intersection.isEmpty

/-- Helper function to compute union of two variable lists -/
def unionVariables (vars1 vars2 : List (String × String)) : List (String × String) :=
  let set1 := vars1.foldl (fun acc var => acc.insert var) (HashSet.empty : HashSet (String × String))
  let unionSet := set1.fold (fun acc var => acc.insert var) vars2
  unionSet

/-- Helper function to rebuild quantified expression with only used variables -/
def rebuildWithUsedVars (vars : List (String × String)) (usedVars : HashSet String) (body : EAssertion) : EAssertion :=
  vars.foldr (fun (varName, varType) acc =>
    if usedVars.contains varName then .all varName varType acc else acc) body

/-- Helper function to extract raw premises and conclusion from an implication (without quantifiers) -/
def extractRawPremisesAndConclusion (expr : EAssertion) : MetaM (EAssertion × EAssertion) := do
  -- Find the innermost implication by stripping all quantifiers
  let rec findImplication (e : EAssertion) : EAssertion :=
    match e with
    | .all _ _ body => findImplication body
    | _ => e

  let innerExpr := findImplication expr
  match innerExpr with
  | .imp premises conclusion =>
    return (premises, conclusion)
  | _ => throwError "[E3] Error: Expected implication structure (possibly with quantifiers) for separate mode, got: {expr}"

/-- Helper function to construct properly quantified implication between two assertions -/
def constructQuantifiedImplication (antecedent consequent : EAssertion) (originalVars : List (String × String)) : EAssertion :=
  -- Collect free variables in both antecedent and consequent
  let antecedentFreeVars := collectFreeVars antecedent
  let consequentFreeVars := collectFreeVars consequent

  -- Find union of variables used in both
  let allUsedVars := unionHashSet antecedentFreeVars consequentFreeVars

  -- Create the implication
  let innerImplication := EAssertion.imp antecedent consequent

  -- Wrap with quantifiers for all used variables
  rebuildWithUsedVars originalVars allUsedVars innerImplication

/-- Helper function to check satisfiability of an assertion and its negation -/
def checkSatisfiabilityDetailed (assertion : EAssertion) (timeout : Nat) (additionalAxioms : List String := []) : PropEvalM (String × String) := do
  let negAssertion : EAssertion := .neg assertion

  IO.println "------------------------------------------------------------"
  IO.println "Running Assertion and Negation checks ..."

  let assertionTask := Task.spawn (fun _ => do
    IO.println "Checking Assertion ..."
    -- Since the assertion is very likely to be true, the SMT solver will most likely
    -- timeout, so we use a small fixed time limit (5s) here
    evalSmt' true none 5 assertion additionalAxioms)

  let negationTask := Task.spawn (fun _ => do
    IO.println "Checking Negation ..."
    -- We expect the negation to be UNSAT, so we use the user-defined timeout
    evalSmt' true none timeout negAssertion additionalAxioms)

  -- Get results from both tasks
  let assertionResult ← assertionTask.get
  let negationResult ← negationTask.get

  return (assertionResult, negationResult)

/-- Function to normalize EAssertion variable names according to mapping -/
def normalizeEAssertion (expr : EAssertion) (mapping : HashMap String String) : EAssertion :=
  let normalizeVar (varName : String) : String := mapping.findD varName varName
  let normalizeExpression (s : String) : String :=
    -- Handle angle expressions in both formats:
    -- Format 1: "AnglePPP V W T" (without outer parentheses)
    -- Format 2: "(AnglePPP V W T)" (with outer parentheses)
    if s.startsWith "AnglePPP " then
      -- Format 1: "AnglePPP V W T"
      let content := s.drop 9  -- Remove "AnglePPP "
      let tokens := content.split (· == ' ')
      if tokens.length == 3 then
        let side1 := normalizeVar tokens[0]!  -- First side point
        let vertex := normalizeVar tokens[1]! -- Vertex (always middle)
        let side2 := normalizeVar tokens[2]!  -- Second side point

        -- Enhanced angle normalization:
        -- 1. First, try to normalize by ordering the side points alphabetically, keep vertex in middle
        -- 2. If that doesn't help, try to identify equivalent angles based on geometric properties

        -- Standard normalization: order side points alphabetically
        let normalized := if side1 < side2 || side1 == side2 then
          s!"AnglePPP {side1} {vertex} {side2}"
        else
          s!"AnglePPP {side2} {vertex} {side1}"

        -- Additional normalization: try to identify equivalent angles
        -- This is a heuristic to help the SMT solver recognize equivalent angles
        -- For example, if we have angles that should be equivalent based on the problem context
        normalized
      else
        -- Return error message instead of panicking
        s!"ERROR: Malformed angle expression: expected 3 tokens, got {tokens.length} in '{s}'"
    else if s.startsWith "(AnglePPP " && s.endsWith ")" then
      -- Format 2: "(AnglePPP V W T)"
      let content := s.drop 10 |>.dropRight 1  -- Remove "(AnglePPP " and ")"
      let tokens := content.split (· == ' ')
      if tokens.length == 3 then
        let side1 := normalizeVar tokens[0]!  -- First side point
        let vertex := normalizeVar tokens[1]! -- Vertex (always middle)
        let side2 := normalizeVar tokens[2]!  -- Second side point

        -- Enhanced angle normalization (same as above)
        let normalized := if side1 < side2 || side1 == side2 then
          s!"(AnglePPP {side1} {vertex} {side2})"
        else
          s!"(AnglePPP {side2} {vertex} {side1})"

        normalized
      else
        -- Return error message instead of panicking
        s!"ERROR: Malformed angle expression: expected 3 tokens, got {tokens.length} in '{s}'"
    else normalizeVar s
  match expr with
  | .top => .top
  | .erel r => .erel (normalizeRelation r mapping)
  | .eq a b => .eq (normalizeExpression a) (normalizeExpression b)
  | .lt a b => .lt (normalizeExpression a) (normalizeExpression b)
  | .lte a b => .lte (normalizeExpression a) (normalizeExpression b)
  | .gt a b => .gt (normalizeExpression a) (normalizeExpression b)
  | .gte a b => .gte (normalizeExpression a) (normalizeExpression b)
  | .neg x => .neg (normalizeEAssertion x mapping)
  | .ex x t p => .ex (normalizeVar x) t (normalizeEAssertion p mapping)
  | .all x t p => .all (normalizeVar x) t (normalizeEAssertion p mapping)
  | .or a b => .or (normalizeEAssertion a mapping) (normalizeEAssertion b mapping)
  | .and a b => .and (normalizeEAssertion a mapping) (normalizeEAssertion b mapping)
  | .imp a b => .imp (normalizeEAssertion a mapping) (normalizeEAssertion b mapping)

where normalizeRelation (r : SystemE.Smt.ERelation) (mapping : HashMap String String) : SystemE.Smt.ERelation :=
  let normalizeVar (varName : String) : String := mapping.findD varName varName
  match r with
  | .OnL p l => .OnL (normalizeVar p) (normalizeVar l)
  | .OnC p c => .OnC (normalizeVar p) (normalizeVar c)
  | .Centre p c => .Centre (normalizeVar p) (normalizeVar c)
  | .InC p c => .InC (normalizeVar p) (normalizeVar c)
  | .SameSide p q l => .SameSide (normalizeVar p) (normalizeVar q) (normalizeVar l)
  | .Between p q r => .Between (normalizeVar p) (normalizeVar q) (normalizeVar r)
  | .IntersectsLL l1 l2 => .IntersectsLL (normalizeVar l1) (normalizeVar l2)
  | .IntersectsLC l c => .IntersectsLC (normalizeVar l) (normalizeVar c)
  | .IntersectsCC c1 c2 => .IntersectsCC (normalizeVar c1) (normalizeVar c2)

/-- Helper: Normalize a variable (name, type) pair --/
def normalizeVariable (name : String) (varType : String) : (String × String) :=
  (preprocessVariableName name varType, varType)

/-- Helper function to create mapping from all variable names to canonical (normalized) forms --/
def createCanonicalMapping (testVars groundVars : List (String × String)) : HashMap String String :=
  let allVars := testVars ++ groundVars
  allVars.foldl (fun acc (varName, varType) =>
    let canonical := preprocessVariableName varName varType
    acc.insert varName canonical
  ) HashMap.empty

/-- Helper function to verify variable consistency in implication quantifiers --/
def verifyImplication (name : String) (impl : EAssertion) (expectedVars : List (String × String)) : IO Bool := do
  let implQuantifiedVars := collectQuantifiedVars impl
  let expectedVarNames := expectedVars.map (·.1)
  let implVarNames := implQuantifiedVars.map (·.1)
  let expectedSet := expectedVarNames.foldl (·.insert ·) HashSet.empty
  let implSet := implVarNames.foldl (·.insert ·) HashSet.empty
  if expectedSet == implSet then do
    IO.println s!"{name}: Quantifier declarations match exactly with used variables"
    return true
  else do
    IO.println s!"❌ {name}: Quantifier declaration mismatch!"
    IO.println s!"   Expected declarations: {expectedVars}"
    IO.println s!"   Found declarations: {implQuantifiedVars}"
    IO.println s!"   Expected var names: {expectedVarNames}"
    IO.println s!"   Found var names: {implVarNames}"
    return false

/-- Enum to specify which direction(s) to check in separate mode -/
inductive SeparateCheckDirection
| testToGroundOnly
| groundToTestOnly
| bothDirections


/-- Separate mode implementation: Check equivalence of premises and conclusions separately -/
def runSeparateCheckImpl (direction : SeparateCheckDirection := .bothDirections) : PropEvalM SeparateResult := do
  let test ← translateTestExpr
  let ground ← translateGroundExpr

  IO.println "============================================================"
  IO.println ("[SEPARATE MODE] Checking variable declarations for " ++
    match direction with
    | .testToGroundOnly => "Test → Ground only"
    | .groundToTestOnly => "Ground → Test only"
    | .bothDirections => "Both Directions")

  -- Step 1: Extraction
  let testVars := collectQuantifiedVars test
  let groundVars := collectQuantifiedVars ground

  -- Step 2: Normalization
  let testVarsNormalized := testVars.map (fun (name, varType) => normalizeVariable name varType)
  let groundVarsNormalized := groundVars.map (fun (name, varType) => normalizeVariable name varType)

  -- Log any variable preprocessing that occurred
  for (name, varType) in testVars do
    let normalized := normalizeVariable name varType
    if normalized.1 != name then
      IO.println s!"[VARIABLE PREPROCESSING] {varType} variable '{name}' → '{normalized.1}'"

  for (name, varType) in groundVars do
    let normalized := normalizeVariable name varType
    if normalized.1 != name then
      IO.println s!"[VARIABLE PREPROCESSING] {varType} variable '{name}' → '{normalized.1}'"

  IO.println "------------------------------------------------------------"

  -- Check for error messages in variable preprocessing
  let hasVariableError :=
    testVarsNormalized.any (fun (name, _) => name.startsWith "ERROR:") ||
    groundVarsNormalized.any (fun (name, _) => name.startsWith "ERROR:")

  if hasVariableError then do
    IO.println "============================================================"
    IO.println "[ERROR DETECTION] Found error messages in variable preprocessing:"
    IO.println s!"Test variables: {testVarsNormalized}"
    IO.println s!"Ground variables: {groundVarsNormalized}"
    IO.println "============================================================"
    return {
      premisesTestImpGroundAssertion := "variable preprocessing error"
      premisesTestImpGroundNegation := "variable preprocessing error"
      premisesGroundImpTestAssertion := "variable preprocessing error"
      premisesGroundImpTestNegation := "variable preprocessing error"
      conclusionsTestImpGroundAssertion := "variable preprocessing error"
      conclusionsTestImpGroundNegation := "variable preprocessing error"
      conclusionsGroundImpTestAssertion := "variable preprocessing error"
      conclusionsGroundImpTestNegation := "variable preprocessing error"
    }

  -- Step 3: Check variable compatibility with different rules for different types
  -- For Points: Check (Test ⊆ Ground) ∨ (Ground ⊆ Test)
  -- For Lines: Check if (Test ∩ Ground) ≠ ∅ (if they overlap)
  -- For Circles: Check (Test ⊆ Ground) ∨ (Ground ⊆ Test) (same as points)

  let testPoints := testVarsNormalized.filter (fun (_, varType) => varType == "Point")
  let testLines := testVarsNormalized.filter (fun (_, varType) => varType == "Line")
  let testCircles := testVarsNormalized.filter (fun (_, varType) => varType == "Circle")

  let groundPoints := groundVarsNormalized.filter (fun (_, varType) => varType == "Point")
  let groundLines := groundVarsNormalized.filter (fun (_, varType) => varType == "Line")
  let groundCircles := groundVarsNormalized.filter (fun (_, varType) => varType == "Circle")

  -- Check point compatibility: (Test ⊆ Ground) ∨ (Ground ⊆ Test)
  let testPointsSubsetGround := checkSubset testPoints groundPoints
  let groundPointsSubsetTest := checkSubset groundPoints testPoints
  let pointsCompatible := testPointsSubsetGround || groundPointsSubsetTest

  -- Check line compatibility: (Test ∩ Ground) ≠ ∅
  let linesCompatible := checkIntersection testLines groundLines

  -- Check circle compatibility: (Test ⊆ Ground) ∨ (Ground ⊆ Test) (same as points)
  let testCirclesSubsetGround := checkSubset testCircles groundCircles
  let groundCirclesSubsetTest := checkSubset groundCircles testCircles
  let circlesCompatible := testCirclesSubsetGround || groundCirclesSubsetTest

  let allCompatible := pointsCompatible && linesCompatible && circlesCompatible

  if !allCompatible then do
    -- Build detailed error message indicating which variable types are incompatible
    let incompatibleTypes : List String := []
    let incompatibleTypes := if !pointsCompatible then incompatibleTypes ++ ["points"] else incompatibleTypes
    let incompatibleTypes := if !linesCompatible then incompatibleTypes ++ ["lines"] else incompatibleTypes
    let incompatibleTypes := if !circlesCompatible then incompatibleTypes ++ ["circles"] else incompatibleTypes

    let varIncompatibleMessage :=
      if incompatibleTypes.length == 1 then
        s!"variable incompatible ({incompatibleTypes[0]!})"
      else if incompatibleTypes.length == 2 then
        s!"variable incompatible ({incompatibleTypes[0]!}, {incompatibleTypes[1]!})"
      else
        s!"variable incompatible ({incompatibleTypes[0]!}, {incompatibleTypes[1]!}, {incompatibleTypes[2]!})"

    IO.println s!"Variable declarations incompatible!"
    IO.println s!"Test variables: {testVars}"
    IO.println s!"Ground variables: {groundVars}"
    IO.println "------------------------------------------------------------"
    IO.println s!"Points compatible: {pointsCompatible} (Test ⊆ Ground: {testPointsSubsetGround}, Ground ⊆ Test: {groundPointsSubsetTest})"
    IO.println s!"Lines compatible: {linesCompatible}"
    IO.println s!"Circles compatible: {circlesCompatible} (Test ⊆ Ground: {testCirclesSubsetGround}, Ground ⊆ Test: {groundCirclesSubsetTest})"
    IO.println "------------------------------------------------------------"
    IO.println s!"Test points: {testPoints}"
    IO.println s!"Ground points: {groundPoints}"
    IO.println "------------------------------------------------------------"
    IO.println s!"Test lines: {testLines}"
    IO.println s!"Ground lines: {groundLines}"
    IO.println "------------------------------------------------------------"
    IO.println s!"Test circles: {testCircles}"
    IO.println s!"Ground circles: {groundCircles}"
    IO.println "------------------------------------------------------------"
    IO.println s!"Variable compatibility check failed - cannot determine equivalence. Incompatible types: {incompatibleTypes}"
    return {
      premisesTestImpGroundAssertion := varIncompatibleMessage
      premisesTestImpGroundNegation := varIncompatibleMessage
      premisesGroundImpTestAssertion := varIncompatibleMessage
      premisesGroundImpTestNegation := varIncompatibleMessage
      conclusionsTestImpGroundAssertion := varIncompatibleMessage
      conclusionsTestImpGroundNegation := varIncompatibleMessage
      conclusionsGroundImpTestAssertion := varIncompatibleMessage
      conclusionsGroundImpTestNegation := varIncompatibleMessage
    }

  -- Create variable declarations by taking union of all variables from both test and ground
  let maxDeclarations := unionVariables testVarsNormalized groundVarsNormalized

  IO.println "------------------------------------------------------------"
  IO.println s!"Points Compatibility: {pointsCompatible} (Test ⊆ Ground: {testPointsSubsetGround}, Ground ⊆ Test: {groundPointsSubsetTest})"
  IO.println s!"Lines Compatibility: {linesCompatible}"
  IO.println s!"Circles Compatibility: {circlesCompatible} (Test ⊆ Ground: {testCirclesSubsetGround}, Ground ⊆ Test: {groundCirclesSubsetTest})"
  IO.println "------------------------------------------------------------"
  IO.println s!"Test variables: {testVarsNormalized}"
  IO.println s!"Ground variables: {groundVarsNormalized}"
  IO.println s!"Union declarations: {maxDeclarations}"
  IO.println "------------------------------------------------------------"

  -- Extract raw premises and conclusions from test and ground
  let (testPremises, testConclusion) ← extractRawPremisesAndConclusion test
  let (groundPremises, groundConclusion) ← extractRawPremisesAndConclusion ground

  IO.println s!"Test premises: {testPremises}"
  IO.println s!"Test conclusion: {testConclusion}"
  IO.println "------------------------------------------------------------"
  IO.println s!"Ground premises: {groundPremises}"
  IO.println s!"Ground conclusion: {groundConclusion}"

  IO.println "============================================================"
  IO.println "[SEPARATE MODE] Constructing quantified implications ..."

  let canonicalMapping := createCanonicalMapping testVars groundVars

  -- Normalize BOTH test and ground to use canonical variable names
  let normalizedTestPremises := normalizeEAssertion testPremises canonicalMapping
  let normalizedTestConclusions := normalizeEAssertion testConclusion canonicalMapping
  let normalizedGroundPremises := normalizeEAssertion groundPremises canonicalMapping
  let normalizedGroundConclusions := normalizeEAssertion groundConclusion canonicalMapping

  -- Check for error messages in normalized expressions
  let hasError :=
    let testPremisesStr := toString normalizedTestPremises
    let testConclusionsStr := toString normalizedTestConclusions
    let groundPremisesStr := toString normalizedGroundPremises
    let groundConclusionsStr := toString normalizedGroundConclusions
    stringContains testPremisesStr "ERROR:" || stringContains testConclusionsStr "ERROR:" ||
    stringContains groundPremisesStr "ERROR:" || stringContains groundConclusionsStr "ERROR:"

  if hasError then do
    IO.println "============================================================"
    IO.println "[ERROR DETECTION] Found error messages in normalized expressions:"
    IO.println "------------------------------------------------------------"
    IO.println s!"Test premises: {normalizedTestPremises}"
    IO.println s!"Test conclusions: {normalizedTestConclusions}"
    IO.println s!"Ground premises: {normalizedGroundPremises}"
    IO.println s!"Ground conclusions: {normalizedGroundConclusions}"
    IO.println "============================================================"
    return {
      premisesTestImpGroundAssertion := "normalization error"
      premisesTestImpGroundNegation := "normalization error"
      premisesGroundImpTestAssertion := "normalization error"
      premisesGroundImpTestNegation := "normalization error"
      conclusionsTestImpGroundAssertion := "normalization error"
      conclusionsTestImpGroundNegation := "normalization error"
      conclusionsGroundImpTestAssertion := "normalization error"
      conclusionsGroundImpTestNegation := "normalization error"
    }

  -- Check if normalization actually happened
  IO.println "============================================================"
  IO.println "[NORMALIZATION] After normalization:"
  IO.println "------------------------------------------------------------"
  IO.println s!"Original test conclusion: {testConclusion}"
  IO.println s!"Normalized test conclusion: {normalizedTestConclusions}"
  IO.println s!"Original ground conclusion: {groundConclusion}"
  IO.println s!"Normalized ground conclusion: {normalizedGroundConclusions}"
  IO.println "============================================================"

  -- Create normalized variable list for quantifier construction
  let normalizedVarList := maxDeclarations.foldl
    (fun acc var => if acc.contains var then acc else acc ++ [var]) []

  IO.println s!"testVars = {testVars}"
  IO.println s!"groundVars = {groundVars}"
  IO.println s!"maxDeclarations = {maxDeclarations}"
  IO.println s!"normalizedVarList = {normalizedVarList}"
  IO.println s!"canonicalMapping = {canonicalMapping.toList}"

  -- Step 4: Construct implications using only used variables for each case
  IO.println "------------------------------------------------------------"
  IO.println "[SEPARATE MODE] Constructing implications with used variables only ..."
  IO.println "------------------------------------------------------------"

  -- For premises implications: collect variables used in both premises
  let testPremisesVars := collectFreeVars normalizedTestPremises
  let groundPremisesVars := collectFreeVars normalizedGroundPremises
  let premisesUsedVars := (testPremisesVars.toList ++ groundPremisesVars.toList).eraseDups
  let premisesVarDeclarations := maxDeclarations.filter (fun (varName, _) => premisesUsedVars.contains varName)

  -- For conclusions implications: collect variables used in both conclusions AND ground premises
  let testConclusionVars := collectFreeVars normalizedTestConclusions
  let groundConclusionVars := collectFreeVars normalizedGroundConclusions
  let groundPremisesVars := collectFreeVars normalizedGroundPremises
  let conclusionsUsedVars := (testConclusionVars.toList ++ groundConclusionVars.toList ++ groundPremisesVars.toList).eraseDups
  let conclusionsVarDeclarations := maxDeclarations.filter (fun (varName, _) => conclusionsUsedVars.contains varName)

  IO.println s!"Premises used variables: {premisesUsedVars}"
  IO.println s!"Premises declarations: {premisesVarDeclarations}"
  IO.println s!"Conclusions used variables: {conclusionsUsedVars}"
  IO.println s!"Conclusions declarations: {conclusionsVarDeclarations}"

  -- Construct Implications based on which direction we're checking
  -- For conclusions, we use the optimized form: instead of checking ∀ variables, (p ∧ q) → (p ∧ q'),
  -- we check ∀ variables, (p ∧ q) → q' since ∀ variables, (p ∧ q) → p is always true
  let testWithGroundPremises := EAssertion.and normalizedGroundPremises normalizedTestConclusions
  let groundWithGroundPremises := EAssertion.and normalizedGroundPremises normalizedGroundConclusions
  let (premisesTestImpGround, premisesGroundImpTest, conclusionsTestImpGround, conclusionsGroundImpTest) :=
    match direction with
    | .bothDirections =>
      -- Check both directions (original behavior)
      let premisesTestImpGround := constructQuantifiedImplication normalizedTestPremises normalizedGroundPremises premisesVarDeclarations
      let premisesGroundImpTest := constructQuantifiedImplication normalizedGroundPremises normalizedTestPremises premisesVarDeclarations
      -- Optimized: check ∀ variables, (p ∧ q') → q
      let conclusionsTestImpGround := constructQuantifiedImplication testWithGroundPremises normalizedGroundConclusions conclusionsVarDeclarations
      -- Optimized: check ∀ variables, (p ∧ q) → q'
      let conclusionsGroundImpTest := constructQuantifiedImplication groundWithGroundPremises normalizedTestConclusions conclusionsVarDeclarations
      (premisesTestImpGround, premisesGroundImpTest, conclusionsTestImpGround, conclusionsGroundImpTest)
    | .testToGroundOnly =>
      -- Check only test->ground direction
      let premisesTestImpGround := constructQuantifiedImplication normalizedTestPremises normalizedGroundPremises premisesVarDeclarations
      -- Optimized: check ∀ variables, (p ∧ q') → q
      let conclusionTestImpGround := constructQuantifiedImplication testWithGroundPremises normalizedGroundConclusions conclusionsVarDeclarations
      (premisesTestImpGround, EAssertion.top, conclusionTestImpGround, EAssertion.top)
    | .groundToTestOnly =>
      -- Check only ground->test direction
      let premisesGroundImpTest := constructQuantifiedImplication normalizedGroundPremises normalizedTestPremises premisesVarDeclarations
      -- Optimized: check ∀ variables, (p ∧ q) → q'
      let conclusionsGroundImpTest := constructQuantifiedImplication groundWithGroundPremises normalizedTestConclusions conclusionsVarDeclarations
      (EAssertion.top, premisesGroundImpTest, EAssertion.top, conclusionsGroundImpTest)

  IO.println "------------------------------------------------------------"
  match direction with
  | .bothDirections =>
    IO.println ("Premises Test → Ground: Assertion=" ++ toString premisesTestImpGround)
    IO.println ("Premises Ground → Test: " ++ toString premisesGroundImpTest)
    IO.println ("Conclusions Test → Ground (with ground premises): " ++ toString conclusionsTestImpGround)
    IO.println ("Conclusions Ground → Test (with ground premises): " ++ toString conclusionsGroundImpTest)
  | .testToGroundOnly => do
    IO.println ("Premises Test → Ground: " ++ toString premisesTestImpGround)
    IO.println ("Conclusions Test → Ground: " ++ toString conclusionsTestImpGround)
  | .groundToTestOnly => do
    IO.println ("Premises Ground → Test: " ++ toString premisesGroundImpTest)
    IO.println ("Conclusions Ground → Test: " ++ toString conclusionsGroundImpTest)

  -- Step 5: Final checking - verify variables in implications match declarations
  IO.println "------------------------------------------------------------"
  IO.println "[SEPARATE MODE] Verifying variable consistency ..."
  IO.println "------------------------------------------------------------"

  let premisesTestImpGroundOK ← match direction with
    | .bothDirections => verifyImplication "Premises test→ground" premisesTestImpGround premisesVarDeclarations
    | .testToGroundOnly => verifyImplication "Premises test→ground" premisesTestImpGround premisesVarDeclarations
    | .groundToTestOnly => pure true  -- Skip verification for test→ground in ground→test only mode
  let premisesGroundImpTestOK ← match direction with
    | .bothDirections => verifyImplication "Premises ground→test" premisesGroundImpTest premisesVarDeclarations
    | .groundToTestOnly => verifyImplication "Premises ground→test" premisesGroundImpTest premisesVarDeclarations
    | .testToGroundOnly => pure true  -- Skip verification for ground→test in test→ground only mode
  let conclusionsTestImpGroundOK ← match direction with
    | .bothDirections => verifyImplication "Conclusions test→ground" conclusionsTestImpGround conclusionsVarDeclarations
    | .testToGroundOnly => verifyImplication "Conclusions test→ground" conclusionsTestImpGround conclusionsVarDeclarations
    | .groundToTestOnly => pure true  -- Skip verification for test→ground in ground→test only mode
  let conclusionsGroundImpTestOK ← match direction with
    | .bothDirections => verifyImplication "Conclusions ground→test" conclusionsGroundImpTest conclusionsVarDeclarations
    | .groundToTestOnly => verifyImplication "Conclusions ground→test" conclusionsGroundImpTest conclusionsVarDeclarations
    | .testToGroundOnly => pure true  -- Skip verification for ground→test in test→ground only mode

  if !premisesTestImpGroundOK || !premisesGroundImpTestOK || !conclusionsTestImpGroundOK || !conclusionsGroundImpTestOK then do
    IO.println "❌ Variable verification failed! Implications have incorrect variable declarations."
    return {
      premisesTestImpGroundAssertion := "variable verification failed"
      premisesTestImpGroundNegation := "variable verification failed"
      premisesGroundImpTestAssertion := "variable verification failed"
      premisesGroundImpTestNegation := "variable verification failed"
      conclusionsTestImpGroundAssertion := "variable verification failed"
      conclusionsTestImpGroundNegation := "variable verification failed"
      conclusionsGroundImpTestAssertion := "variable verification failed"
      conclusionsGroundImpTestNegation := "variable verification failed"
    }

  IO.println "============================================================"
  IO.println "[SEPARATE MODE] Checking implications ..."

  -- Step 6: Check implications based on direction
  -- Check for exact matches first (outside tasks to avoid redundancy)
  let premisesExactMatch := normalizedTestPremises == normalizedGroundPremises
  let conclusionsExactMatch := normalizedTestConclusions == normalizedGroundConclusions

  if premisesExactMatch then
    IO.println "Premises are exact matches! Skipping SMT checks ..."
  if conclusionsExactMatch then
    IO.println "Conclusions are exact matches! Skipping SMT checks ..."

  let (premisesTestImpGroundAssertion, premisesTestImpGroundNegation, premisesGroundImpTestAssertion, premisesGroundImpTestNegation,
       conclusionsTestImpGroundAssertion, conclusionsTestImpGroundNegation, conclusionsGroundImpTestAssertion, conclusionsGroundImpTestNegation) ←
    match direction with
    | .bothDirections => do
      -- All 4 SMT solver calls run
      let cfg ← getEvalConfig

      -- Create tasks for all 4 checks
      let premisesTestToGroundTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if premisesExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Premises Test → Ground ..."
          checkSatisfiabilityDetailed premisesTestImpGround cfg.equivSolverTime [])

      let premisesGroundToTestTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if premisesExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Premises Ground → Test ..."
          checkSatisfiabilityDetailed premisesGroundImpTest cfg.equivSolverTime [])

      let conclusionsTestToGroundTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if conclusionsExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Conclusions Test → Ground ..."
          checkSatisfiabilityDetailed conclusionsTestImpGround cfg.equivSolverTime [])

      let conclusionsGroundToTestTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if conclusionsExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Conclusions Ground → Test ..."
          checkSatisfiabilityDetailed conclusionsGroundImpTest cfg.equivSolverTime [])

      IO.println "------------------------------------------------------------"
      IO.println "Running all 4 SMT checks ..."

      -- Get results from all 4 tasks
      let (premisesTestImpGroundAssertion, premisesTestImpGroundNegation) ← premisesTestToGroundTask.get
      let (premisesGroundImpTestAssertion, premisesGroundImpTestNegation) ← premisesGroundToTestTask.get
      let (conclusionsTestImpGroundAssertion, conclusionsTestImpGroundNegation) ← conclusionsTestToGroundTask.get
      let (conclusionsGroundImpTestAssertion, conclusionsGroundImpTestNegation) ← conclusionsGroundToTestTask.get

      pure (premisesTestImpGroundAssertion, premisesTestImpGroundNegation, premisesGroundImpTestAssertion, premisesGroundImpTestNegation,
            conclusionsTestImpGroundAssertion, conclusionsTestImpGroundNegation, conclusionsGroundImpTestAssertion, conclusionsGroundImpTestNegation)
    | .testToGroundOnly => do
      -- Check only test->ground direction
      let cfg ← getEvalConfig
      let premisesTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if premisesExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Premises Test → Ground ..."
          checkSatisfiabilityDetailed premisesTestImpGround cfg.equivSolverTime [])

      let conclusionsTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if conclusionsExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Conclusions Test → Ground ..."
          checkSatisfiabilityDetailed conclusionsTestImpGround cfg.equivSolverTime [])

      IO.println "------------------------------------------------------------"
      IO.println "Running Premises and Conclusions checks ..."

      let (premisesTestImpGroundAssertion, premisesTestImpGroundNegation) ← premisesTask.get
      let (conclusionsTestImpGroundAssertion, conclusionsTestImpGroundNegation) ← conclusionsTask.get

      pure (premisesTestImpGroundAssertion, premisesTestImpGroundNegation, "VALID", "UNSAT",
            conclusionsTestImpGroundAssertion, conclusionsTestImpGroundNegation, "VALID", "UNSAT")
    | .groundToTestOnly => do
      -- Check only ground->test direction
      let cfg ← getEvalConfig
      let premisesTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if premisesExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Premises Ground → Test ..."
          checkSatisfiabilityDetailed premisesGroundImpTest cfg.equivSolverTime [])

      let conclusionsTask := Task.spawn (fun _ =>
        -- If exact matches, skip SMT checks
        if conclusionsExactMatch then
          pure ("VALID", "UNSAT")
        else do
          IO.println "Checking Conclusions Ground → Test ..."
          checkSatisfiabilityDetailed conclusionsGroundImpTest cfg.equivSolverTime [])

      IO.println "------------------------------------------------------------"
      IO.println "Running Premises and Conclusions checks..."

      let (premisesGroundImpTestAssertion, premisesGroundImpTestNegation) ← premisesTask.get
      let (conclusionsGroundImpTestAssertion, conclusionsGroundImpTestNegation) ← conclusionsTask.get

      pure ("VALID", "UNSAT", premisesGroundImpTestAssertion, premisesGroundImpTestNegation,
            "VALID", "UNSAT", conclusionsGroundImpTestAssertion, conclusionsGroundImpTestNegation)

  IO.println "------------------------------------------------------------"
  match direction with
  | .bothDirections =>
    IO.println ("Premises Test → Ground: Assertion=" ++ premisesTestImpGroundAssertion ++ ", Negation=" ++ premisesTestImpGroundNegation)
    IO.println ("Premises Ground → Test: Assertion=" ++ premisesGroundImpTestAssertion ++ ", Negation=" ++ premisesGroundImpTestNegation)
    IO.println ("Conclusions Test → Ground: Assertion=" ++ conclusionsTestImpGroundAssertion ++ ", Negation=" ++ conclusionsTestImpGroundNegation)
    IO.println ("Conclusions Ground → Test: Assertion=" ++ conclusionsGroundImpTestAssertion ++ ", Negation=" ++ conclusionsGroundImpTestNegation)
  | .testToGroundOnly =>
    IO.println ("Premises Test → Ground: Assertion=" ++ premisesTestImpGroundAssertion ++ ", Negation=" ++ premisesTestImpGroundNegation)
    IO.println ("Conclusions Test → Ground: Assertion=" ++ conclusionsTestImpGroundAssertion ++ ", Negation=" ++ conclusionsTestImpGroundNegation)
  | .groundToTestOnly =>
    IO.println ("Premises Ground → Test: Assertion=" ++ premisesGroundImpTestAssertion ++ ", Negation=" ++ premisesGroundImpTestNegation)
    IO.println ("Conclusions Ground → Test: Assertion=" ++ conclusionsGroundImpTestAssertion ++ ", Negation=" ++ conclusionsGroundImpTestNegation)
  IO.println "============================================================"

  let separateResult : SeparateResult := {
    premisesTestImpGroundAssertion := premisesTestImpGroundAssertion,
    premisesTestImpGroundNegation := premisesTestImpGroundNegation,
    premisesGroundImpTestAssertion := premisesGroundImpTestAssertion,
    premisesGroundImpTestNegation := premisesGroundImpTestNegation,
    conclusionsTestImpGroundAssertion := conclusionsTestImpGroundAssertion,
    conclusionsTestImpGroundNegation := conclusionsTestImpGroundNegation,
    conclusionsGroundImpTestAssertion := conclusionsGroundImpTestAssertion,
    conclusionsGroundImpTestNegation := conclusionsGroundImpTestNegation
  }

  if (← getEvalConfig).writeResult = false then
    IO.println s!"[E3] Separate check result: {separateResult}"
    IO.println s!"Premises Equivalence: {separateResult.premisesEquiv}"
    IO.println s!"Conclusions Equivalence: {separateResult.conclusionsEquiv}"

  return separateResult


/-- Separate mode: Check equivalence of premises and conclusions separately -/
def runSeparateCheck (_ : EvalConfig) (ctx : EvalCtx) (old : E3Result) : MetaM E3Result := do
  let ⟨result, _⟩ ← runSeparateCheckImpl .bothDirections |>.run ctx
  return E3Result.addSeparateResult old result


/-- Pre-check function to validate Test expression before running equivalence checks.
    Returns Some(reason) if Test is invalid and checking should be skipped,
    Returns None if Test passes validation and checking should proceed -/
def runTestValidityPreCheck : PropEvalM (Option String) := do
  let test ← translateTestExpr
  IO.println "============================================================"

  -- Collect quantified variables from test
  let testVars := collectQuantifiedVars test

  -- Extract raw premises and conclusions from test
  let (testPremises, testConclusions) ← extractRawPremisesAndConclusion test

  IO.println "------------------------------------------------------------"
  IO.println s!"Test variables: {testVars}"
  IO.println s!"Test premises: {testPremises}"
  IO.println s!"Test conclusions: {testConclusions}"

  -- Collect variables actually used in premises and conclusions
  let premisesUsedVars := collectFreeVars testPremises
  let premisesVarDeclarations := testVars.filter (fun (varName, _) => premisesUsedVars.contains varName)
  let conclusionsUsedVars := collectFreeVars testConclusions
  let conclusionsVarDeclarations := testVars.filter (fun (varName, _) => conclusionsUsedVars.contains varName)

  IO.println s!"Premises used variables: {premisesUsedVars.toList}"
  IO.println s!"Premises variable declarations: {premisesVarDeclarations}"
  IO.println s!"Conclusions used variables: {conclusionsUsedVars.toList}"
  IO.println s!"Conclusions variable declarations: {conclusionsVarDeclarations}"

  -- Construct expressions for checking
  let negPremises := EAssertion.neg testPremises
  let quantifiedNegPremises := premisesVarDeclarations.foldr (fun (varName, varType) acc =>
    EAssertion.all varName varType acc) negPremises
  let negQuantifiedNegPremises := EAssertion.neg quantifiedNegPremises

  let quantifiedConclusions := conclusionsVarDeclarations.foldr (fun (varName, varType) acc =>
    EAssertion.all varName varType acc) testConclusions
  let negQuantifiedConclusions := EAssertion.neg quantifiedConclusions

  IO.println "------------------------------------------------------------"
  IO.println "[PRE-CHECK] Running 3 validation checks sequentially ..."
  IO.println "------------------------------------------------------------"

  -- Check 1: Test premises is contradictory
  IO.println "[PRE-CHECK] Checking if Test premises is contradictory ..."
  let premisesResult ← evalSmt' true none 5 negQuantifiedNegPremises []
  if premisesResult == "UNSAT" then do
    IO.println "[PRE-CHECK] ❌ Test premises is contradictory i.e. (∃ variables, test premises) is UNSAT - Test cannot be equivalent to Ground"
    IO.println "============================================================"
    return some "test_premises_contradictory"

  -- Check 2: Test conclusions is valid
  IO.println "[PRE-CHECK] Checking if Test conclusions is valid ..."
  let conclusionsResult ← evalSmt' true none 5 negQuantifiedConclusions []
  if conclusionsResult == "UNSAT" then do
    IO.println "[PRE-CHECK] ❌ Test conclusions is valid i.e. ¬(∀ variables, test conclusions) is UNSAT - Test cannot be equivalent to Ground"
    IO.println "============================================================"
    return some "test_conclusions_valid"

  -- Check 3: Test is a false statement
  IO.println "[PRE-CHECK] Checking if Test is a false statement under the background theory ..."
  let testResult ← evalSmt' true none 5 test []
  if testResult == "UNSAT" then do
    IO.println "[PRE-CHECK] ❌ Test is a false statement i.e. test is UNSAT - Test cannot be equivalent to Ground"
    IO.println "============================================================"
    return some "test_false"

  -- All checks passed
  IO.println "------------------------------------------------------------"
  IO.println "[PRE-CHECK] ✅ Test passes pre-check"
  IO.println "============================================================"
  return none


/-- Pre-Check+Separate mode implementation: First pre-check, then separate mode -/
def runPreCheckPlusSeparateCheckImpl : PropEvalM PreCheckPlusSeparateResult := do
  IO.println "============================================================"
  IO.println "[PRECHECK+SEPARATE MODE] Running pre-check for the test expression ..."

  -- Run pre-check to validate test expression
  match ← runTestValidityPreCheck with
  | some reason => do
    IO.println s!"[PRECHECK+SEPARATE MODE] Pre-check failed: {reason} - skipping equivalence checking"
    -- Return a result indicating that the test is not equivalent to ground, with precheck failed
    return PreCheckPlusSeparateResult.mk
      reason  -- preCheck field: store the error reason
      none  -- No separate result needed
  | none => do
    IO.println "[PRECHECK+SEPARATE MODE] Pre-check passed. Running separate mode ..."
    let separateResult ← runSeparateCheckImpl .bothDirections
    IO.println s!"[PRECHECK+SEPARATE MODE] Separate check completed."
    return PreCheckPlusSeparateResult.mk
      "passed"  -- preCheck field: indicate success
      (some separateResult)


/-- Pre-Check+Separate mode: First run pre-check, then separate mode (no binary check) -/
def runPreCheckPlusSeparateCheck (_ : EvalConfig) (ctx : EvalCtx) (old : E3Result) : MetaM E3Result := do
  let ⟨result, _⟩ ← runPreCheckPlusSeparateCheckImpl |>.run ctx
  return E3Result.addPreCheckPlusSeparateResult old result


/-- Naive mode implementation: Check satisfiability of test and ground statements (both assertion and negation) -/
def runNaiveCheckImpl : PropEvalM NaiveResult := do
  IO.println "============================================================"
  IO.println "[NAIVE MODE] Running pre-check for the test expression ..."

  -- Run pre-check to validate test expression
  match ← runTestValidityPreCheck with
  | some reason => do
    IO.println s!"[NAIVE MODE] Pre-check failed: {reason} - skipping equivalence checking"
    -- Return a result indicating that the test is not equivalent to ground, with precheck failed
    return {
      testSat := s!"pre-check_failed: {reason}",
      testNegSat := s!"pre-check_failed: {reason}",
      groundSat := s!"pre-check_failed: {reason}",
      groundNegSat := s!"pre-check_failed: {reason}"
    }
  | none => do
    IO.println "[NAIVE MODE] Pre-check passed. Running naive checks ..."

    let test ← translateTestExpr
    let testNeg : EAssertion := .neg <| test
    let ground ← translateGroundExpr
    let groundNeg : EAssertion := .neg <| ground

    /- Check satisfiability of both Assertion and Negation of `Test` -/
    IO.println "============================================================"
    IO.println "[NAIVE MODE] Checking Test (Assertion) ..."
    let testResult ← evalSmt' true none 5 test []
    IO.println "------------------------------------------------------------"
    IO.println "[NAIVE MODE] Checking Test (Negation) ..."
    let testNegResult ← evalSmt' true none (←getEvalConfig).equivSolverTime testNeg []

    /- Check satisfiability of both Assertion and Negation of `Ground` -/
    IO.println "============================================================"
    IO.println "[NAIVE MODE] Checking Ground (Assertion) ..."
    let groundResult ← evalSmt' true none 5 ground []
    IO.println "------------------------------------------------------------"
    IO.println "[NAIVE MODE] Checking Ground (Negation) ..."
    let groundNegResult ← evalSmt' true none (←getEvalConfig).equivSolverTime groundNeg []
    IO.println "============================================================"

    let naiveResult : NaiveResult := {
      testSat := testResult,
      testNegSat := testNegResult,
      groundSat := groundResult,
      groundNegSat := groundNegResult
    }

    if (← getEvalConfig).writeResult = false then
      IO.println s!"[E3] Naive check result: {naiveResult}"

    return naiveResult


/-- Naive mode: Check satisfiability of test and ground statements (both assertion and negation) -/
def runNaiveCheck (_ : EvalConfig) (ctx : EvalCtx) (old : E3Result) : MetaM E3Result := do
  let ⟨naiveResult, _⟩ ← runNaiveCheckImpl.run ctx
  return old.addNaiveResult naiveResult


/-- Pre-check mode: Only run pre-check validation of Test expression -/
def runPreCheck (_ : EvalConfig) (ctx : EvalCtx) (old : E3Result) : MetaM E3Result := do
  let ⟨precheckOption, _⟩ ← runTestValidityPreCheck.run ctx
  let result := match precheckOption with
  | some reason => PreCheckResult.mk reason
  | none => PreCheckResult.mk "passed"
  return old.addPreCheckResult result
