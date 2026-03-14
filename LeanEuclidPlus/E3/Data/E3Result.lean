import E3.Data.BoundVars
import E3.Data.EquivResult
import E3.Data.ApproxResult
import E3.Data.NewModeResults
import E3.Util.String

structure E3Result where
  bvarDelta : BvarDelta
  equiv : Option EquivResult := none
  approx : Option ApproxResult := none
  naive : Option NaiveResult := none
  separate : Option SeparateResult := none
  preCheckPlusSeparate : Option PreCheckPlusSeparateResult := none
  precheck : Option PreCheckResult := none
  test : String := ""
  testNeg : String := ""
  ground : String := ""
  groundNeg : String := ""
  testToGround : String := ""
  testToGroundNeg : String := ""
  groundToTest : String := ""
  groundToTestNeg : String := ""

namespace E3Result

def equivSuccess (result : E3Result) : Bool :=
  match result.equiv with
  | some r => r.isEquiv
  | none => false

def addEquivResult : E3Result → EquivResult → E3Result :=
  λ x r => {x with equiv := r}

def addApproxResult : E3Result → ApproxResult → E3Result :=
  λ x r => {x with approx := r}

def addNaiveResult : E3Result → NaiveResult → E3Result :=
  λ x r => {x with naive := r}

def addSeparateResult : E3Result → SeparateResult → E3Result :=
  λ x r => {x with separate := r}

def addPreCheckPlusSeparateResult : E3Result → PreCheckPlusSeparateResult → E3Result :=
  λ x r => {x with preCheckPlusSeparate := r}

def addPreCheckResult : E3Result → PreCheckResult → E3Result :=
  λ x r => {x with precheck := r}

def addTestString : E3Result → String → E3Result :=
  λ x s => {x with test := s}

def addTestNegString : E3Result → String → E3Result :=
  λ x s => {x with testNeg := s}

def addGroundString : E3Result → String → E3Result :=
  λ x s => {x with ground := s}

def addGroundNegString : E3Result → String → E3Result :=
  λ x s => {x with groundNeg := s}

def addTestToGroundString : E3Result → String → E3Result :=
  λ x s => {x with testToGround := s}

def addTestToGroundNegString : E3Result → String → E3Result :=
  λ x s => {x with testToGroundNeg := s}

def addGroundToTestString : E3Result → String → E3Result :=
  λ x s => {x with groundToTest := s}

def addGroundToTestNegString : E3Result → String → E3Result :=
  λ x s => {x with groundToTestNeg := s}

def toJson (name : String) : E3Result → String
| result =>
  let bin_str := match result.equiv with | none => "\"none\"" | some r => r.toJson
  let approx_str := match result.approx with | none => "\"none\"" | some r => r.toJson
  let naive_str := match result.naive with | none => "\"none\"" | some r => r.toJson
  let separate_str := match result.separate with | none => "\"none\"" | some r => r.toJson

  let preCheckPlusSeparate_str := match result.preCheckPlusSeparate with | none => "\"none\"" | some r => r.toJson
  let precheck_str := match result.precheck with | none => "\"none\"" | some r => r.toJson

  -- Group with more descriptive names
  let ground_group := wrapObject s!"\"assertion\" : \"{result.ground}\", \"negation\" : \"{result.groundNeg}\""
  let test_group := wrapObject s!"\"assertion\" : \"{result.test}\", \"negation\" : \"{result.testNeg}\""
  let test_to_ground_group := wrapObject s!"\"assertion\" : \"{result.testToGround}\", \"negation\" : \"{result.testToGroundNeg}\""
  let ground_to_test_group := wrapObject s!"\"assertion\" : \"{result.groundToTest}\", \"negation\" : \"{result.groundToTestNeg}\""

  let contents := wrapObject s!"\"bvars\" : {result.bvarDelta.toJson}, \n \"binary_check\" : {bin_str}, \n \"approx_check\" : {approx_str}, \n \"naive_check\" : {naive_str}, \n \"separate_check\" : {separate_str}, \n \"precheck_plus_separate_check\" : {preCheckPlusSeparate_str}, \n \"precheck\" : {precheck_str}, \n\"ground\" : {ground_group}, \n\"test\" : {test_group}, \n\"test_implies_ground\" : {test_to_ground_group}, \n\"ground_implies_test\" : {ground_to_test_group}"

  wrapObject s!"\"{name}\" : \n {contents}"



instance : ToString E3Result := ⟨toJson "E3-result"⟩


end E3Result
