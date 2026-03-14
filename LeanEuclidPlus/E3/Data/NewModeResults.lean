-- New result structures for naive and separate modes
import E3.Data.EquivResult

structure NaiveResult where
  testSat : String
  testNegSat : String
  groundSat : String
  groundNegSat : String

namespace NaiveResult

def toJson (result : NaiveResult) : String :=
  let test_group := "\"assertion\" : \"" ++ result.testSat ++ "\", \"negation\" : \"" ++ result.testNegSat ++ "\""
  let ground_group := "\"assertion\" : \"" ++ result.groundSat ++ "\", \"negation\" : \"" ++ result.groundNegSat ++ "\""
  "{\"test\" : {" ++ test_group ++ "}, \"ground\" : {" ++ ground_group ++ "}}"

instance : ToString NaiveResult where
  toString := toJson

end NaiveResult

structure SeparateResult where
  -- Detailed SMT results for premises implications
  premisesTestImpGroundAssertion : String
  premisesTestImpGroundNegation : String
  premisesGroundImpTestAssertion : String
  premisesGroundImpTestNegation : String
  -- Detailed SMT results for conclusions implications
  conclusionsTestImpGroundAssertion : String
  conclusionsTestImpGroundNegation : String
  conclusionsGroundImpTestAssertion : String
  conclusionsGroundImpTestNegation : String

namespace SeparateResult

def premisesTestImpGround (result : SeparateResult) : Bool :=
  result.premisesTestImpGroundNegation == "UNSAT"

def premisesGroundImpTest (result : SeparateResult) : Bool :=
  result.premisesGroundImpTestNegation == "UNSAT"

def conclusionsTestImpGround (result : SeparateResult) : Bool :=
  result.conclusionsTestImpGroundNegation == "UNSAT"

def conclusionsGroundImpTest (result : SeparateResult) : Bool :=
  result.conclusionsGroundImpTestNegation == "UNSAT"

def premisesEquiv (result : SeparateResult) : Bool :=
  result.premisesTestImpGround && result.premisesGroundImpTest

def conclusionsEquiv (result : SeparateResult) : Bool :=
  result.conclusionsTestImpGround && result.conclusionsGroundImpTest

def toJson (result : SeparateResult) : String :=
  let premises_test_imp_ground := "\"assertion\" : \"" ++ result.premisesTestImpGroundAssertion ++ "\", \"negation\" : \"" ++ result.premisesTestImpGroundNegation ++ "\""
  let premises_ground_imp_test := "\"assertion\" : \"" ++ result.premisesGroundImpTestAssertion ++ "\", \"negation\" : \"" ++ result.premisesGroundImpTestNegation ++ "\""
  let conclusions_test_imp_ground := "\"assertion\" : \"" ++ result.conclusionsTestImpGroundAssertion ++ "\", \"negation\" : \"" ++ result.conclusionsTestImpGroundNegation ++ "\""
  let conclusions_ground_imp_test := "\"assertion\" : \"" ++ result.conclusionsGroundImpTestAssertion ++ "\", \"negation\" : \"" ++ result.conclusionsGroundImpTestNegation ++ "\""

  let premises_group := "\"test_implies_ground\" : {" ++ premises_test_imp_ground ++ "}, \"ground_implies_test\" : {" ++ premises_ground_imp_test ++ "}"
  let conclusions_group := "\"test_implies_ground\" : {" ++ conclusions_test_imp_ground ++ "}, \"ground_implies_test\" : {" ++ conclusions_ground_imp_test ++ "}"
  "{\"premises\" : {" ++ premises_group ++ "}, \"conclusions\" : {" ++ conclusions_group ++ "}}"

instance : ToString SeparateResult where
  toString := toJson

end SeparateResult

structure PreCheckPlusSeparateResult where
  -- Pre-check result message
  preCheck : String
  -- Separate check results
  separateCheck : Option SeparateResult := none

namespace PreCheckPlusSeparateResult

def toJson (result : PreCheckPlusSeparateResult) : String :=
  let precheck_str := "\"" ++ result.preCheck ++ "\""
  let separate_str := match result.separateCheck with | none => "\"none\"" | some r => r.toJson

  let precheck_group := "\"precheck\" : " ++ precheck_str
  let separate_group := "\"separate_check\" : " ++ separate_str

  "{" ++ precheck_group ++ ", " ++ separate_group ++ "}"

instance : ToString PreCheckPlusSeparateResult where
  toString := toJson

end PreCheckPlusSeparateResult

structure PreCheckResult where
  -- Pre-check result message - "passed" if successful, or specific error reason if failed
  result : String

namespace PreCheckResult

def toJson (result : PreCheckResult) : String :=
  "\"" ++ result.result ++ "\""

instance : ToString PreCheckResult where
  toString := toJson

end PreCheckResult
