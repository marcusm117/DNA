structure EquivResult where
  groundImpTest : Bool
  testImpGround : Bool
  precheckFailed : Bool := false

namespace EquivResult

def isEquiv : EquivResult → Bool
| ⟨true, true, false⟩ => true
| _ => false

def toString : EquivResult → String
| ⟨_, _, true⟩ => "propositions are not equivalent (pre-check failed)"
| ⟨true, true, false⟩ => "propositions are equivalent"
| ⟨true, false, false⟩ => "prediction is strictly weaker than ground truth"
| ⟨false, true, false⟩ => "prediction is strictly stronger than ground truth"
| ⟨false, false, false⟩ => "no conclusion made between prediction and ground truth"

def toJson : EquivResult → String
| ⟨_, _, true⟩ => "\"not_equiv\""
| ⟨true, true, false⟩ => "\"equiv\""
| ⟨true, false, false⟩ => "\"ground_imp_test\""
| ⟨false, true, false⟩ => "\"test_imp_ground\""
| ⟨false, false, false⟩ => "\"no_conclusion\""

instance : ToString EquivResult := ⟨EquivResult.toString ⟩

end EquivResult
