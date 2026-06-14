import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- 2.2.2: CF drawn through C parallel to AD or BE [Prop.~1.31]. Both facts (c on CF, CF ∥ AD)
   are produced by the proposition_31 construction in Main; this helper repackages them. -/
theorem helper_2_2_step2 (c : Point) (CF AD : Line)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD)) :
    c.onLine CF ∧ ¬(CF.intersectsLine AD) := by
  exact ⟨hcCF, hCFAD⟩

end Elements.Book2
