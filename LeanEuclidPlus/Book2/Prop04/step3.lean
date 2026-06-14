import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.3: CF drawn through C parallel to AD/EB [Prop.~1.31]. The line CF through c, parallel to
   AD, is produced by the proposition_31 construction in Main; this helper repackages its facts. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step3 (c : Point) (CF AD : Line)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD)) :
    c.onLine CF ∧ ¬(CF.intersectsLine AD) := by
  exact ⟨hcCF, hCFAD⟩

end Elements.Book2
