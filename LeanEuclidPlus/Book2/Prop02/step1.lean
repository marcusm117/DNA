import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- 2.2.1: the square ADEB on AB [Prop.~1.46]. The square's defining length/angle facts are
   produced by the proposition_46 construction in Main; this helper just repackages them. -/
theorem helper_2_2_step1 (a b d e : Point)
    (had : |(a─d)| = |(a─b)|) (hbe : |(b─e)| = |(a─b)|) (hde : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hade : ∠ a:d:e = ∟) (habe : ∠ a:b:e = ∟) (hbed : ∠ b:e:d = ∟) :
    |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  exact ⟨had, hbe, hde, hbad, hade, habe, hbed⟩

end Elements.Book2
