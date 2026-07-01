import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by
  sorry

end Elements.Book1
