import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.18: CGKB is right-angled — all four angles are right. Assembled from ∠ k:b:c = ∟ (step15),
   ∠ b:c:g = ∟ (step16), and ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ (step17). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step18 (b c g k : Point)
    (hstep15 : ∠ k:b:c = ∟) (hstep16 : ∠ b:c:g = ∟)
    (hstep17 : ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟) :
    (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟) := by
  exact ⟨hstep15, hstep16, hstep17.1, hstep17.2⟩

end Elements.Book2
