import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step3 (a b c d f g h : Point) (AC BD : Line)
  (hgAC : g.onLine AC) (hgang : ∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟)
  (hhBD : h.onLine BD) (hhang : ∠ b:h:f = ∟ ∨ ∠ d:h:f = ∟)
  : g.onLine AC ∧ (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ h.onLine BD ∧ (∠ b:h:f = ∟ ∨ ∠ d:h:f = ∟) := by
  exact ⟨hgAC, hgang, hhBD, hhang⟩

end Elements.Book3
