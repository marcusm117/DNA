import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.20: "Thus, it is a square." CGKB is both equilateral (step19) and right-angled (step18), i.e.
   a square. -/
theorem helper_2_4_step20 (b c g k : Point)
    (hstep19 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|)
    (hstep18 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) :
    (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
      ((∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by
  exact ⟨hstep19, hstep18⟩

end Elements.Book2
