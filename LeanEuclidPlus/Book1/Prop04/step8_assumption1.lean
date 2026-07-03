import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step8_assumption1
  (a b c d e f : Point) (b' c' : Point)
  (ptImg : Point → Point)
  (h_ptImg_a : ptImg a = d)
  (step1 : ptImg b = e)
  (step3 : ptImg c = f)
  : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f :=
  ⟨h_ptImg_a, step1, step3⟩

end Elements.Book1
