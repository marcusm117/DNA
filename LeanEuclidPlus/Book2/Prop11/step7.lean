import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step7
    (k : Point) (GH CD : Line)
    (hkGH : k.onLine GH) (hkCD : k.onLine CD) :
    k.onLine GH := by
  exact hkGH

end Elements.Book2
