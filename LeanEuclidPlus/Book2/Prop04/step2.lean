import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.2: BD joined. line_from_points b d in Main puts b, d on BD; b ≠ d because the square
   corner d makes a right angle ∠b:a:d = ∟ at a (so d ≠ b, else the angle would be degenerate). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step2 (a b d : Point) (AB AD BD : Line)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (hbad : ∠ b:a:d = ∟) :
    distinctPointsOnLine b d BD := by
  euclid_finish

end Elements.Book2
