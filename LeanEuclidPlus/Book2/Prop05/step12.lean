import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12: AH = |(a─d)| * |(d─b)|. The parallelogram AH (area △adh + △ahk) equals
   the rectangle with sides AD and DB. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12 (a b d h k : Point) (AB DG AK KM : Line)
    (haAB : a.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hstep13 : |(d─h)| = |(d─b)|) :
    Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)| := by
  euclid_finish

end Elements.Book2