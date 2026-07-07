import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step9_inside (a b p : Point) (ABC : Circle)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC)
    (hbet : between a p b) :
    p.insideCircle ABC := by
  euclid_finish

end Elements.Book3
