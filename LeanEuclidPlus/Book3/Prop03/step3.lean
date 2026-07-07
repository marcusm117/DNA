import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step3
    (a b e : Point) (ABC : Circle)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (he : e.isCentre ABC)
    : |(e─a)| = |(e─b)| := by
  euclid_apply (point_on_circle_onlyif e b a ABC)
  euclid_finish

end Elements.Book3
