import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_hbet (a c f : Point) (ABC : Circle) (DA : Line)
    (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
    (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
    (hfinside : f.insideCircle ABC) (hac : a ≠ c) :
    between a f c := by
  euclid_apply (circle_line_intersections f a c DA ABC)
  euclid_finish

end Elements.Book3
