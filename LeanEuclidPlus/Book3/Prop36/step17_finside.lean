import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_finside (a e f : Point) (ABC : Circle) (DA : Line)
    (ha_circ : a.onCircle ABC) (he_centre : e.isCentre ABC)
    (ha_DA : a.onLine DA) (hf_DA : f.onLine DA) (hne_DA : ¬ e.onLine DA)
    (h1 : ∠ a:f:e = ∟) (haf : a ≠ f) (hef : e ≠ f) :
    f.insideCircle ABC := by
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points f e) as FE
  euclid_apply (proposition_47 f a e AF AE FE)
  euclid_apply (point_in_circle_if e a f ABC)
  euclid_finish

end Elements.Book3
