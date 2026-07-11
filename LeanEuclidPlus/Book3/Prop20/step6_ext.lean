import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step6_ext
  (a c e f : Point) (AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_c_circ : c.onCircle ABC)
  (h_f_circ : f.onCircle ABC)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_cne_a : c ≠ a) (h_bet : between f e a)
  : ∠ f:e:c = ∠ e:a:c + ∠ e:c:a := by
  by_cases hc : c.onLine AEF
  · -- @euclid_gap: c on line AE ⟹ AC is a diameter, so C,E,F collinear; degenerate.
    euclid_finish
  · euclid_apply (line_from_points c a) as CA
    euclid_apply (line_from_points c e) as CE
    have htri : formTriangle c a e CA AEF CE := by euclid_finish
    euclid_apply (Elements.Book1.proposition_32 c a e f CA AEF CE)
    euclid_finish

end Elements.Book3
