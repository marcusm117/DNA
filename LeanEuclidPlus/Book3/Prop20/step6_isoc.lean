import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step6_isoc
  (a c e : Point) (AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_c_circ : c.onCircle ABC)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_cne_a : c ≠ a)
  : ∠ e:a:c = ∠ e:c:a := by
  by_cases hc : c.onLine AEF
  · -- @euclid_gap: c on line AE ⟹ AC is a diameter, triangle EAC degenerates.
    euclid_finish
  · euclid_apply (line_from_points a c) as AC
    euclid_apply (line_from_points e c) as EC
    have hrad : |(e─a)| = |(e─c)| := by euclid_finish
    have htri : formTriangle e a c AEF AC EC := by euclid_finish
    euclid_apply (extend_point AEF e a) as d1
    euclid_apply (extend_point EC e c) as d2
    euclid_apply (Elements.Book1.proposition_5 e a c d1 d2 AEF AC EC)
    euclid_finish

end Elements.Book3
