import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step4
  (a b e f : Point) (AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_f_circ : f.onCircle ABC)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_bet : between f e a)
  : ∠ b:e:f = ∠ e:a:b + ∠ e:b:a := by
  by_cases hb : b.onLine AEF
  · -- @euclid_gap: b on line AE ⟹ b = f (antipode of a), so B,E,F collinear and the
    -- exterior-angle triangle degenerates. Euclid tacitly excludes the diameter case.
    euclid_finish
  · euclid_apply (line_from_points b a) as BA
    euclid_apply (line_from_points b e) as BE
    have htri : formTriangle b a e BA AEF BE := by euclid_finish
    euclid_apply (Elements.Book1.proposition_32 b a e f BA AEF BE)
    euclid_finish

end Elements.Book3
