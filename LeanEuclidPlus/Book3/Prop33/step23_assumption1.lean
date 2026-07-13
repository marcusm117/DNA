import SystemE
import Book1.Prop05.Main
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Angle in a semicircle is a right angle ([Prop.~3.31], SUPPRESSED in Main — III.31's horn-angle
-- addendum is not formalizable in System E). The clean core is re-derived from the isosceles triangles
-- FAE, FBE (|(f─a)| = |(f─e)| = |(f─b)| radii, I.5) plus the triangle-angle-sum I.32, exactly as in
-- Book3/Prop32/step6.
theorem helper_3_33_step23_assumption1
    (a b e f : Point) (α : Circle) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hfcen : f.isCentre α) (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hafb : between a f b) (he_off : ¬ e.onLine AB) :
    ∠ a:e:b = ∟ := by
  have hea : e ≠ a := by euclid_finish
  have heb : e ≠ b := by euclid_finish
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b e) as EB
  euclid_apply (line_from_points f e) as FE
  euclid_apply (extend_point AB f a) as d1
  euclid_apply (extend_point FE f e) as e1
  euclid_apply (extend_point AB f b) as g1
  euclid_apply (extend_point AB a b) as k
  euclid_apply (Elements.Book1.proposition_5 f a e d1 e1 AB AE FE)
  euclid_apply (Elements.Book1.proposition_5 f b e g1 e1 AB EB FE)
  euclid_apply (Elements.Book1.proposition_32 e a b k AE AB EB)
  euclid_finish

end Elements.Book3
