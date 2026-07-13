import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- g (centre) and b (on the circle) are on the same side of the tangent line AD: AD does not cross α,
-- so the whole circle and its centre lie on one side. If b were on AD then the interior chord-point f
-- (between a and b) would be inside α and on AD, making AD a secant — contradicting the tangent.
theorem helper_3_33_step14_edab_gbAD
    (a b d f g : Point) (AD : Line) (α : Circle)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadne : a ≠ d) (habne : a ≠ b)
    (hafb : between a f b)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hbcirc : b.onCircle α)
    (hADtangent : ¬ AD.intersectsCircle α) :
    g.sameSide b AD := by
  have hgin : ¬ g.outsideCircle α := by euclid_finish
  have hbin : ¬ b.outsideCircle α := by euclid_finish
  have hboff : ¬ b.onLine AD := by
    intro hbAD
    euclid_apply (circle_points_between a b f α)
    euclid_apply (intersection_circle_line_2 f α AD)
    euclid_finish
  have hgoff : ¬ g.onLine AD := by
    intro hgAD
    euclid_apply (intersection_circle_line_2 g α AD)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_circle_line_1 g b α AD)
  euclid_finish

end Elements.Book3
