import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b and e are on the same side of the tangent line AD: both lie on the circle α, which AD does not
-- cross, so the whole circle is on one side of AD. (e is off AD since e ∈ AE ≠ AD meet only at a≠e;
-- b is off AD since otherwise the chord-interior point f would make AD a secant.)
theorem helper_3_33_step14_edab_bdAE_beAD
    (a b e f : Point) (AD AE : Line) (α : Circle)
    (haad : a.onLine AD) (habne : a ≠ b) (heane : e ≠ a)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hADAEne : AD ≠ AE)
    (hafb : between a f b)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hADtangent : ¬ AD.intersectsCircle α) :
    b.sameSide e AD := by
  have hbin : ¬ b.outsideCircle α := by euclid_finish
  have hein : ¬ e.outsideCircle α := by euclid_finish
  have hboff : ¬ b.onLine AD := by
    intro hbAD
    euclid_apply (circle_points_between a b f α)
    euclid_apply (intersection_circle_line_2 f α AD)
    euclid_finish
  have heoff : ¬ e.onLine AD := by
    intro heAD
    euclid_apply (two_points_determine_line a e AD AE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_circle_line_1 b e α AD)
  euclid_finish

end Elements.Book3
