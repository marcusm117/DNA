import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_step3
    (d a c b e : Point) (ABC : Circle) (AE DC : Line)
    (left : d.isCentre ABC)
    (left_1 : a.onCircle ABC)
    (hcABC : c.onCircle ABC)
    (hcne : c ≠ a)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (hcAE : c.onLine AE)
    (hDCd : d.onLine DC)
    (hDCc : c.onLine DC)
    (step2 : distinctPointsOnLine d c DC)
    (hassump1 : |(d─a)| = |(d─c)|)
    : ∠ d:a:c = ∠ a:c:d := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_not_on : ¬d.onCircle ABC := inside_not_on_circle d ABC hd_inside
  have hda : d ≠ a := fun h => hd_not_on (h ▸ left_1)
  have hdc : d ≠ c := fun h => hd_not_on (h ▸ hcABC)
  obtain ⟨DA, hDAd, hDAa⟩ := line_from_points d a hda
  have hstep : ∠ d:a:c = ∠ d:c:a := by
    euclid_finish
  have hsymm : ∠ d:c:a = ∠ a:c:d := by
    euclid_apply (angle_symm d c a)
    euclid_finish
  linarith

end Elements.Book3
