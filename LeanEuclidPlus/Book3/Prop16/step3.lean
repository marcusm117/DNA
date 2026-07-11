import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop16.step3_htri
import Book3.Prop16.step3_isoceles
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

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
    (right_6 : a ≠ e)
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
  have step3_htri : formTriangle d a c DA AE DC := by euclid_apply (helper_3_16_step3_htri d a c e b DA AE DC (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show c.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)))
  have step3_isoceles : ∠ d:a:c = ∠ d:c:a := by euclid_apply (helper_3_16_step3_isoceles d a c DA AE DC (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─c)|; assumption)) (by euclid_assumption "" (show formTriangle d a c DA AE DC; assumption)))
  have hsymm : ∠ d:c:a = ∠ a:c:d := angle_symm d c a ⟨hdc, hcne⟩
  linarith

end Elements.Book3
