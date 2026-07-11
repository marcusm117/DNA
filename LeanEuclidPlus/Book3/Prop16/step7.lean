import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step7
    (d a c : Point) (ABC : Circle) (DC : Line)
    (left : d.isCentre ABC)
    (left_1 : a.onCircle ABC)
    (hcABC : c.onCircle ABC)
    (hcne : c ≠ a)
    (hDCd : d.onLine DC)
    (hDCc : c.onLine DC)
    (step6 : ∠ d:a:c + ∠ a:c:d = ∟ + ∟)
    : False := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_not_on : ¬d.onCircle ABC := inside_not_on_circle d ABC hd_inside
  have hda : d ≠ a := fun h => hd_not_on (h ▸ left_1)
  have hdc : d ≠ c := fun h => hd_not_on (h ▸ hcABC)
  have hac : a ≠ c := hcne.symm
  obtain ⟨DA, hDAd, hDAa⟩ := line_from_points d a hda
  obtain ⟨AC, hACa, hACc⟩ := line_from_points a c hac
  have htri : formTriangle d a c DA AC DC := by euclid_finish
  have h17 : ∠ d:a:c + ∠ a:c:d < ∟ + ∟ := by
    euclid_apply (Elements.Book1.proposition_17 d a c DA AC DC htri)
  linarith

end Elements.Book3
