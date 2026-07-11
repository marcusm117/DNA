import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠d:a:g < ∟: triangle d-a-g with ∠a:g:d=∟ → by I.17, ∠d:a:g + ∟ < 2∟ → ∠d:a:g < ∟.
theorem helper_3_16_step15_assumption2
    (a g d : Point) (ABC : Circle) (FA : Line)
    (left : d.isCentre ABC)
    (hFAon : a.onLine FA)
    (hgFA : g.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (hagne : a ≠ g)
    (hgperp : ∠ a:g:d = ∟)
    : ∠ d:a:g < ∟ := by
  have hd_off : ¬d.onLine FA := fun hd_on =>
    hFAnot (intersection_circle_line_2 d ABC FA ⟨center_inside_circle d ABC left, hd_on⟩)
  have hda : d ≠ a := fun h => hd_off (h ▸ hFAon)
  have hdg : d ≠ g := fun h => hd_off (h ▸ hgFA)
  obtain ⟨DA, hDAd, hDAa⟩ := line_from_points d a hda
  obtain ⟨AG, hAGa, hAGg⟩ := line_from_points a g hagne
  obtain ⟨DG, hDGd, hDGg⟩ := line_from_points d g hdg
  have htri : formTriangle d a g DA AG DG := by euclid_finish
  have h17 : ∠ d:a:g + ∠ a:g:d < ∟ + ∟ := Elements.Book1.proposition_17 d a g DA AG DG htri
  linarith

end Elements.Book3
