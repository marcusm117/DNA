import SystemE
import Book1.Prop12.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_16_step14
    (a g d : Point) (ABC : Circle) (FA : Line)
    (left : d.isCentre ABC)
    (hFAon : a.onLine FA)
    (hgFA : g.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (hagne : a ≠ g)
    (hgperp : ∠ a:g:d = ∟)
    : g.onLine FA ∧ ∠ a:g:d = ∟ := by
  have hd_off : ¬d.onLine FA := fun hd_on =>
    hFAnot (intersection_circle_line_2 d ABC FA ⟨center_inside_circle d ABC left, hd_on⟩)
  have hpts : distinctPointsOnLine a g FA := ⟨hFAon, hgFA, hagne⟩
  euclid_apply (Elements.Book1.proposition_12 a g d FA)
  exact ⟨hgFA, hgperp⟩

end Elements.Book3
