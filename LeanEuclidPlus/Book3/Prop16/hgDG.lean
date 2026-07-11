import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_hgDG
    (a d : Point) (ABC : Circle) (FA AE : Line) (e b : Point)
    (left : d.isCentre ABC)
    (hFAon : a.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (hFAne : FA ≠ AE)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (right_6 : a ≠ e)
    : ∃ (g : Point) (DG_line : Line),
        g.onLine FA ∧ ∠ a:g:d = ∟ ∧ d.onLine DG_line ∧ g.onLine DG_line := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_off : ¬d.onLine FA := fun hd_on =>
    hFAnot (intersection_circle_line_2 d ABC FA ⟨hd_inside, hd_on⟩)
  obtain ⟨a', ha'ne, ha'FA⟩ := exists_distincts_points_on_line FA a
  have hgDG_foot_exists : ∃ g : Point, g.onLine FA ∧ (∠ a:g:d = ∟ ∨ ∠ a':g:d = ∟) ∧
      (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟) := by sorry
  have hgDG_foot : ∃ g, g.onLine FA ∧ ∠ a:g:d = ∟ := by sorry
  obtain ⟨g, hgFA, hang⟩ := hgDG_foot
  have hdg : d ≠ g := fun h => hd_off (h ▸ hgFA)
  obtain ⟨DG_line, hDGd, hDGg⟩ := line_from_points d g hdg
  exact ⟨g, DG_line, hgFA, hang, hDGd, hDGg⟩

end Elements.Book3
