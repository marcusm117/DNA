import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_hh
    (d : Point) (ABC : Circle) (DG_line : Line)
    (left : d.isCentre ABC)
    (hDGd : d.onLine DG_line)
    : ∃ h : Point, h.onCircle ABC ∧ h.onLine DG_line := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hDGint : DG_line.intersectsCircle ABC :=
    intersection_circle_line_2 d ABC DG_line ⟨hd_inside, hDGd⟩
  obtain ⟨h, _h2, hh_circ, hh_line, _h2_circ, _h2_line, _hne⟩ :=
    intersections_circle_line ABC DG_line hDGint
  exact ⟨h, hh_circ, hh_line⟩

end Elements.Book3
