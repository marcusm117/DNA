import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_step18
    (d g h : Point) (ABC : Circle) (FA : Line)
    (left : d.isCentre ABC)
    (hhcircle : h.onCircle ABC)
    (hgFA : g.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (step17 : |(d─h)| > |(d─g)|)
    : False := by
  have g_inside : g.insideCircle ABC :=
    point_in_circle_if d h g ABC ⟨left, hhcircle, step17⟩
  exact hFAnot (intersection_circle_line_2 g ABC FA ⟨g_inside, hgFA⟩)

end Elements.Book3
