import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_18_hfoff (f : Point) (ABC : Circle) (DE : Line)
    (h_no_int : ¬DE.intersectsCircle ABC) (h_centre : f.isCentre ABC) :
    ¬f.onLine DE := by
  intro hfon
  have hfinside : f.insideCircle ABC := center_inside_circle f ABC h_centre
  exact h_no_int (intersection_circle_line_2 f ABC DE ⟨hfinside, hfon⟩)

end Elements.Book3
