import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_hEFG_int_ABC (ABC : Circle) (EFG : Line) (e : Point)
    (he_inside_ABC : e.insideCircle ABC) (heEFG : e.onLine EFG)
    : EFG.intersectsCircle ABC := by
  exact intersection_circle_line_2 e ABC EFG ⟨he_inside_ABC, heEFG⟩

end Elements.Book3
