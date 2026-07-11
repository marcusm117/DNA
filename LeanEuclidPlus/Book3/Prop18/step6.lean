import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step6 (f b g : Point) (ABC : Circle) (DE : Line)
    (h_centre : f.isCentre ABC) (h_bon : b.onCircle ABC)
    (h_gon_DE : g.onLine DE) (h_no_int : ¬DE.intersectsCircle ABC)
    (step5 : |(f─b)| > |(f─g)|) :
    False := by
  have hginside : g.insideCircle ABC :=
    point_in_circle_if f b g ABC ⟨h_centre, h_bon, step5⟩
  exact h_no_int (intersection_circle_line_2 g ABC DE ⟨hginside, h_gon_DE⟩)

end Elements.Book3
