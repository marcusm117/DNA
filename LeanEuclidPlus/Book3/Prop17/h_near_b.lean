import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_h_near_b (e f : Point) (BCD : Circle) (EF : Line)
    (hcen_BCD : e.isCentre BCD)
    (he_onEF : e.onLine EF)
    (hf_onEF : f.onLine EF)
    (hf_out : f.outsideCircle BCD) :
    ∃ b : Point, b.onCircle BCD ∧ b.onLine EF ∧ between e b f := by
  have he_in : e.insideCircle BCD := center_inside_circle e BCD hcen_BCD
  exact intersection_circle_line_between_points BCD EF e f ⟨he_in, he_onEF, hf_out, hf_onEF⟩

end Elements.Book3
