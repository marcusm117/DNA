import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step1_cNotIn (c f : Point) (ABC ADE : Circle)
    (hc_ABC : c.onCircle ABC)
    (hf_in : f.insideCircle ABC)
    (left_4 : ¬ABC.intersectsCircle ADE)
    (hfNotIn : ¬f.insideCircle ADE)
    (hfNotOn : ¬f.onCircle ADE)
    : ¬c.insideCircle ADE :=
  fun hc_in => left_4 (intersection_circle_circle_1 c f ABC ADE
    ⟨fun h => h.2 hc_ABC, fun h => h.1 hf_in, hc_in, ⟨hfNotIn, hfNotOn⟩⟩)

end Elements.Book3
