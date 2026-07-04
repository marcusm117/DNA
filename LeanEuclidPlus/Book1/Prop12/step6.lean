import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step6 (g h e c : Point)
    (hassump1 : |(g─h)| = |(h─e)|)
    (hassump2 : |(h─c)| = |(h─c)|) :
    |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)| := by
  euclid_finish

end Elements.Book1
