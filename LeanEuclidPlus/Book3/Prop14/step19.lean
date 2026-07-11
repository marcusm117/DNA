import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step19
    (a c e : Point)
    (hassump1 : |(a─e)| = |(e─c)|) :
    |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)| := by rw [hassump1]

end Elements.Book3
