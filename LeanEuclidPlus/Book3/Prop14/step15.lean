import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step15
    (e f g : Point)
    (hassump1 : |(e─f)| = |(e─g)|) :
    |(e─f)| = |(e─g)| := hassump1

end Elements.Book3
