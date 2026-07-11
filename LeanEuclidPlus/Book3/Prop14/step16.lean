import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_14_step16
    (e f g : Point)
    (hgiven : |(e─f)| = |(e─g)|) :
    |(e─f)| = |(e─g)| := hgiven

end Elements.Book3
