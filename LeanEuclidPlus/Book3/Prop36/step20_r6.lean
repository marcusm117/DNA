import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20_r6 (a c d f : Point) (DA : Line)
    (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hd_DA : d.onLine DA)
    (hbet : between a f c) (hlen : |(a─f)| = |(f─c)|)
    (hbetdca : between d c a) (hac : a ≠ c) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
