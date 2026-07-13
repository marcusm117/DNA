import SystemE
import Book2.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step5 (a c d f : Point) (ABC : Circle) (DA : Line)
    (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
    (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
    (hf_centre : f.isCentre ABC) (hbet : between d c a)
    (hhalf : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
