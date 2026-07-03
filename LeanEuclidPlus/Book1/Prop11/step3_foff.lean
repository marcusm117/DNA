import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_11_step3_foff
    (a b c d e f : Point) (AB : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|) :
    ¬(f.onLine AB) := by
  euclid_finish

end Elements.Book1
