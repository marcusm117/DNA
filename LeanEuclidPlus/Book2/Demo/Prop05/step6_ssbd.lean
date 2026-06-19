import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: b and d (both on AB) are on the same side of KM. [AFTER: library call.] witness h on KM
   off AB, AB ∦ KM ⟹ sameSide_of_parallel. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_ssbd (b d h : Point) (AB KM : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    b.sameSide d KM :=
  sameSide_of_parallel b d h AB KM hbAB hdAB hhKM hhoffAB hKMAB

end Elements.Book2
