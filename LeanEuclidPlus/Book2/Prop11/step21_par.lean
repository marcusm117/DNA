import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step21_par
    (d k b h : Point) (CD AB BD GH : Line)
    (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hbAB : b.onLine AB) (hhAB : h.onLine AB)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (hkGH : k.onLine GH) (hhGH : h.onLine GH)
    (hCDAB : ¬CD.intersectsLine AB)
    (hBDGH : ¬BD.intersectsLine GH)
    (hBDneGH : BD ≠ GH) (hkh : k ≠ h) :
    formParallelogram d k b h CD AB BD GH := by
  euclid_intros
  -- d, b on BD ∥ GH ⟹ d, b on the same side of GH.
  have hss : d.sameSide b GH := sameSide_of_parallel_both d b BD GH hdBD hbBD hBDneGH hBDGH
  euclid_finish

end Elements.Book2
