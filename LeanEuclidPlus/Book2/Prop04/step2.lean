import SystemE
import Book.Prop29

namespace Elements.Book2

open Elements.Book1

-- 2.4.2: CF ∥ AD, transversal BD ⟹ external ∠CGB = internal opposite ∠ADB  [Prop.~1.29].
-- Corresponding angles: proposition_29'''' with parallels CF, AD and transversal BD (b,g,d
-- collinear, g between b and d), c and a on the same side of BD.
set_option systemE.solverTime 30 in
theorem helper_2_step2 (a b c d g : Point) (AD CF BD : Line)
    (hgc : distinctPointsOnLine g c CF) (hda : distinctPointsOnLine d a AD)
    (hbd : distinctPointsOnLine b d BD)
    (hbgd : between b g d) (hca : c.sameSide a BD)
    (hpar : ¬(CF.intersectsLine AD)) :
    ∠ c:g:b = ∠ a:d:b := by
  euclid_intros
  euclid_apply (proposition_29'''' c a b g d CF AD BD)
  euclid_finish

end Elements.Book2
