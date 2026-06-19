import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

open Elements.Book1

/- Right angle from co-interior angles. Two parallels `L1 ∥ L2` cut by a transversal `T`
   at feet `g` (on L1) and `h` (on L2): the co-interior angles sum to two right angles
   (proposition_29'''''), so if ONE of them (`∠ g:h:d`) is right, the OTHER (`∠ b:g:h`)
   is right too. `b` is a point on L1, `d` a point on L2, both on the same side of T.
   This wraps the recurring rectangle-corner core; the caller supplies its own orientation
   prep (which angle is the known right angle — by supplement, ray-rewrite, etc.). -/
theorem right_angle_cointerior (b d g h : Point) (L1 L2 T : Line)
    (hgb : distinctPointsOnLine g b L1)
    (hhd : distinctPointsOnLine h d L2)
    (hgh : distinctPointsOnLine g h T)
    (hsame : b.sameSide d T)
    (hpar : ¬(L1.intersectsLine L2))
    (hknown : ∠ g:h:d = ∟) :
    ∠ b:g:h = ∟ := by
  euclid_apply (Elements.Book1.proposition_29''''' b d g h L1 L2 T)
  euclid_finish

end Elements
