import SystemE
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.10: CG ∥ BK cut by transversal CB ⟹ co-interior ∠KBC + ∠GCB = two right-angles [1.29].
-- BK lies on BE, CG on CF; CF ∥ BE (from CF ∥ AD and AD ∥ BE, [1.30]). Transversal is line AB
-- (through b,c). proposition_29''''' k g b c BE CF AB : ∠KBC + ∠BCG = ∟ + ∟.
set_option systemE.solverTime 30 in
theorem helper_2_step10 (a b c d e g k : Point) (AB DE AD BE CF : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hkb : distinctPointsOnLine k b BE) (hgc : distinctPointsOnLine g c CF)
    (hbc : distinctPointsOnLine b c AB) (hcab : c.onLine AB) (hacb : between a c b)
    (hk_side : k.sameSide g AB)
    (hCFAD : ¬(CF.intersectsLine AD)) (hADCF : AD ≠ CF) :
    ∠ k:b:c + ∠ g:c:b = ∟ + ∟ := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_29''''' k g b c BE CF AB)
  euclid_finish

end Elements.Book2
