import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.12 sub: ∠ a:k:h = ∟ (the corner of rectangle ADHK at K). Given ∠ k:a:c = ∟ (step8_kal_right,
   the corner of rectangle AL at the same vertical AK), AB ∥ KM are cut by the transversal AK at feet
   a (on AB) and k (on KM); the co-interior angles ∠ c:a:k and ∠ a:k:h sum to two right angles
   (proposition_29'''''), with c on AB and h on KM on the same side of AK. Since ∠ c:a:k = ∠ k:a:c = ∟,
   we get ∠ a:k:h = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12_akh_right (a c h k : Point) (AB AK KM : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM)
    (hac : a ≠ c) (hak : a ≠ k) (hkh : k ≠ h)
    (hkac : ∠ k:a:c = ∟)
    (hhcAK : c.sameSide h AK)
    (hKMAB : ¬(AB.intersectsLine KM)) :
    ∠ a:k:h = ∟ := by
  euclid_intros
  euclid_apply (proposition_29''''' c h a k AB KM AK)
  euclid_finish

end Elements.Book2
