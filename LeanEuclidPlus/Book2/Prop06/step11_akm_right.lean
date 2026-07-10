import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: ∠ a:k:m = ∟ (the corner of rectangle ADMK at K). Given ∠ k:a:c = ∟ (step11_kac_right,
   the corner at the same vertical AK), AB ∥ KM are cut by the transversal AK at feet a (on AB) and k
   (on KM); the co-interior angles ∠ c:a:k and ∠ a:k:m sum to two right angles (proposition_29'''''),
   with c on AB and m on KM on the same side of AK. Since ∠ c:a:k = ∠ k:a:c = ∟, ∠ a:k:m = ∟.
   (Mirror of Prop05 step12_akh_right.) -/
theorem helper_2_6_step11_akm_right (a c k m : Point) (AB AK KM : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hkKM : k.onLine KM) (hmKM : m.onLine KM)
    (hac : a ≠ c) (hak : a ≠ k) (hkm : k ≠ m)
    (hkac : ∠ k:a:c = ∟)
    (hcmAK : c.sameSide m AK)
    (hABKM : ¬(AB.intersectsLine KM)) :
    ∠ a:k:m = ∟ := by
  euclid_intros
  euclid_apply (proposition_29''''' c m a k AB KM AK)
  euclid_finish

end Elements.Book2
