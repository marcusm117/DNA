import SystemE
import Book.Prop29
import Helpers.RightAngle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: ∠ k:a:c = ∟ (rectangle AM / AL has a right angle at a).
   AK ∥ CE are cut by the transversal AB at the feet a (on AK) and c (on CE). The co-interior angles
   sum to two right angles (right_angle_cointerior): ∠ k:a:c + ∠ a:c:e = ∟ + ∟. And ∠ a:c:e = ∟,
   the supplement of ∠ d:c:e = ∟ (CE ⊥ AB at c, with a–c–d straight). Hence ∠ k:a:c = ∟.
   k.sameSide e AB: k on KM ∥ AB so k.sameSide l AB; l.sameSide e AB by pasch_2 (between c l e);
   transitivity gives k.sameSide e AB. (Mirror of Prop05 step8_kal_right.) -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11_kac_right (a b c d e k l : Point) (AB AK CE KM EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (heEF : e.onLine EF)
    (hacb : between a c b) (habd : between a b d)
    (hdce : ∠ d:c:e = ∟)
    (hcle : between c l e)
    (hAKCE : ¬(AK.intersectsLine CE))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ∠ k:a:c = ∟ := by
  euclid_intros
  have hkoffAB : ¬(k.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point k AB KM); euclid_finish
  have hloffAB : ¬(l.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point l AB KM); euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point e AB EF); euclid_finish
  have hacd : between a c d := by euclid_finish
  have hace : ∠ a:c:e = ∟ := by euclid_finish
  have hkl : k.sameSide l AB := by
    by_contra hns; euclid_apply (intersection_lines_opposing k l AB KM); euclid_finish
  have hle : l.sameSide e AB := by
    euclid_apply (pasch_2 c l e AB); euclid_finish
  have hke : k.sameSide e AB := by euclid_finish
  euclid_apply (right_angle_cointerior k e a c AK CE AB)
  euclid_finish

end Elements.Book2
