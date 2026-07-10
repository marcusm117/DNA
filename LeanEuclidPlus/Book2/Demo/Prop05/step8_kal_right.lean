import SystemE
import Book1Variants.Prop29
import Helpers.RightAngle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8 sub: ∠ k:a:c = ∟ (rectangle AL has a right angle at a).
   AK ∥ CE are cut by the transversal AB at the feet a (on AK) and c (on CE).
   The co-interior angles sum to two right angles (proposition_29'''''):
     ∠ k:a:c + ∠ a:c:e = ∟ + ∟.
   And ∠ a:c:e = ∟ since CE ⊥ AB at c: ∠ b:c:e = ∟ and a–c–b is straight
   (between a c d, between c d b ⟹ between a c b), so the supplement ∠ a:c:e is
   also right. Hence ∠ k:a:c = ∟.
   k.sameSide e AB: k on KM ∥ AB so k.sameSide l AB (l also on KM); l.sameSide e AB
   by pasch_2 (between c l e, c on AB, l off AB); transitivity gives k.sameSide e AB.
   The off-AB facts and `between c l e` are figure facts Main supplies. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_kal_right (a b c d e k l : Point) (AB AK CE KM EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b)
    (hbce : ∠ b:c:e = ∟)
    (hcle : between c l e)
    (hAKCE : ¬(AK.intersectsLine CE))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ∠ k:a:c = ∟ := by
  euclid_intros
  -- off-AB facts (k,l on KM ∥ AB; e on EF ∥ AB), derived locally
  have hkoffAB : ¬(k.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point k AB KM); euclid_finish
  have hloffAB : ¬(l.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point l AB KM); euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point e AB EF); euclid_finish
  -- a–c–b is a straight line (combine the two betweens)
  have habt : between a c b := by euclid_finish
  -- supplement: ∠ a:c:e = ∟ because ∠ b:c:e = ∟ and a,c,b collinear with c between
  have hace : ∠ a:c:e = ∟ := by euclid_finish
  -- k.sameSide e AB by transitivity through l
  have hkl : k.sameSide l AB := by
    by_contra hns
    euclid_apply (intersection_lines_opposing k l AB KM)
    euclid_finish
  have hle : l.sameSide e AB := by
    euclid_apply (pasch_2 c l e AB)
    euclid_finish
  have hke : k.sameSide e AB := by euclid_finish
  -- co-interior core via the shared lemma: AK ∥ CE cut by AB at feet a,c; ∠a:c:e = ∟ ⟹ ∠k:a:c = ∟
  euclid_apply (right_angle_cointerior k e a c AK CE AB)
  euclid_finish

end Elements.Book2
