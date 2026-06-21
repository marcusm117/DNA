import SystemE
import Book.Prop29
import Helpers.RightAngle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.13 sub: ∠ c:b:h = ∟ (BG ⊥ AB at b). BG ∥ CE are cut by the transversal AB at the feet b (on BG)
   and c (on CE). The co-interior angles sum to two right angles (right_angle_cointerior):
   ∠ h:b:c + ∠ b:c:e = ∟ + ∟. And ∠ b:c:e = ∟ (ray c→b ≡ c→d, ∠ d:c:e = ∟). Hence ∠ c:b:h = ∟.
   h.sameSide e AB: h on KM ∥ AB so h.sameSide l AB; l.sameSide e AB by pasch_2 (between c l e);
   transitivity gives h.sameSide e AB. -/
theorem helper_2_6_step13_cbh_right (a b c d e h l : Point) (AB BG CE KM EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (heEF : e.onLine EF)
    (hacb : between a c b) (habd : between a b d)
    (hdce : ∠ d:c:e = ∟)
    (hcle : between c l e)
    (hBGCE : ¬(BG.intersectsLine CE))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ∠ c:b:h = ∟ := by
  euclid_intros
  have hhoffAB : ¬(h.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point h AB KM); euclid_finish
  have hloffAB : ¬(l.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point l AB KM); euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point e AB EF); euclid_finish
  have hcbd : between c b d := by euclid_finish
  have hbce : ∠ b:c:e = ∟ := by
    euclid_apply (equal_angles c b d e e AB CE)
    euclid_finish
  have hhl : h.sameSide l AB := by
    by_contra hns; euclid_apply (intersection_lines_opposing h l AB KM); euclid_finish
  have hle : l.sameSide e AB := by
    euclid_apply (pasch_2 c l e AB); euclid_finish
  have hhe : h.sameSide e AB := by euclid_finish
  euclid_apply (right_angle_cointerior h e b c BG CE AB)
  euclid_finish

end Elements.Book2
