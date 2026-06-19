import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: b and d (both on AB) are on the same side of KM. (Mirror of Prop06 step7_ssdb, relabel
   d↔b.) b,d off KM (a common point of AB and KM would force them to meet, contra AB ∦ KM; AB ≠ KM
   since h ∈ KM, ¬h ∈ AB). Off KM and not separable ⟹ same side. -/
theorem helper_2_5_step6_ssbd (b d h : Point) (AB KM : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    b.sameSide d KM := by
  euclid_intros
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hboff : ¬(b.onLine KM) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b KM AB)
    euclid_finish
  have hdoff : ¬(d.onLine KM) := by
    by_contra hdon
    euclid_apply (intersection_lines_common_point d KM AB)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b d KM AB)
  euclid_finish

end Elements.Book2
