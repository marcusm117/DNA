import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: d and b (both on AB) are on the same side of KM. d,b off KM (a common point of AB and
   KM would force them to meet, contradicting AB ∦ KM; AB ≠ KM since h ∈ KM, ¬h ∈ AB). Off KM and not
   separable, d and b share a side. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_ssdb (b d h : Point) (AB KM : Line)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    d.sameSide b KM := by
  euclid_intros
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hdoff : ¬(d.onLine KM) := by
    by_contra hdon
    euclid_apply (intersection_lines_common_point d KM AB)
    euclid_finish
  have hboff : ¬(b.onLine KM) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b KM AB)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d b KM AB)
  euclid_finish

end Elements.Book2
