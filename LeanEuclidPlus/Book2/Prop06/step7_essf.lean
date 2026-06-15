import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: e.sameSide f KM (e and f both on EF, which is parallel to KM). e,f off KM (a common
   point of EF and KM would force them to meet, contradicting KM ∦ EF; KM ≠ EF since h ∈ KM, ¬h ∈ EF).
   Off KM and not separable, e and f share a side. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_essf (e f h : Point) (EF KM : Line)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    e.sameSide f KM := by
  euclid_intros
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  have heoff : ¬(e.onLine KM) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point e KM EF)
    euclid_finish
  have hfoff : ¬(f.onLine KM) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point f KM EF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing e f KM EF)
  euclid_finish

end Elements.Book2
