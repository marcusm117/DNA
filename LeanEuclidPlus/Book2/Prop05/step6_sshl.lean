import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h and l (both on KM) are on the same side of EF. (Mirror of Prop06 step7_sshl.) h,l off
   EF (a common point of KM and EF would force them to meet, contra KM ∦ EF; KM ≠ EF since h ∈ KM,
   ¬h ∈ EF). Off EF and not separable ⟹ same side. -/
theorem helper_2_5_step6_sshl (h l : Point) (KM EF : Line)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    h.sameSide l EF := by
  euclid_intros
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  have hloff : ¬(l.onLine EF) := by
    by_contra hlon
    euclid_apply (intersection_lines_common_point l EF KM)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing h l EF KM)
  euclid_finish

end Elements.Book2
