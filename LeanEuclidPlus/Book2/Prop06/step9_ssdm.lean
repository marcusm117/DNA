import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: d.sameSide m CE (d and m both on DF, which is parallel to CE). d,m off CE (a common
   point of DF and CE would force them to meet, contradicting CE ∦ DF; DF ≠ CE since d ∈ DF, ¬d ∈ CE).
   Off CE and not separable, d and m share a side. d ∉ CE supplied (step9_doffce). -/
theorem helper_2_6_step9_ssdm (d m : Point) (CE DF : Line)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF)
    (hdoffCE : ¬(d.onLine CE))
    (hCEDF : ¬(CE.intersectsLine DF)) :
    d.sameSide m CE := by
  euclid_intros
  have hDFneCE : DF ≠ CE := fun heq => hdoffCE (heq ▸ hdDF)
  have hmoff : ¬(m.onLine CE) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point m CE DF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d m CE DF)
  euclid_finish

end Elements.Book2
