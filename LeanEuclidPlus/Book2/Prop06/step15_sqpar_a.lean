import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: formParallelogram c e d f CE DF AB EF (the square CEFD, left–right orientation: c,e on
   CE; d,f on DF; c,d on AB; e,f on EF). Cut by KM at l (on CE) and m (on DF) for sum_parallelograms_area.
   The sameSide c.sameSide d EF (c,d both on AB ∥ EF) derived in-body. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step15_sqpar_a (c d e f : Point) (AB EF CE DF : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hcoffEF : ¬(c.onLine EF)) (hdoffEF : ¬(d.onLine EF)) (heoffDF : ¬(e.onLine DF))
    (hCEDF : ¬(CE.intersectsLine DF)) (hEFAB : ¬(EF.intersectsLine AB)) :
    formParallelogram c e d f CE DF AB EF := by
  euclid_intros
  have hcssd_ef : c.sameSide d EF := by
    by_contra hns; euclid_apply (intersection_lines_opposing c d EF AB); euclid_finish
  unfold formParallelogram
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
