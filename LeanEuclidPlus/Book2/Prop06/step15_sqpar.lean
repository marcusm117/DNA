import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: formParallelogram c d e f AB EF CE DF (the square CEFD, top–bottom orientation: c,d on
   AB; e,f on EF; c,e on CE; d,f on DF). Used by rectangle_area to compute its area as |c─d|². -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step15_sqpar (c d e f : Point) (AB EF CE DF : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hecDF : e.sameSide c DF) (hdoffEF : ¬(d.onLine EF))
    (hEFAB : ¬(EF.intersectsLine AB)) (hCEDF : ¬(CE.intersectsLine DF)) :
    formParallelogram c d e f AB EF CE DF := by
  euclid_intros
  unfold formParallelogram
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
