import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: formParallelogram l e h g CE DG KM EF (the square LG = LEGH).
   l,e on CE; h,g on DG; l,h on KM; e,g on EF; CE ∥ DG, KM ∥ EF; l.sameSide e KM-side etc.
   Assembled from the figure facts (sides on the four lines, the two parallelisms, the sameSide and
   the distinctness), all passed in / derived in-body. -/
theorem helper_2_5_step15_par (e g h l : Point) (CE DG KM EF : Line)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hle : l ≠ e) (hlssh : l.sameSide e DG)
    (hCEDG : ¬(CE.intersectsLine DG)) (hKMEF : ¬(KM.intersectsLine EF)) :
    formParallelogram l e h g CE DG KM EF := by
  euclid_intros
  unfold formParallelogram
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
