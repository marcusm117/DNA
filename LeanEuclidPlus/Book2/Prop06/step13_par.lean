import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.13 sub: formParallelogram l e h g CE BG KM EF (the square LG = LHGE). l,e on CE; h,g on BG;
   l,h on KM; e,g on EF; CE ∥ BG, KM ∥ EF; l.sameSide e BG. Assembled from the figure facts. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step13_par (e g h l : Point) (CE BG KM EF : Line)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hhBG : h.onLine BG) (hgBG : g.onLine BG)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hle : l ≠ e) (hlssh : l.sameSide e BG)
    (hBGCE : ¬(BG.intersectsLine CE)) (hKMEF : ¬(KM.intersectsLine EF)) :
    formParallelogram l e h g CE BG KM EF := by
  euclid_intros
  have hCEBG : ¬(CE.intersectsLine BG) := by
    intro hx; euclid_apply (intersection_symm CE BG); euclid_finish
  unfold formParallelogram
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
