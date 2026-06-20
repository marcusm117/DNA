import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: formParallelogram l m e f KM EF CE DF (the bottom strip LMFE: l,m on KM; e,f on EF;
   l,e on CE; m,f on DF). Cut by BG at h (on KM) and g (on EF) for sum_parallelograms_area.
   The sameSide l.sameSide e DF passed in (l,e both on CE ∥ DF). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step15_botpar (e f l m : Point) (KM EF CE DF : Line)
    (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hmDF : m.onLine DF) (hfDF : f.onLine DF)
    (hle : l ≠ e) (hlsse_df : l.sameSide e DF)
    (hKMEF : ¬(KM.intersectsLine EF)) (hCEDF : ¬(CE.intersectsLine DF)) :
    formParallelogram l m e f KM EF CE DF := by
  euclid_intros
  unfold formParallelogram
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
