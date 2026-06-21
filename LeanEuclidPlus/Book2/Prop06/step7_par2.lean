import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: parallelogram HGLE = formParallelogram h g l e BG CE KM EF. def a b c d AB CD AC BD:
   a=h,b=g on BG; c=l,d=e on CE; a=h,c=l on KM; b=g,d=e on EF. sameSide a.sameSide c BD = h.sameSide l
   EF (step7_sshl). BD-slot distinctPointsOnLine g e EF needs g ≠ e, from g ∈ BG, ¬e ∈ BG. Parallels
   BG∥CE, KM∥EF. Assembled by refine so euclid_finish only closes the two non-intersection conjuncts. -/
theorem helper_2_6_step7_par2 (e g h l : Point) (BG CE KM EF : Line)
    (hhBG : h.onLine BG) (hgBG : g.onLine BG)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (heoffBG : ¬(e.onLine BG)) (hsshl : h.sameSide l EF)
    (hBGCE : ¬(BG.intersectsLine CE)) (hKMEF : ¬(KM.intersectsLine EF)) :
    formParallelogram h g l e BG CE KM EF := by
  euclid_intros
  have hge : g ≠ e := fun heq => heoffBG (heq ▸ hgBG)
  refine ⟨hhBG, hgBG, hlCE, heCE, hhKM, hlKM, ⟨hgEF, heEF, hge⟩, hsshl, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
