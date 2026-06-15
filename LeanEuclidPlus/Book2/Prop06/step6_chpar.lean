import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: CH (= L,H,C,B) is a parallelogram. Top edge C,B on AB; bottom edge L,H on KM;
   left vertical CE (l,c); right vertical BG (h,b). The non-obvious conjunct l.sameSide c BG is passed
   in (proved by step6_sslc); h ≠ b passed in (step6_hb); the rest closes from the incidences. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step6_chpar (b c h l : Point) (AB KM CE BG : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hhBG : h.onLine BG) (hbBG : b.onLine BG)
    (hhb : h ≠ b) (hsslc : l.sameSide c BG)
    (hKMAB : ¬(KM.intersectsLine AB)) (hBGCE : ¬(BG.intersectsLine CE)) :
    formParallelogram l h c b KM AB CE BG := by
  euclid_intros
  euclid_finish

end Elements.Book2
