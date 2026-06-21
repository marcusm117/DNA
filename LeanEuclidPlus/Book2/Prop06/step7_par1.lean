import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: parallelogram DMBH = formParallelogram d m b h DF BG AB KM. def a b c d AB CD AC BD:
   a=d,b=m on DF; c=b,d=h on BG; a=d,c=b on AB; b=m,d=h on KM. sameSide a.sameSide c BD = d.sameSide b
   KM (step7_ssdb). BD-slot distinctPointsOnLine m h KM needs m ≠ h, from m ∈ DF, ¬h ∈ DF. The two
   parallels DF∥BG, AB∥KM supplied (BG∩DF / KM∩AB orientation, flipped in-body). Assembled by refine
   so euclid_finish only closes the two non-intersection conjuncts. -/
theorem helper_2_6_step7_par1 (b d h m : Point) (DF BG AB KM : Line)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hhoffDF : ¬(h.onLine DF)) (hssdb : d.sameSide b KM)
    (hBGDF : ¬(BG.intersectsLine DF)) (hKMAB : ¬(KM.intersectsLine AB)) :
    formParallelogram d m b h DF BG AB KM := by
  euclid_intros
  have hmh : m ≠ h := fun heq => hhoffDF (heq ▸ hmDF)
  refine ⟨hdDF, hmDF, hbBG, hhBG, hdAB, hbAB, ⟨hmKM, hhKM, hmh⟩, hssdb, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
