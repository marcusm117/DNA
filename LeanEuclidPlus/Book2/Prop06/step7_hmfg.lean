import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: complement parallelogram HMFG = formParallelogram h m g f KM EF BG DF. def a b c d
   AB CD AC BD: a=h,b=m on KM; c=g,d=f on EF; a=h,c=g on BG; b=m,d=f on DF. sameSide a.sameSide c BD =
   h.sameSide g DF (step7_sshg). BD-slot distinctPointsOnLine m f DF needs m ≠ f, from m ∈ KM, ¬f ∈ KM.
   Parallels KM∥EF, BG∥DF. refine + euclid_finish on the two non-intersection conjuncts. -/
theorem helper_2_6_step7_hmfg (f g h m : Point) (KM EF BG DF : Line)
    (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hhBG : h.onLine BG) (hgBG : g.onLine BG)
    (hmDF : m.onLine DF) (hfDF : f.onLine DF)
    (hfoffKM : ¬(f.onLine KM)) (hsshg : h.sameSide g DF)
    (hKMEF : ¬(KM.intersectsLine EF)) (hBGDF : ¬(BG.intersectsLine DF)) :
    formParallelogram h m g f KM EF BG DF := by
  euclid_intros
  have hmf : m ≠ f := fun heq => hfoffKM (heq ▸ hmKM)
  refine ⟨hhKM, hmKM, hgEF, hfEF, hhBG, hgBG, ⟨hmDF, hfDF, hmf⟩, hsshg, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
