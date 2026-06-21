import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: complement parallelogram CBHL = formParallelogram c b l h AB KM CE BG. def a b c d
   AB CD AC BD: a=c,b=b on AB; c=l,d=h on KM; a=c,c=l on CE; b=b,d=h on BG. sameSide a.sameSide c BD =
   c.sameSide l BG (step7_sscl). BD-slot distinctPointsOnLine b h BG needs b ≠ h, from b ∈ AB, ¬h ∈ AB.
   Parallels AB∥KM, CE∥BG (KM∩AB / BG∩CE orientation, flipped in-body). refine + euclid_finish. -/
theorem helper_2_6_step7_cbhl (b c h l : Point) (AB KM CE BG : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hhoffAB : ¬(h.onLine AB)) (hsscl : c.sameSide l BG)
    (hKMAB : ¬(KM.intersectsLine AB)) (hBGCE : ¬(BG.intersectsLine CE)) :
    formParallelogram c b l h AB KM CE BG := by
  euclid_intros
  have hbh : b ≠ h := fun heq => hhoffAB (heq ▸ hbAB)
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  have hCEBG : ¬(CE.intersectsLine BG) := by
    intro hx; euclid_apply (intersection_symm CE BG); euclid_finish
  exact ⟨hcAB, hbAB, hlKM, hhKM, hcCE, hlCE, ⟨hbBG, hhBG, hbh⟩, hsscl, hABKM, hCEBG⟩

end Elements.Book2
