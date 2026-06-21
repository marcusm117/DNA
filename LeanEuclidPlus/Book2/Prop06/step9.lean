import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9: the whole rectangle AM = AL + CM (add CM to AL). AM (= A,D,M,K) is cut by the vertical CE
   (at C on top AB, at L on bottom KM) into AL (A,C,L,K) and CM (C,D,M,L). sum_parallelograms_area on
   formParallelogram a d k m AB KM AK DF, with between a c d (on AB) and between k l m (on KM), yields
   △a:k:l + △a:l:c + △c:l:m + △c:m:d = △a:k:m + △a:m:d, which is the goal up to area-permutation.
   sub-nodes: step9_ampar (the AM parallelogram), step9_acd (between a c d), step9_klm (between k l m). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step9 (a b c d e f k l m h : Point) (AB KM AK DF CE BG DE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF) (hfDF : f.onLine DF)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hhKM : h.onLine KM) (hhBG : h.onLine BG) (hhDE : h.onLine DE)
    (hbBG : b.onLine BG) (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|)
    (hdce : ∠ d:c:e = ∟) (hcdf : ∠ c:d:f = ∟)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE))
    (hCEDF : ¬(CE.intersectsLine DF)) (hBGCE : ¬(BG.intersectsLine CE)) :
    Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) := by
  euclid_intros
  -- off-line anchors
  have step6_sska_aoff : ¬(a.onLine CE) := by sorry
  have step7_coffdf : ¬(c.onLine DF) := by sorry
  have step9_aoffdf : ¬(a.onLine DF) := by sorry
  have step9_doffce : ¬(d.onLine CE) := by sorry
  have step6_sska : k.sameSide a CE := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  -- @args: d h AB KM
  have step7_doffkm : ¬(d.onLine KM) := by sorry
  -- parallels
  have step9_akdf : ¬(AK.intersectsLine DF) := by sorry
  -- sameSides
  have step9_ssak : a.sameSide k DF := by sorry
  have step9_ssdm : d.sameSide m CE := by sorry
  -- the AM parallelogram + the two cut betweennesses
  have step9_ampar : formParallelogram a d k m AB KM AK DF := by sorry
  have step9_acd : between a c d := by sorry
  have step9_klm : between k l m := by sorry
  euclid_apply (sum_parallelograms_area a d k m c l AB KM AK DF)
  euclid_finish

end Elements.Book2
