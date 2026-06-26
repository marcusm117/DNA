import SystemE
import Book2.Prop06.step6_sska_aoff
import Book2.Prop06.step7_coffdf
import Book2.Prop06.step9_aoffdf
import Book2.Prop06.step9_doffce
import Book2.Prop06.step6_sska
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step7_doffkm
import Book2.Prop06.step9_akdf
import Book2.Prop06.step9_ssak
import Book2.Prop06.step9_ssdm
import Book2.Prop06.step9_ampar
import Book2.Prop06.step9_acd
import Book2.Prop06.step9_klm
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9: the whole rectangle AM = AL + CM (add CM to AL). AM (= A,D,M,K) is cut by the vertical CE
   (at C on top AB, at L on bottom KM) into AL (A,C,L,K) and CM (C,D,M,L). sum_parallelograms_area on
   formParallelogram a d k m AB KM AK DF, with between a c d (on AB) and between k l m (on KM), yields
   △a:k:l + △a:l:c + △c:l:m + △c:m:d = △a:k:m + △a:m:d, which is the goal up to area-permutation.
   sub-nodes: step9_ampar (the AM parallelogram), step9_acd (between a c d), step9_klm (between k l m). -/
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
  have step6_sska_aoff : ¬(a.onLine CE) := by euclid_apply (helper_2_6_step6_sska_aoff a b c d e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have step7_coffdf : ¬(c.onLine DF) := by euclid_apply (helper_2_6_step7_coffdf a b c d f AB DF (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)))
  have step9_aoffdf : ¬(a.onLine DF) := by euclid_apply (helper_2_6_step9_aoffdf a b c d f AB DF (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)))
  have step9_doffce : ¬(d.onLine CE) := by euclid_apply (helper_2_6_step9_doffce a b c d e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have step6_sska : k.sameSide a CE := by euclid_apply (helper_2_6_step6_sska a b c d e k AB CE AK (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  -- @args: d h AB KM
  have step7_doffkm : ¬(d.onLine KM) := by euclid_apply (helper_2_6_step7_doffkm d h AB KM (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  -- parallels
  have step9_akdf : ¬(AK.intersectsLine DF) := by euclid_apply (helper_2_6_step9_akdf a c AK CE DF (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬(a.onLine CE); assumption)) (by euclid_assumption "" (show ¬(c.onLine DF); assumption)) (by euclid_assumption "" (show ¬(a.onLine DF); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)))
  -- sameSides
  have step9_ssak : a.sameSide k DF := by euclid_apply (helper_2_6_step9_ssak a k AK DF (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show ¬(a.onLine DF); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine DF); assumption)))
  have step9_ssdm : d.sameSide m CE := by euclid_apply (helper_2_6_step9_ssdm d m CE DF (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)))
  -- the AM parallelogram + the two cut betweennesses
  have step9_ampar : formParallelogram a d k m AB KM AK DF := by euclid_apply (helper_2_6_step9_ampar a d k m AB KM AK DF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show ¬(d.onLine KM); assumption)) (by euclid_assumption "" (show a.sameSide k DF; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine DF); assumption)))
  have step9_acd : between a c d := by euclid_apply (helper_2_6_step9_acd a b c d (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)))
  have step9_klm : between k l m := by euclid_apply (helper_2_6_step9_klm a c d k l m AB CE KM (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show k.sameSide a CE; assumption)) (by euclid_assumption "" (show d.sameSide m CE; assumption)))
  euclid_apply (sum_parallelograms_area a d k m c l AB KM AK DF)
  euclid_finish

end Elements.Book2
