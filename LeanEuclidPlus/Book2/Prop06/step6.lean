import SystemE
import Book.Prop36
import Book2.Prop06.step6_bgce_ne
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step6_lc
import Book2.Prop06.step6_hb
import Book2.Prop06.step6_sska
import Book2.Prop06.step6_sslc
import Book2.Prop06.step6_ssbh
import Book2.Prop06.step6_alpar
import Book2.Prop06.step6_chpar
import Book2.Prop06.step6_klh
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.6: since AC = CB, rectangle AL = rectangle CH [Prop.~1.36]. AL (= A,C,L,K) and CH (= C,B,H,L)
   are parallelograms on equal bases AC, CB of the top line AB, between the parallels AB and KM.
   proposition_36 on these two parallelograms gives the area equality.
   sub-nodes: step6_sska (k.sameSide a CE) + step6_alpar (AL pgram); step6_sslc (l.sameSide c BG) +
   step6_chpar (CH pgram); step6_klh (between k l h). -/
theorem helper_2_6_step6 (a b c d e k l h : Point) (AB KM AK CE BG DE : Line)
    (hacb : between a c b) (habd : between a b d) (hacb_len : |(a─c)| = |(c─b)|)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hhBG : h.onLine BG) (hbBG : b.onLine BG)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ c:b:h + Triangle.area △ c:h:l := by
  euclid_intros
  have step6_bgce_ne : BG ≠ CE := by euclid_apply (helper_2_6_step6_bgce_ne a b c d e AB CE BG (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step6_lc : l ≠ c := by euclid_apply (helper_2_6_step6_lc c l h AB KM (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  have step6_hb : h ≠ b := by euclid_apply (helper_2_6_step6_hb b h AB KM (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  have step6_sska : k.sameSide a CE := by euclid_apply (helper_2_6_step6_sska a b c d e k AB CE AK (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))
  have step6_sslc : l.sameSide c BG := by euclid_apply (helper_2_6_step6_sslc c l CE BG (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show BG ≠ CE; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step6_ssbh : b.sameSide h CE := by euclid_apply (helper_2_6_step6_ssbh b h CE BG (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show BG ≠ CE; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step6_alpar : formParallelogram k l a c KM AB AK CE := by euclid_apply (helper_2_6_step6_alpar a c k l AB KM AK CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l ≠ c; assumption)) (by euclid_assumption "" (show k.sameSide a CE; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))
  have step6_chpar : formParallelogram l h c b KM AB CE BG := by euclid_apply (helper_2_6_step6_chpar b c h l AB KM CE BG (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h ≠ b; assumption)) (by euclid_assumption "" (show l.sameSide c BG; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step6_klh : between k l h := by euclid_apply (helper_2_6_step6_klh a b c k l h AB CE KM (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show k.sameSide a CE; assumption)) (by euclid_assumption "" (show b.sameSide h CE; assumption)))
  euclid_apply (proposition_36 k a c l l c b h KM AB AK CE CE BG)
  euclid_finish

end Elements.Book2
