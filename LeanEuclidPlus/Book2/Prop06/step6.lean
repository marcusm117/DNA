import SystemE
import Book.Prop36
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.6: since AC = CB, rectangle AL = rectangle CH [Prop.~1.36]. AL (= A,C,L,K) and CH (= C,B,H,L)
   are parallelograms on equal bases AC, CB of the top line AB, between the parallels AB and KM.
   proposition_36 on these two parallelograms gives the area equality.
   sub-nodes: step6_sska (k.sameSide a CE) + step6_alpar (AL pgram); step6_sslc (l.sameSide c BG) +
   step6_chpar (CH pgram); step6_klh (between k l h). -/
set_option systemE.solverTime 30 in
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
  have step6_bgce_ne : BG ≠ CE := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  have step6_lc : l ≠ c := by sorry
  have step6_hb : h ≠ b := by sorry
  have step6_sska : k.sameSide a CE := by sorry
  have step6_sslc : l.sameSide c BG := by sorry
  have step6_ssbh : b.sameSide h CE := by sorry
  have step6_alpar : formParallelogram k l a c KM AB AK CE := by sorry
  have step6_chpar : formParallelogram l h c b KM AB CE BG := by sorry
  have step6_klh : between k l h := by sorry
  euclid_apply (proposition_36 k a c l l c b h KM AB AK CE CE BG)
  euclid_finish

end Elements.Book2
