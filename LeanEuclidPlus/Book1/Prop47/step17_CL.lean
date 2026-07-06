import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step17_ALCE
import Book1.Prop47.step17_CL_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Parallelogram CMLE (base CE, between parallels CE ∥ AL) = 2·△ACE [Prop.1.41] (mirror of step13).
theorem helper_1_47_step17_CL
    (a b c e l m : Point) (AC CE BC DE AL AE BD : Line)
    (hm_AL : m.onLine AL) (hl_AL : l.onLine AL) (ha_AL : a.onLine AL)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hm_BC : m.onLine BC) (hc_BC : c.onLine BC)
    (hl_DE : l.onLine DE) (he_DE : e.onLine DE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (h_offCE : ¬a.onLine CE) (hoffBD : ¬a.onLine BD)
    (hb_BD : b.onLine BD) (hb_BC : b.onLine BC) (h_c_nBD : ¬c.onLine BD)
    (h_e_nBC : ¬e.onLine BC)
    (h_nDEBC : ¬DE.intersectsLine BC)
    (h_nALBD : ¬AL.intersectsLine BD) (h_nBDCE : ¬BD.intersectsLine CE) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:c:e + Triangle.area △ a:c:e := by
  have step17_ALCE : ¬AL.intersectsLine CE := by euclid_apply (helper_1_47_step17_ALCE a b c AL CE BD BC (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  have step17_CL_pgram : formParallelogram m l c e AL CE BC DE := by euclid_apply (helper_1_47_step17_CL_pgram a c e l m AL CE BC DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬e.onLine BC; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)))
  euclid_apply (proposition_41 m c e l a AL CE BC DE AC AE)
  euclid_apply (parallelogram_area m l c e AL CE BC DE)
  euclid_finish

end Elements.Book1
