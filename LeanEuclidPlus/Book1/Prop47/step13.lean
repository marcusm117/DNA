import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step13_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Parallelogram BMLD (base BD, between parallels BD ∥ AL) = 2·△ABD [Prop.1.41];
-- parallelogram_area bridges the m─d diagonal split (prop_41 form) to the b─l split (claim form).
theorem helper_1_47_step13
    (a b d l m : Point) (AB BC BD DE AL AD : Line)
    (hm_AL : m.onLine AL) (hl_AL : l.onLine AL) (ha_AL : a.onLine AL)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hm_BC : m.onLine BC) (hb_BC : b.onLine BC)
    (hl_DE : l.onLine DE) (hd_DE : d.onLine DE)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (ha_AD : a.onLine AD) (hd_AD : d.onLine AD)
    (hoffBD : ¬a.onLine BD)
    (h_d_nBC : ¬d.onLine BC)
    (h_nDEBC : ¬DE.intersectsLine BC)
    (hassump1 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL)) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:b:d + Triangle.area △ a:b:d := by
  obtain ⟨_, _, h_nBDAL⟩ := hassump1
  have step13_pgram : formParallelogram m l b d AL BD BC DE := by euclid_apply (helper_1_47_step13_pgram a b d l m AL BD BC DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine AL; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)))
  euclid_apply (proposition_41 m b d l a AL BD BC DE AB AD)
  euclid_apply (parallelogram_area m l b d AL BD BC DE)
  euclid_finish

end Elements.Book1
