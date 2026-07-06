import SystemE
import Book.Prop17
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step3
    (a b c d f : Point) (AB BC AC BD BF AD FC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (ha_nBC : ¬a.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hACAB : AC ≠ AB)
    (hoffBD : ¬a.onLine BD) (hd_BD : d.onLine BD)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (h_abf : (∠ a:b:f : ℝ) = ∟) (h_bac : (∠ b:a:c : ℝ) = ∟)
    (ha_AD : a.onLine AD) (hd_AD : d.onLine AD)
    (hf_FC : f.onLine FC) (hc_FC : c.onLine FC) :
    distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by
  have hbc : b ≠ c := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  euclid_apply (proposition_17 c a b AC AB BC)
  euclid_finish

end Elements.Book1
