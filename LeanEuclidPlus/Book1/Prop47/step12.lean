import SystemE
import Book1.Prop04.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- SAS congruence △BDA ≅ △BCF ⟹ equal area: △ABD = △FBC.
theorem helper_1_47_step12
    (a b c d f : Point) (AB BC AC BD AD FC BF : Line)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hd_AD : d.onLine AD) (ha_AD : a.onLine AD)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hc_FC : c.onLine FC) (hf_FC : f.onLine FC)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_a_nBC : ¬a.onLine BC) (hoffBD : ¬a.onLine BD)
    (h_abf : (∠ a:b:f : ℝ) = ∟) (h_bac : (∠ b:a:c : ℝ) = ∟)
    (hlen1 : |(d─b)| = |(b─c)|) (hlen2 : |(f─b)| = |(b─a)|)
    (hang : ∠ d:b:a = ∠ f:b:c) :
    Triangle.area △ a:b:d = Triangle.area △ f:b:c := by
  euclid_apply (proposition_17 c a b AC AB BC)
  have hbc : b ≠ c := by euclid_finish
  have h_d_nAB : ¬d.onLine AB := by euclid_finish
  have h_f_nBC : ¬f.onLine BC := by euclid_finish
  have h_c_nBF : ¬c.onLine BF := by euclid_finish
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_finish

end Elements.Book1
