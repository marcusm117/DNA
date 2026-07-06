import SystemE
import Book1.Prop13.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported helper_47_between_blc (l'=m): AL ⊥ BC at the foot m (∠a:m:b = ∠a:m:c = ∟) + acute base
-- angles ⟹ the foot m lands strictly between b and c.
theorem helper_1_47_step18_blc
    (a b c m : Point) (AB BC AC AL : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hbc : b ≠ c)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (h_a_nBC : ¬a.onLine BC)
    (hABBC : AB ≠ BC) (hACBC : AC ≠ BC)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (hm_BC : m.onLine BC)
    (h_acuteB : (∠ a:b:c : ℝ) < ∟) (h_acuteC : (∠ a:c:b : ℝ) < ∟)
    (h_perp_b : (∠ a:m:b : ℝ) = ∟) (h_perp_c : (∠ a:m:c : ℝ) = ∟) :
    between b m c := by
  by_cases hbtw : between b m c
  · exact hbtw
  · exfalso
    by_cases hb2 : between m b c
    · euclid_apply (proposition_17 a m b AL BC AB)
      euclid_apply (proposition_13 a b c m AB BC)
      euclid_finish
    · euclid_apply (proposition_17 a m c AL BC AC)
      euclid_apply (proposition_13 a c b m AC BC)
      euclid_finish

end Elements.Book1
