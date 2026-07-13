import SystemE
import Book3.Prop09.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (AC : Line) (α₁ : Circle)
    (ha_ac : a.onLine AC) (hc_ac : c.onLine AC) (ha_ne_c : a ≠ c) (hb_off : ¬b.onLine AC)
    (he_centre : e.isCentre α₁) (ha_circ : a.onCircle α₁)
    (hstep15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  have hb_circ : b.onCircle α₁ := by euclid_finish
  have hc_circ : c.onCircle α₁ := by euclid_finish
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
