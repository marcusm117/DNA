import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step15 (2.10.15): ∠AEB is a right-angle. ray ec splits it (step15_split):
-- ∠a:e:b = ∠a:e:c + ∠c:e:b = ∟/2 + ∟/2 (step13.2, step14.1).
set_option systemE.solverTime 30 in
theorem helper_2_10_step15
  (a b c e e0 e1 : Point) (AD CE EA EB : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hacb : between a c b)
  (hbte : between c e e1)
  (h13 : ∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2)
  (h14 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) :
  ∠ a:e:b = ∟ := by
  have step15_split : ∠ a:e:b = ∠ a:e:c + ∠ c:e:b := by sorry
  linarith [h13.2, h14.1, step15_split]

end Elements.Book2
