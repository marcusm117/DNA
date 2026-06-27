import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop10.step15_split
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step15 (2.10.15): ∠AEB is a right-angle. ray ec splits it (step15_split):
-- ∠a:e:b = ∠a:e:c + ∠c:e:b = ∟/2 + ∟/2 (step13.2, step14.1).
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
  have step15_split : ∠ a:e:b = ∠ a:e:c + ∠ c:e:b := by euclid_apply (helper_2_10_step15_split a b c e e0 e1 AD CE EA EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)))
  linarith [h13.2, h14.1, step15_split]

end Elements.Book2
