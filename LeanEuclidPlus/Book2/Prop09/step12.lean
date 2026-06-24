import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop09.step12_split
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step12 (2.9.12): ∠AEB is a right-angle. The geometric angle-split lives in
-- step12_split (no ∟/2, euclid_finish); here only linarith combines it with the
-- half-angle facts (linarith tolerates ∟/2; euclid_finish's translator cannot).
theorem helper_2_9_step12
  (a b c e e0 e1 : Point) (AB CE EA EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (h10 : ∠ c:e:a = ∟ / 2 ∧ ∠ c:a:e = ∟ / 2)
  (h11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) :
  ∠ a:e:b = ∟ := by
  have step12_split : (∠ a:e:b = ∠ a:e:c + ∠ c:e:b) ∧ (∠ a:e:c = ∠ c:e:a) := by euclid_apply (helper_2_9_step12_split a b c e e0 e1 AB CE EA EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  linarith

end Elements.Book2
