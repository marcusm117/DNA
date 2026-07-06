import SystemE
import Book1.Prop05.variants
import Mathlib.Tactic.Linarith
import Book1.Prop07.step5_c2_iso
import Book1.Prop07.step5_c2_sumc
import Book1.Prop07.step5_c2_sum
import Book1.Prop07.step5_c2_s5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Case 2: a.sameSide b CD ∧ ¬d.sameSide b AC → contradiction (Euclid omitted)
-- linarith closes the angle arithmetic (0 = ∠a:d:b + ∠a:c:b) from 4 sub-nodes;
-- trailing euclid_finish closes geometry (∠a:d:b = 0 → d on AB → ¬hsameSide)
theorem helper_1_7_step5_c2 (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB) (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (step4 : ∠ a:c:d = ∠ a:d:c)
    (h1 : a.sameSide b CD) (h2 : ¬d.sameSide b AC)
    : ∠ a:d:c > ∠ d:c:b := by
  exfalso
  have step5_c2_iso : ∠ b:d:c = ∠ b:c:d := by euclid_apply (helper_1_7_step5_c2_iso a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ a:d:c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬d.sameSide b AC; assumption)))
  have step5_c2_sumc : ∠ d:c:b = ∠ d:c:a + ∠ a:c:b := by euclid_apply (helper_1_7_step5_c2_sumc a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ a:d:c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬d.sameSide b AC; assumption)))
  have step5_c2_sum : ∠ a:d:c = ∠ a:d:b + ∠ b:d:c := by euclid_apply (helper_1_7_step5_c2_sum a b c d AB AC CB AD DB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide d AB; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(c─b)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ a:d:c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬d.sameSide b AC; assumption)))
  have step5_c2_s5 : ∠ d:c:b = ∠ a:d:c + ∠ a:c:b := by euclid_apply (helper_1_7_step5_c2_s5 a b c d AC CB AD CD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CB; assumption)) (by euclid_assumption "" (show b.onLine CB; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ a:d:c; assumption)) (by euclid_assumption "" (show ∠ d:c:b = ∠ d:c:a + ∠ a:c:b; assumption)))
  have h_bcd_sym : ∠ b:c:d = ∠ d:c:b := by euclid_finish
  have h_adb_nonneg : (0 : ℝ) ≤ ∠ a:d:b := by euclid_finish
  have h_acb_nonneg : (0 : ℝ) ≤ ∠ a:c:b := by euclid_finish
  have h_adb_zero : ∠ a:d:b = 0 := by linarith
  have h_b_on_AD : b.onLine AD := by euclid_finish
  have h_AB_eq_AD : AB = AD := by euclid_finish
  euclid_finish

end Elements.Book1
