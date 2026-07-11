import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
import Book3.Prop15.step11_assumption2_pg_ekg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_pg
    (k g e f : Point) (ABCD : Circle) (FG EK : Line)
    (h_centre : e.isCentre ABCD) (hg_on : g.onCircle ABCD)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (h_e_off_FG : ¬e.onLine FG)
    (hperp_k : ∠ e:k:f = ∟)
    (h_fkg : between f k g) :
    |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)| := by
  by_cases hkg : k = g
  · have h0 : |(k─g)| = 0 := zero_segment_onlyif k g hkg
    have heq : |(e─g)| = |(e─k)| := by rw [← hkg]
    nlinarith [segment_gte_zero (e─k), h0]
  · by_cases hke : k = e
    · have h0 : |(e─k)| = 0 := zero_segment_onlyif e k hke.symm
      have heq : |(k─g)| = |(e─g)| := by rw [hke]
      have h1 : |(k─g)| * |(k─g)| = |(e─g)| * |(e─g)| := by rw [heq]
      nlinarith [h0, h1]
    · -- Non-degenerate: k ≠ g, k ≠ e; ¬e.onLine FG + EK line + perp gives ∠e:k:g = ∟
      have step11_assumption2_pg_ekg : ∠ e:k:g = ∟ := by euclid_apply (helper_3_15_step11_assumption2_pg_ekg k g e f FG EK (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show ¬e.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show k ≠ g; assumption)) (by euclid_assumption "" (show k ≠ e; assumption)) (by euclid_assumption "" (show between f k g; assumption)))
      -- right angle at k: apply prop47 at vertex k
      euclid_apply (line_from_points e k) as EK2
      euclid_apply (line_from_points e g) as EG2
      have htri : formTriangle k e g EK2 EG2 FG := by euclid_finish
      have hp := Elements.Book1.proposition_47 k e g EK2 EG2 FG ⟨htri, step11_assumption2_pg_ekg⟩
      linarith [hp]

end Elements.Book3
