import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- h ≠ b: if h = b then |e─h| = |e─b| = |e─m|, so |e─l| = |e─m|,
-- then |l─m|² + |e─l|² = |e─m|² → |l─m|² = 0 → l = m, contradicting between m l n.
theorem helper_3_15_step6_hb_ne
    (b h l m n e : Point) (ABCD : Circle)
    (step6_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|)
    (step6_rad : |(e─b)| = |(e─m)|)
    (hassump1 : |(e─h)| = |(e─l)|)
    (hbetw_mln : between m l n) :
    h ≠ b := by
  intro heq
  -- h = b → |e─h| = |e─b|; combined with hassump1 and step6_rad: |e─l| = |e─m|
  have hassump1' : |(e─b)| = |(e─l)| := by rw [← heq]; exact hassump1
  have h_el_em : |(e─l)| = |(e─m)| := by linarith [hassump1', step6_rad]
  -- |e─l|² = |e─m|² (by rewriting with h_el_em)
  have h_el_sq : |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by rw [h_el_em]
  -- step6_pm + h_el_sq → |l─m|² = 0
  have h_lm_sq : |(l─m)| * |(l─m)| = 0 := by nlinarith [step6_pm, h_el_sq]
  -- |l─m| = 0 → l = m
  have h_lm_eq : l = m := zero_segment_if l m (by nlinarith [segment_gte_zero (l─m), h_lm_sq])
  exact absurd h_lm_eq.symm (between_symm m l n hbetw_mln).2.1

end Elements.Book3
