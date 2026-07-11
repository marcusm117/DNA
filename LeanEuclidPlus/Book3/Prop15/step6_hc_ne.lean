import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- h ≠ c: if h = c then |e─h| = |e─c| = |e─m| (equal radii), so |e─l| = |e─m|,
-- then |l─m|² = 0 → l = m, contradicting between m l n.
set_option systemE.solverTime 30 in
theorem helper_3_15_step6_hc_ne
    (c h l m n e : Point) (ABCD : Circle)
    (h_centre : e.isCentre ABCD) (hm_on : m.onCircle ABCD) (hc_on : c.onCircle ABCD)
    (step6_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|)
    (hassump1 : |(e─h)| = |(e─l)|)
    (hbetw_mln : between m l n) :
    h ≠ c := by
  intro heq
  -- h = c → |e─h| = |e─c|; equal radii give |e─c| = |e─m|; hassump1 gives |e─l| = |e─m|
  have hassump1' : |(e─c)| = |(e─l)| := by rw [← heq]; exact hassump1
  have h_ec_em : |(e─c)| = |(e─m)| := by euclid_finish
  have h_el_em : |(e─l)| = |(e─m)| := by linarith [hassump1', h_ec_em]
  -- |e─l|² = |e─m|²
  have h_el_sq : |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by rw [h_el_em]
  -- step6_pm + h_el_sq → |l─m|² = 0
  have h_lm_sq : |(l─m)| * |(l─m)| = 0 := by nlinarith [step6_pm, h_el_sq]
  have h_lm_eq : l = m := zero_segment_if l m (by nlinarith [segment_gte_zero (l─m), h_lm_sq])
  exact absurd h_lm_eq.symm (between_symm m l n hbetw_mln).2.1

end Elements.Book3
