import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step9_eaf
    (a b c e f f0 : Point) (AC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_aec : between a e c)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hab : a ≠ b)
    (hpy : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|) :
    between e a f := by
  -- Magnitude: |e-b| > |a-e| (Pythagoras on right triangle a-e-b, plus a ≠ b).
  -- NONLINEAR — keep OFF the SMT path (euclid_finish's translator chokes on squares).
  have hab_nn : (0 : ℝ) ≤ |(a─b)| := segment_gte_zero _
  have heb_nn : (0 : ℝ) ≤ |(e─b)| := segment_gte_zero _
  have hae_nn : (0 : ℝ) ≤ |(a─e)| := segment_gte_zero _
  have hab_pos : (0 : ℝ) < |(a─b)| := by
    rcases lt_or_eq_of_le hab_nn with h | h
    · exact h
    · exact (hab (zero_segment_if a b h.symm)).elim
  have hmag : |(e─b)| > |(a─e)| := by nlinarith [hpy, hab_pos, heb_nn, hae_nn]
  -- |e-f| = |e-b|; hence |e-f| > |e-a|, so f lies beyond a on ray e→f0.
  have hef : |(e─f)| = |(e─b)| := by euclid_finish
  have hmag2 : |(e─f)| > |(e─a)| := by euclid_finish
  clear hpy
  -- e, a, f are distinct collinear points on AC; between_points gives the 3-way order.
  have heAC : e.onLine AC := by euclid_finish
  have hea : e ≠ a := by euclid_finish
  have haef : a ≠ f := by euclid_finish
  have hfe : f ≠ e := by euclid_finish
  rcases between_points e a f AC ⟨hea, haef, hfe, heAC, haAC, hfAC⟩ with h1 | h2 | h3
  · -- between e a f : the desired order.
    exact h1
  · -- between a e f impossible: with between e f f0 it forces between a e f0, but a lies
    -- between e and f0 (between e a f0), contradiction.
    exfalso
    have heaf0 : between e a f0 := by euclid_finish
    have haef0 : between a e f0 := between_trans_out a e f f0 ⟨h2, hbet_eff0⟩
    exact (between_symm e a f0 heaf0).2.2.2 haef0
  · -- between e f a impossible: |e-a| = |e-f| + |f-a| ≥ |e-f|, contradicting |e-f| > |e-a|.
    exfalso
    have h3' : |(e─f)| + |(f─a)| = |(e─a)| := between_if e f a h3
    have hfa_nn : (0 : ℝ) ≤ |(f─a)| := segment_gte_zero _
    linarith [hmag2, h3', hfa_nn]

end Elements.Book2
