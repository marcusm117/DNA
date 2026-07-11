import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step11_assumption2_fg_le
    (f g k e : Point) (ABCD : Circle) (FG : Line)
    (h_centre : e.isCentre ABCD)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (h_pf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|)
    (h_pg : |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)|)
    (hfg : f ≠ g) :
    |(f─g)| ≤ |(k─f)| + |(k─f)| := by
  -- Equal radii
  have h_ef_eg : |(e─f)| = |(e─g)| := by euclid_finish
  have h_ef_eg_sq : |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| := by rw [h_ef_eg]
  -- |k─f|² = |k─g|²
  have h_kf_kg_sq : |(k─f)| * |(k─f)| = |(k─g)| * |(k─g)| := by
    linarith [h_pf, h_pg, h_ef_eg_sq]
  -- |k─f| = |k─g|
  have h_kf_eq_kg : |(k─f)| = |(k─g)| := by
    nlinarith [h_kf_kg_sq, segment_gte_zero (k─f), segment_gte_zero (k─g)]
  by_cases h_kf_eq : k = f
  · -- k = f → |k─f| = 0 → |k─g| = 0 → k = g → f = g, contradicts hfg
    exfalso
    have h0_kf : |(k─f)| = 0 := zero_segment_onlyif k f h_kf_eq
    have h0_kf_sq : |(k─f)| * |(k─f)| = 0 := by
      nlinarith [h0_kf, segment_gte_zero (k─f)]
    have h0_kg_sq : |(k─g)| * |(k─g)| = 0 := by linarith [h_kf_kg_sq, h0_kf_sq]
    have h_kg_zero : |(k─g)| = 0 := by
      nlinarith [h0_kg_sq, segment_gte_zero (k─g)]
    exact hfg (h_kf_eq.symm.trans (zero_segment_if k g h_kg_zero))
  · by_cases h_kg_eq : k = g
    · -- k = g → |k─g| = 0 → |k─f| = 0 → k = f, contradicts h_kf_eq
      exfalso
      have h0_kg : |(k─g)| = 0 := zero_segment_onlyif k g h_kg_eq
      have h0_kg_sq : |(k─g)| * |(k─g)| = 0 := by
        nlinarith [h0_kg, segment_gte_zero (k─g)]
      have h0_kf_sq : |(k─f)| * |(k─f)| = 0 := by linarith [h_kf_kg_sq, h0_kg_sq]
      have h_kf_zero : |(k─f)| = 0 := by
        nlinarith [h0_kf_sq, segment_gte_zero (k─f)]
      exact h_kf_eq (zero_segment_if k f h_kf_zero)
    · -- k ≠ f and k ≠ g: use between_points on f k g
      rcases between_points f k g FG
        ⟨Ne.symm h_kf_eq, h_kg_eq, Ne.symm hfg, hf_FG, hk_FG, hg_FG⟩
        with h1 | h2 | h3
      · -- between f k g: |f─g| = |f─k| + |k─g| = 2|k─f|
        have h_fkg : |(f─k)| + |(k─g)| = |(f─g)| := between_if f k g h1
        have h_fk_kf : |(f─k)| = |(k─f)| := segment_symmetric f k
        linarith [h_fkg, h_fk_kf, h_kf_eq_kg]
      · -- between k f g: |k─f| + |f─g| = |k─g| = |k─f| → |f─g| = 0
        have h_kfg : |(k─f)| + |(f─g)| = |(k─g)| := between_if k f g h2
        linarith [h_kfg, h_kf_eq_kg, segment_gte_zero (k─f)]
      · -- between f g k: |f─g| + |g─k| = |f─k| = |k─f| = |k─g| = |g─k| → |f─g| = 0
        have h_fgk : |(f─g)| + |(g─k)| = |(f─k)| := between_if f g k h3
        have h_fk_kf : |(f─k)| = |(k─f)| := segment_symmetric f k
        have h_gk_kg : |(g─k)| = |(k─g)| := segment_symmetric g k
        linarith [h_fgk, h_fk_kf, h_gk_kg, h_kf_eq_kg, segment_gte_zero (k─f)]

end Elements.Book3
