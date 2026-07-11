import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_fg_le
    (f g k e : Point) (ABCD : Circle) (FG : Line)
    (h_centre : e.isCentre ABCD)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (h_pf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|)
    (h_pg : |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)|)
    (hfg : f ≠ g) :
    |(f─g)| ≤ |(k─f)| + |(k─f)| := by
  -- Equal radii: |e─f| = |e─g|
  have h_ef_eg : |(e─f)| = |(e─g)| := by euclid_finish
  -- |e─f|² = |e─g|²
  have h_ef_eg_sq : |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| := by rw [h_ef_eg]
  -- |k─f|² = |k─g|²
  have h_kf_kg_sq : |(k─f)| * |(k─f)| = |(k─g)| * |(k─g)| := by
    nlinarith [h_pf, h_pg, h_ef_eg_sq, segment_gte_zero (e─k)]
  -- |k─f| = |k─g|
  have h_kf_kg : |(k─f)| = |(k─g)| := by
    nlinarith [h_kf_kg_sq, segment_gte_zero (k─f), segment_gte_zero (k─g)]
  -- Deduce |f─g| > 0 from f ≠ g
  have h_fg_pos : |(f─g)| > 0 := by
    rcases lt_or_eq_of_le (segment_gte_zero (f─g)) with h | h
    · exact h
    · exact absurd (zero_segment_if f g h.symm) hfg
  by_cases h_kf_eq : k = f
  · -- k = f: |k─f| = 0 and |k─g| = 0, forcing f = g
    exfalso
    have h0 : |(k─f)| = 0 := zero_segment_onlyif k f h_kf_eq
    have h0g : |(k─g)| = 0 := by linarith [h_kf_kg, h0]
    exact hfg (h_kf_eq.symm.trans (zero_segment_if k g h0g))
  · by_cases h_kg_eq : k = g
    · -- k = g: symmetric
      exfalso
      have h0g : |(k─g)| = 0 := zero_segment_onlyif k g h_kg_eq
      have h0 : |(k─f)| = 0 := by linarith [h_kf_kg, h0g]
      exact h_kf_eq (zero_segment_if k f h0)
    · rcases between_points f k g FG
          ⟨Ne.symm h_kf_eq, h_kg_eq, Ne.symm hfg, hf_FG, hk_FG, hg_FG⟩
          with h1 | h2 | h3
      · -- between f k g: |f─k| + |k─g| = |f─g| = 2|k─f|
        have h_fkg : |(f─k)| + |(k─g)| = |(f─g)| := between_if f k g h1
        have h_fk_kf : |(f─k)| = |(k─f)| := segment_symmetric f k
        linarith [h_fkg, h_fk_kf, h_kf_kg]
      · -- between k f g: |k─f| + |f─g| = |k─g| and |k─f| = |k─g| → |f─g| = 0. ⊥
        exfalso
        have h_kfg : |(k─f)| + |(f─g)| = |(k─g)| := between_if k f g h2
        linarith [h_kfg, h_kf_kg]
      · -- between f g k: |f─g| + |g─k| = |f─k| and |k─f| = |k─g| → |f─g| = 0. ⊥
        exfalso
        have h_fgk : |(f─g)| + |(g─k)| = |(f─k)| := between_if f g k h3
        have h_fk_kf : |(f─k)| = |(k─f)| := segment_symmetric f k
        have h_gk_kg : |(g─k)| = |(k─g)| := segment_symmetric g k
        linarith [h_fgk, h_fk_kf, h_gk_kg, h_kf_kg]

end Elements.Book3
