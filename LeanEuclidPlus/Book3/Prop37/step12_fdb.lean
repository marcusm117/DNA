import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step12_fdb (d e f b : Point) (DB : Line)
    (h_b_DB : b.onLine DB) (h_d_DB : d.onLine DB)
    (h_pyth : |(f─d)| * |(f─d)| = |(f─e)| * |(f─e)| + |(e─d)| * |(e─d)|)
    (h_de_db : |(d─e)| = |(d─b)|) (h_fe_fb : |(f─e)| = |(f─b)|)
    (h_bd : b ≠ d) (h_fb : f ≠ b) (h_fd : f ≠ d) :
    ¬ f.onLine DB := by
  intro hf_DB
  have h_ed_bd : |(e─d)| = |(b─d)| := by
    rw [segment_symmetric e d, segment_symmetric b d]; exact h_de_db
  have key : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(b─d)| * |(b─d)| := by
    rw [← h_fe_fb, ← h_ed_bd]; exact h_pyth
  have hfb_pos : |(f─b)| > 0 :=
    lt_of_le_of_ne (segment_gte_zero _) (fun h => h_fb (zero_segment_if f b h.symm))
  have hbd_pos : |(b─d)| > 0 :=
    lt_of_le_of_ne (segment_gte_zero _) (fun h => h_bd (zero_segment_if b d h.symm))
  have hfd0 : (0:ℝ) ≤ |(f─d)| := segment_gte_zero _
  rcases between_points f b d DB ⟨h_fb, h_bd, h_fd.symm, hf_DB, h_b_DB, h_d_DB⟩ with hbet | hbet | hbet
  · -- between f b d: |f─d| = |f─b| + |b─d|
    have hL : |(f─d)| = |(f─b)| + |(b─d)| := (between_if f b d hbet).symm
    rw [hL] at key
    nlinarith [key, mul_pos hfb_pos hbd_pos]
  · -- between b f d: |b─d| = |f─b| + |f─d|
    have hL : |(b─d)| = |(f─b)| + |(f─d)| := by
      have h := between_if b f d hbet
      rw [segment_symmetric b f] at h; linarith [h]
    rw [hL] at key
    nlinarith [key, mul_pos hfb_pos hfb_pos, mul_nonneg (le_of_lt hfb_pos) hfd0]
  · -- between f d b: |f─b| = |f─d| + |b─d|
    have hL : |(f─b)| = |(f─d)| + |(b─d)| := by
      have h := between_if f d b hbet
      rw [segment_symmetric d b] at h; linarith [h]
    rw [hL] at key
    nlinarith [key, mul_pos hbd_pos hbd_pos, mul_nonneg hfd0 (le_of_lt hbd_pos)]

end Elements.Book3
