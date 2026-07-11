import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_hlines (e h k : Point)
    (heh : e ≠ h)
    (h_lt : |(e─h)| < |(e─k)|) :
    ∃ EH EK : Line, distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK := by
  have hek : e ≠ k := by
    intro heq
    subst heq
    have hzero : |(e─e)| = 0 := zero_segment_onlyif e e rfl
    have hge : (0 : ℝ) ≤ |(e─h)| := segment_gte_zero (e─h)
    linarith
  euclid_apply (line_from_points e h) as EH
  euclid_apply (line_from_points e k) as EK
  exact ⟨EH, EK, ⟨by assumption, by assumption, heh⟩, ⟨by assumption, by assumption, hek⟩⟩

end Elements.Book3
