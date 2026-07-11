import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step7 (a f g : Point) (ABC : Circle) (AF AG : Line)
    (left : f.isCentre ABC)
    (left_6 : ¬g.insideCircle ABC)
    (step2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG)
    (hsuppose1 : ¬between f a g)
    : |(f─g)| < |(f─a)| + |(a─g)| := by
  have hfNa : f ≠ a := step2.1.2.2.symm
  have hgNa : g ≠ a := step2.2.2.2.symm
  have hf_in : f.insideCircle ABC := center_inside_circle f ABC left
  have hfNg : f ≠ g := fun h => left_6 (h ▸ hf_in)
  obtain ⟨FG, hf_FG, hg_FG⟩ := line_from_points f g hfNg
  rcases Classical.em (a.onLine FG) with ha_FG | ha_not_FG
  · rcases between_points f g a FG ⟨hfNg, hgNa, step2.1.2.2, hf_FG, hg_FG, ha_FG⟩
        with h1 | h2 | h3
    · -- between f g a: |f─g| + |g─a| = |f─a|, so |f─a| + |a─g| > |f─g|
      have hlen := between_if f g a h1
      have hag_nz : |(a─g)| ≠ 0 := fun h => hgNa.symm (zero_segment_if a g h)
      have hag_pos : 0 < |(a─g)| :=
        lt_of_le_of_ne (segment_gte_zero (a─g)) (Ne.symm hag_nz)
      linarith [segment_symmetric g a]
    · -- between g f a: |g─f| + |f─a| = |g─a|, so |f─a| + |a─g| > |f─g|
      have hlen := between_if g f a h2
      have hfa_nz : |(f─a)| ≠ 0 := fun h => hfNa (zero_segment_if f a h)
      have hfa_pos : 0 < |(f─a)| :=
        lt_of_le_of_ne (segment_gte_zero (f─a)) (Ne.symm hfa_nz)
      linarith [segment_symmetric g f, segment_symmetric a g]
    · exact absurd h3 hsuppose1
  · have hAFneFG : AF ≠ FG := by euclid_finish
    have hFGneAG : FG ≠ AG := by euclid_finish
    have hAGneAF : AG ≠ AF := by euclid_finish
    have hform : formTriangle a f g AF FG AG :=
      ⟨step2.1, hf_FG, hg_FG, step2.2.2.1, step2.2.1, hAFneFG, hFGneAG, hAGneAF⟩
    euclid_apply (Elements.Book1.proposition_20 a f g AF FG AG hform)
    linarith

end Elements.Book3
