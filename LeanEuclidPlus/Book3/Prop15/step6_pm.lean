import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagorean for m-side: |l─m|² + |e─l|² = |e─m|² (right angle at l)
-- Three cases: l=m, l=e (both trivial), l≠m∧l≠e (proposition_47).
theorem helper_3_15_step6_pm
    (m l e : Point) (ABCD : Circle) (MN : Line)
    (h_centre : e.isCentre ABCD) (hm_on : m.onCircle ABCD)
    (hm_MN : m.onLine MN) (hl_MN : l.onLine MN)
    (h_perp_mle : ∠ m:l:e = ∟) :
    |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by
  by_cases hlm : l = m
  · -- l = m: |l─m| = 0, |e─m| = |e─l|
    have h0 : |(l─m)| = 0 := zero_segment_onlyif l m hlm
    have heq : |(e─m)| = |(e─l)| := by rw [← hlm]
    nlinarith [segment_gte_zero (e─l), h0]
  · by_cases hle : l = e
    · -- l = e: |e─l| = 0, |l─m| = |e─m|
      have h0 : |(e─l)| = 0 := zero_segment_onlyif e l hle.symm
      have heq : |(l─m)| = |(e─m)| := by rw [hle]
      have h1 : |(l─m)| * |(l─m)| = |(e─m)| * |(e─m)| := by rw [heq]
      nlinarith [h0, h1]
    · -- l ≠ m and l ≠ e: all three points distinct, apply proposition_47
      have h_elm : ∠ e:l:m = ∟ := by euclid_finish
      euclid_apply (line_from_points e l) as EL
      euclid_apply (line_from_points e m) as EM
      have htri : formTriangle l e m EL EM MN := by euclid_finish
      have hp := Elements.Book1.proposition_47 l e m EL EM MN ⟨htri, h_elm⟩
      -- hp : |(e─m)| * |(e─m)| = |(e─l)| * |(e─l)| + |(l─m)| * |(l─m)|
      linarith [hp]

end Elements.Book3
