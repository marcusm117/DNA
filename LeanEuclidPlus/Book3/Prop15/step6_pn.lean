import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagorean for n-side: |l─n|² + |e─l|² = |e─m|² (right angle at l, n-direction)
-- Three cases: l=n, l=e (trivial), l≠n∧l≠e (proposition_47 + equal radii).
theorem helper_3_15_step6_pn
    (m n l e : Point) (ABCD : Circle) (MN : Line)
    (h_centre : e.isCentre ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (h_perp_mle : ∠ m:l:e = ∟)
    (hbetw_mln : between m l n) :
    |(l─n)| * |(l─n)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by
  have h_rad : |(e─n)| = |(e─m)| := by euclid_finish
  have h_rad_sq : |(e─n)| * |(e─n)| = |(e─m)| * |(e─m)| := by rw [h_rad]
  by_cases hln : l = n
  · -- l = n: |l─n| = 0, |e─n| = |e─l|
    have h0 : |(l─n)| = 0 := zero_segment_onlyif l n hln
    have heq : |(e─n)| = |(e─l)| := by rw [← hln]
    have h_el_em : |(e─l)| = |(e─m)| := by linarith [heq, h_rad]
    have h_el_sq : |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by rw [h_el_em]
    have h0_sq : |(l─n)| * |(l─n)| = 0 := by nlinarith [h0, segment_gte_zero (l─n)]
    linarith [h0_sq, h_el_sq]
  · by_cases hle : l = e
    · -- l = e: |e─l| = 0, |l─n| = |e─n|
      have h0 : |(e─l)| = 0 := zero_segment_onlyif e l hle.symm
      have heq : |(l─n)| = |(e─n)| := by rw [hle]
      have h1 : |(l─n)| * |(l─n)| = |(e─n)| * |(e─n)| := by rw [heq]
      have h0_sq : |(e─l)| * |(e─l)| = 0 := by nlinarith [h0, segment_gte_zero (e─l)]
      linarith [h1, h_rad_sq, h0_sq]
    · -- l ≠ n and l ≠ e: apply proposition_47 then use equal radii
      have h_eln : ∠ e:l:n = ∟ := by euclid_finish
      euclid_apply (line_from_points e l) as EL
      euclid_apply (line_from_points e n) as EN
      have htri : formTriangle l e n EL EN MN := by euclid_finish
      have hp := Elements.Book1.proposition_47 l e n EL EN MN ⟨htri, h_eln⟩
      -- hp : |(e─n)| * |(e─n)| = |(e─l)| * |(e─l)| + |(l─n)| * |(l─n)|
      linarith [hp, h_rad_sq]

end Elements.Book3
