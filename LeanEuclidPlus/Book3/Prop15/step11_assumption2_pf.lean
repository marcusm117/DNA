import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_pf
    (k f e : Point) (ABCD : Circle) (FG : Line)
    (h_centre : e.isCentre ABCD) (hf_on : f.onCircle ABCD)
    (hf_FG : f.onLine FG) (hk_FG : k.onLine FG)
    (h_perp : ∠ e:k:f = ∟) :
    |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)| := by
  by_cases hkf : k = f
  · have h0 : |(k─f)| = 0 := zero_segment_onlyif k f hkf
    have heq : |(e─f)| = |(e─k)| := by rw [← hkf]
    nlinarith [segment_gte_zero (e─k), h0]
  · by_cases hke : k = e
    · have h0 : |(e─k)| = 0 := zero_segment_onlyif e k hke.symm
      have heq : |(k─f)| = |(e─f)| := by rw [hke]
      have h1 : |(k─f)| * |(k─f)| = |(e─f)| * |(e─f)| := by rw [heq]
      nlinarith [h0, h1]
    · -- right angle at k: ∠e:k:f = ∟, so apply prop47 at vertex k
      have h_ekf : ∠ e:k:f = ∟ := h_perp
      euclid_apply (line_from_points e k) as EK2
      euclid_apply (line_from_points e f) as EF2
      have htri : formTriangle k e f EK2 EF2 FG := by euclid_finish
      have hp := Elements.Book1.proposition_47 k e f EK2 EF2 FG ⟨htri, h_ekf⟩
      linarith [hp]

end Elements.Book3
