import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step21_rangle
    (a b d h : Point) (AB BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hhAB : h.onLine AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hdb : d ≠ b)
    (hbet_ahb : between a h b) (hang_abd : ∠ a:b:d = ∟) :
    ∠ d:b:h = ∟ := by
  -- h on ray b→a (between a h b), so ∠h:b:d = ∠a:b:d = ∟; angle_symm gives ∠d:b:h.
  have hbh : b ≠ h := by euclid_finish
  have hs : ∠ d:b:h = ∠ h:b:d := angle_symm d b h ⟨hdb, hbh⟩
  rw [hs]
  euclid_apply (equal_angles b h a d d AB BD)
  linarith [hang_abd]

end Elements.Book2
