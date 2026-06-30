import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop11.step17_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step17
    (a b c d : Point) (AB CD AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hdb : d ≠ b)
    (hca_ss : c.sameSide a BD)
    (hCDAB : ¬CD.intersectsLine AB)
    (hACBD : ¬AC.intersectsLine BD)
    (hang_acd : ∠ a:c:d = ∟)
    (hac_ab : |(a─c)| = |(a─b)|) :
    Triangle.area △ a:b:d + Triangle.area △ a:c:d = |(a─b)| * |(a─b)| := by
  -- the big square ABDC is a right-angled parallelogram.
  have step17_par : formParallelogram a b c d AB CD AC BD := by euclid_apply (helper_2_11_step17_par a b c d AB CD AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)))
  have h2 : |(a─b)| * |(a─c)| = |(a─b)| * |(a─b)| := by rw [hac_ab]
  obtain ⟨h1, _⟩ := rectangle_area a b c d AB CD AC BD ⟨step17_par, hang_acd⟩
  linarith [h1, h2]

end Elements.Book2
