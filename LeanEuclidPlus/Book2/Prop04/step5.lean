import SystemE
import Book.Prop29
import Book2.Prop04.step5_bgd
import Book2.Prop04.step5_ss
import Book2.Prop04.step5_corr
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.5: CF ∥ AD cut by transversal BD ⟹ external angle CGB = internal opposite ADB [Prop.~1.29].
   Maps to proposition_29'''' (external = interior-opposite). The parallels are CF (through g, c) and
   AD (through d, a); the transversal is BD (through b, g, d). Its preconditions — between b g d (g is
   the interior crossing of the vertical CF with the diagonal BD) and c.sameSide a BD — are supplied
   as sub-nodes; then proposition_29'''' fires and angle symmetry + collinearity close the goal. -/
theorem helper_2_4_step5 (a b c d g : Point) (AB CF AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b) (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hCFAD : ¬(CF.intersectsLine AD)) :
    ∠ c:g:b = ∠ a:d:b := by
  euclid_intros
  -- a ≠ d: the side a─d equals a─b which is positive (a ≠ b), so a─d > 0 and a ≠ d
  have had : a ≠ d := by euclid_finish
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step5_ss : c.sameSide a BD := by euclid_apply (helper_2_4_step5_ss a b c d AB BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  -- g ≠ d, from g strictly between b and d
  have hgd : g ≠ d := ((between_symm d g b (between_symm b g d step5_bgd).1).2.1).symm
  -- the corresponding-angle equality, already rewritten to the goal's orientation
  have step5_corr : ∠ c:g:b = ∠ a:d:b := by euclid_apply (helper_2_4_step5_corr a b c d g CF AD BD (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  exact step5_corr

end Elements.Book2
