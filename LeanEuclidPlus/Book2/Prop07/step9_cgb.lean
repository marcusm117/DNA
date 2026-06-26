import SystemE
import Book2.Prop07.step3_bgd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.9 sub: ∠ c:g:b = ∠ g:b:c. Chain: ∠ c:g:b = ∠ a:d:b (step9_corr) = ∠ a:b:d (step9_iso). It
   remains that ∠ a:b:d = ∠ g:b:c: at vertex b the ray b→c coincides with b→a (c between a, b) and
   the ray b→d coincides with b→g (g between b, d), so ∠ a:b:d = ∠ c:b:g (equal_angles), then
   ∠ c:b:g = ∠ g:b:c by symmetry. -/
theorem helper_2_7_step9_cgb (a b c d g : Point) (AB CN AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b)
    (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hCNAD : ¬(CN.intersectsLine AD))
    (hstep5 : ∠ c:g:b = ∠ a:d:b) (hstep6 : ∠ a:d:b = ∠ a:b:d) :
    ∠ c:g:b = ∠ g:b:c := by
  euclid_intros
  have had : a ≠ d := by euclid_finish
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)))
  euclid_apply (equal_angles b a c d g AB BD)
  euclid_finish

end Elements.Book2
