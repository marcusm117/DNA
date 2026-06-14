import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.7: ∠ c:g:b = ∠ g:b:c. Chain: ∠ c:g:b = ∠ a:d:b (step5) = ∠ a:b:d (step6). It remains that
   ∠ a:b:d = ∠ g:b:c: at vertex b the ray b→c coincides with b→a (c is between a and b on AB) and
   the ray b→d coincides with b→g (g is between b and d on BD, supplied by the shared step5_bgd),
   so ∠ a:b:d = ∠ c:b:g (equal_angles), then ∠ c:b:g = ∠ g:b:c by symmetry. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step7 (a b c d g : Point) (AB CF AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b)
    (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hCFAD : ¬(CF.intersectsLine AD))
    (hstep5 : ∠ c:g:b = ∠ a:d:b) (hstep6 : ∠ a:d:b = ∠ a:b:d) :
    ∠ c:g:b = ∠ g:b:c := by
  euclid_intros
  -- a ≠ d (side a─d = a─b > 0)
  have had : a ≠ d := by euclid_finish
  -- g is between b and d on the diagonal (shared with step5)
  have step5_bgd : between b g d := by sorry
  -- ∠ a:b:d = ∠ c:b:g: rays b→a = b→c (c between a,b) and b→d = b→g (g between b,d)
  euclid_apply (equal_angles b a c d g AB BD)
  euclid_finish

end Elements.Book2
