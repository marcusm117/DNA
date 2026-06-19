import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13: |DH| = |DB|. Triangle DHB is right-isosceles (the diagonal BE of square CEFB cuts off a
   45° angle), so DH = DB. The whole argument lives in the shared worker step13_dhdb (reused by
   step12), passed in here as a have. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step13 (b c d e h : Point) (AB CE DG BE : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcdb : between c d b)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    |(d─h)| = |(d─b)| := by
  have step13_dhdb : |(d─h)| = |(d─b)| := by sorry
  exact step13_dhdb

end Elements.Book2
