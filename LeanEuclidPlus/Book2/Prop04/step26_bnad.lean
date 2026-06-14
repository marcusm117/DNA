import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.26 sub: b ∉ AD. a, b lie on AB; if b ∈ AD then a, b are two common points of AB and AD, so
   AB = AD, putting d on AB and making a, b, d collinear with ∠ b:a:d = ∟ — impossible. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step26_bnad (a b c d : Point) (AB AD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (had : a ≠ d) (hbad : ∠ b:a:d = ∟) :
    ¬(b.onLine AD) := by
  intro hbAD
  have hABAD : AB = AD := by
    euclid_apply (two_points_determine_line a b AB AD)
    euclid_finish
  rw [hABAD] at hbAB
  -- a, b, d collinear on AD with ∠ b:a:d = ∟ is impossible
  euclid_finish

end Elements.Book2
