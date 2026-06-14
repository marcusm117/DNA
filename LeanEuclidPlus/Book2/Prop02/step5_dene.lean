import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: DE ≠ AB. d lies on DE but not on AB (step5_doff, from the right angle
   ∠b:a:d), so the two lines differ. -/
theorem helper_2_2_step5_dene (a b c d : Point) (AB DE AD : Line)
    (hbad : ∠ b:a:d = ∟) (had : a ≠ d) (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdDE : d.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD) :
    DE ≠ AB := by
  euclid_intros
  have step5_doff : ¬(d.onLine AB) := by sorry
  euclid_finish

end Elements.Book2
