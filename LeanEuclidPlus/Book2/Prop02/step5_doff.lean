import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: ¬(d.onLine AB). If d were on AB with a, b, then b,a,d would be collinear and
   the angle ∠b:a:d would be 0 or 2∟ (degenerate), contradicting ∠b:a:d = ∟. -/
theorem helper_2_2_step5_doff (a b c d : Point) (AB : Line)
    (hbad : ∠ b:a:d = ∟) (hacb : between a c b) (had : a ≠ d)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) :
    ¬(d.onLine AB) := by
  euclid_intros
  by_contra hcon
  by_cases hbet : between b a d
  · euclid_apply (flat_angle_onlyif b a d)
    euclid_finish
  · euclid_apply (degenerated_angle_if a b d AB)
    euclid_finish

end Elements.Book2
