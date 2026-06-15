import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: ¬c.sameSide d BG. On line AB the order is a, c, b, d (between a c b, between a b d), so
   between c b d; b lies on BG, so by pasch_3 c and d are on opposite sides of BG. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_cnsdBG (a b c d : Point) (AB BG : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hbBG : b.onLine BG)
    (hacb : between a c b) (habd : between a b d) :
    ¬(c.sameSide d BG) := by
  euclid_intros
  have hcbd : between c b d := by euclid_finish
  euclid_apply (pasch_3 c b d BG)
  euclid_finish

end Elements.Book2
