import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: ¬(c.sameSide f HK). HK separates c from f. b, d are on opposite sides of HK
   (g ∈ HK is between b and d on BD — pasch_3). c.sameSide b HK (c, b on AB ∥ HK) and
   f.sameSide d HK (f, d on DE ∥ HK), so c, f are on opposite sides of HK. The two sameSide facts
   are passed in. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step31_cfhk (b c d f g : Point) (HK BD : Line)
    (hgHK : g.onLine HK)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbgd : between b g d)
    (hcsb : c.sameSide b HK) (hfsd : f.sameSide d HK) :
    ¬(c.sameSide f HK) := by
  euclid_intros
  euclid_apply (pasch_3 b g d HK)
  euclid_finish

end Elements.Book2
