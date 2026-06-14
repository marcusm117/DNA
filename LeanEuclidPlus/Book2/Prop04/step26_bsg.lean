import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.26 sub: b.sameSide g AD. g is between b and d on BD, and d ∈ AD with g ∉ AD; so along the
   segment d→g→b the points g and b lie on the same side of AD (pasch_2). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step26_bsg (b d g : Point) (AD BD : Line)
    (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbgd : between b g d) (hgnAD : ¬(g.onLine AD)) :
    b.sameSide g AD := by
  euclid_intros
  euclid_apply (pasch_2 d g b AD)
  euclid_finish

end Elements.Book2
