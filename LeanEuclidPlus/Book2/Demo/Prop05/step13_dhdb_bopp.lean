import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13 sub: ¬(b.sameSide e DG) — b and e are on opposite sides of DG. d ∈ DG is between c and b
   on AB (hcdb), so c and b are on opposite sides of DG. e is on the same side of DG as c (e,c both
   on CE, and CE ∥ DG so CE does not cross DG). Hence b and e are on opposite sides. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step13_dhdb_bopp (b c d e : Point) (AB CE DG : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG)
    (hcdb : between c d b)
    (hboffDG : ¬(b.onLine DG)) (heoffDG : ¬(e.onLine DG))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(b.sameSide e DG) := by
  euclid_intros
  have hcoffDG : ¬(c.onLine DG) := by
    intro hon
    euclid_apply (intersection_lines_common_point c DG CE)
    euclid_finish
  -- c,b opposite across DG: d ∈ DG is between them on AB (pasch_3)
  have hcb_opp : ¬(c.sameSide b DG) := by
    euclid_apply (pasch_3 c d b DG)
    euclid_finish
  -- c,e same side across DG: CE ∥ DG
  have hce_ss : c.sameSide e DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing c e DG CE)
    euclid_finish
  euclid_finish

end Elements.Book2
