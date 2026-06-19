import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: ¬(c.sameSide e KM).
   between d h g + h on KM → pasch_3 → ¬(d.sameSide g KM).
   c,d on AB ∥ KM → c.sameSide d KM (by contradiction via intersection_lines_opposing).
   g,e on EF ∥ KM → g.sameSide e KM (by contradiction via intersection_lines_opposing).
   Transitivity: ¬(c.sameSide e KM). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step15_cle_opp (c d e g h : Point) (AB EF KM : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hhKM : h.onLine KM)
    (hdhg : between d h g)
    (hKMEF : ¬(KM.intersectsLine EF))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(c.sameSide e KM) := by
  euclid_intros
  have hcoffKM : ¬(c.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point c KM AB); euclid_finish
  have hdoffKM : ¬(d.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point d KM AB); euclid_finish
  have hgoffKM : ¬(g.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point g KM EF); euclid_finish
  have heoffKM : ¬(e.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point e KM EF); euclid_finish
  euclid_apply (pasch_3 d h g KM)
  have hcdKM : c.sameSide d KM := by
    by_contra hns
    have hABneKM : AB ≠ KM := fun heq => hcoffKM (heq ▸ hcAB)
    euclid_apply (intersection_lines_opposing c d KM AB)
    euclid_finish
  have hgeKM : g.sameSide e KM := by
    by_contra hns
    have hEFneKM : EF ≠ KM := fun heq => hgoffKM (heq ▸ hgEF)
    euclid_apply (intersection_lines_opposing g e KM EF)
    euclid_finish
  euclid_finish

end Elements.Book2
