import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.11 sub: between c l e (l = KM ∩ CE; c on AB above KM, e on EF below KM). c, e lie on opposite
   sides of KM: c is on AB ∥ KM (same side as d), e is opposite d across KM (step7_dnse), so c and e are
   opposite. pasch_4 on c, l, e across KM and CE then gives between c l e. Off-line anchors
   (c, e ∉ KM) derived in-body from KM ≠ AB, KM ≠ EF. -/
theorem helper_2_6_step11_cle (c d e h l : Point) (AB CE EF KM : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (heEF : e.onLine EF)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hdnse : ¬(d.sameSide e KM))
    (hhoffAB : ¬(h.onLine AB)) (hhoffEF : ¬(h.onLine EF))
    (hKMAB : ¬(KM.intersectsLine AB)) (hKMEF : ¬(KM.intersectsLine EF)) :
    between c l e := by
  euclid_intros
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  have hcoffKM : ¬(c.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point c KM AB); euclid_finish
  have hdoffKM : ¬(d.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point d KM AB); euclid_finish
  have heoffKM : ¬(e.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point e KM EF); euclid_finish
  -- c.sameSide d KM (both on AB ∥ KM)
  have hcd_ss : c.sameSide d KM := by
    by_contra hns; euclid_apply (intersection_lines_opposing c d KM AB); euclid_finish
  -- ¬c.sameSide e KM (c same side as d, d opposite e)
  have hcnse : ¬(c.sameSide e KM) := by euclid_finish
  have hKMneCE : KM ≠ CE := fun heq => hcoffKM (heq ▸ hcCE)
  have hcl : c ≠ l := fun heq => hcoffKM (heq ▸ hlKM)
  have hel : e ≠ l := fun heq => heoffKM (heq ▸ hlKM)
  euclid_apply (pasch_4 c l e KM CE)
  euclid_finish

end Elements.Book2
