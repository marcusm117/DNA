import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: between c l e (l = KM ∩ CE, c on AB below KM, e on EF above KM).
   Combine: pasch_4 c l e KM CE once ¬(c.sameSide e KM) is established by step15_cle_opp.
   Off-line facts (hcoffKM, heoffKM, hloffDG) pre-derived in parent step15. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step15_cle (c d e g h l : Point) (AB CE DG EF KM : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG) (hhDG : h.onLine DG)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hdhg : between d h g)
    (hKMEF : ¬(KM.intersectsLine EF))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE))
    (hcoffKM : ¬(c.onLine KM))
    (heoffKM : ¬(e.onLine KM))
    (hloffDG : ¬(l.onLine DG)) :
    between c l e := by
  euclid_intros
  have step15_cle_opp : ¬(c.sameSide e KM) := by sorry
  have hKMneCE : KM ≠ CE := fun heq => hcoffKM (heq ▸ hcCE)
  have hlh : l ≠ h := fun heq => hloffDG (heq ▸ hhDG)
  have hcl : c ≠ l := fun heq => hcoffKM (heq ▸ hlKM)
  have hel : e ≠ l := fun heq => heoffKM (heq ▸ hlKM)
  euclid_apply (pasch_4 c l e KM CE)
  euclid_finish

end Elements.Book2
