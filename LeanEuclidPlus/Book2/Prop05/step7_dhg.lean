import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: between d h g (h = DG ∩ KM, d = DG ∩ AB, g = DG ∩ EF).
   Separator = KM. Chain: pasch_3 c d b DG → e.sameSide c DG → ¬(b.sameSide e DG)
   → pasch_4 b h e DG BE → between b h e → pasch_3 b h e KM → ¬(b.sameSide e KM)
   → d.sameSide b KM (AB ∥ KM) → g.sameSide e KM (EF ∥ KM) → pasch_4 d h g KM DG. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dhg (b c d e g h : Point) (AB BE CE DG EF KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hhKM : h.onLine KM)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hKMEF : ¬(KM.intersectsLine EF))
    (hEFAB : ¬(EF.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE))
    (heoffDG : ¬(e.onLine DG))
    (hboffDG : ¬(b.onLine DG))
    (hdoffKM : ¬(d.onLine KM))
    (hboffKM : ¬(b.onLine KM))
    (hgoffKM : ¬(g.onLine KM))
    (hcdb : between c d b) :
    between d h g := by
  euclid_intros
  -- c, b on opposite sides of DG (d between them, d on DG)
  euclid_apply (pasch_3 c d b DG)
  -- e, c on same side of DG (both on CE ∥ DG)
  have hcoff : ¬(c.onLine DG) := by
    intro hcon
    have hne : DG ≠ CE := fun heq => heoffDG (heq ▸ heCE)
    euclid_apply (intersection_lines_common_point c DG CE)
    euclid_finish
  have hecs : e.sameSide c DG := by
    by_contra hns
    have hne : DG ≠ CE := fun heq => heoffDG (heq ▸ heCE)
    euclid_apply (intersection_lines_opposing e c DG CE)
    euclid_finish
  -- between b h e (b, e opp sides of DG; h = DG ∩ BE)
  have hDGneBE : DG ≠ BE := fun heq => heoffDG (heq ▸ heBE)
  have hbh : b ≠ h := fun heq => hboffDG (heq ▸ hhDG)
  have heh : e ≠ h := fun heq => heoffDG (heq ▸ hhDG)
  have step7_bhe : between b h e := by
    euclid_apply (pasch_4 b h e DG BE)
    euclid_finish
  -- b, e on opposite sides of KM (h between b,e on BE, h on KM)
  euclid_apply (pasch_3 b h e KM)
  -- d, b on same side of KM (both on AB ∥ KM)
  have hKMneAB : KM ≠ AB := fun heq => hdoffKM (heq ▸ hdAB)
  have step7_dsb : d.sameSide b KM := by
    by_contra hns
    euclid_apply (intersection_lines_opposing d b KM AB)
    euclid_finish
  -- g, e on same side of KM (both on EF ∥ KM)
  have heoffKM : ¬(e.onLine KM) := by
    intro heon
    have hne : KM ≠ EF := fun heq => hgoffKM (heq ▸ hgEF)
    euclid_apply (intersection_lines_common_point e KM EF)
    euclid_finish
  have hKMneEF : KM ≠ EF := fun heq => hgoffKM (heq ▸ hgEF)
  have step7_gse : g.sameSide e KM := by
    by_contra hns
    euclid_apply (intersection_lines_opposing g e KM EF)
    euclid_finish
  -- ¬(d.sameSide g KM) then pasch_4
  have step7_opp : ¬(d.sameSide g KM) := by euclid_finish
  have hKMneDG : KM ≠ DG := fun heq => hdoffKM (heq ▸ hdDG)
  have hdh : d ≠ h := fun heq => hdoffKM (heq ▸ hhKM)
  have hgh : g ≠ h := fun heq => hgoffKM (heq ▸ hhKM)
  euclid_apply (pasch_4 d h g KM DG)
  euclid_finish

end Elements.Book2
