import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: between l h m (l = KM∩CE, h = KM∩DG∩BE, m = KM∩BF).
   Separator = DG (h is on DG, not CE). The off-line witnesses needed for
   same-side reasoning are extracted from hcmpar and hdfpar:
   * hcmpar.c.sameSide.l.BF → ¬(c.onLine BF) → CE ≠ BF
   * hdfpar.d.sameSide.b.EF → ¬(d.onLine EF) → EF ≠ AB (breaks the distinctness cascade)
   * hdfpar.¬(DG.intersectsLine BF) directly (no prop_30 needed).
   Chain: pasch_3 c d b DG → ¬(c.sameSide b DG);
   l.sameSide c DG (CE ∥ DG); m.sameSide b DG (BF ∥ DG from hdfpar);
   ¬(l.sameSide m DG) → pasch_4 l h m DG KM. -/
theorem helper_2_5_step7_lhm (b c d e f g h l m : Point) (AB BF BE EF CE DG KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hmBF : m.onLine BF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG) (hhDG : h.onLine DG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hKMAB : ¬(KM.intersectsLine AB)) (hEFAB : ¬(EF.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) (hDGCE : ¬(DG.intersectsLine CE))
    (hcmpar : formParallelogram c b l m AB KM CE BF)
    (hdfpar : formParallelogram d g b f DG BF AB EF)
    (hcdb : between c d b) :
    between l h m := by
  euclid_intros
  -- From hcmpar: c.sameSide l BF → ¬(c.onLine BF)
  have hcoffBF : ¬(c.onLine BF) := by
    euclid_apply (same_side_not_on_line c l BF)
    euclid_finish
  -- From hdfpar: d.sameSide b EF → ¬(d.onLine EF) → EF ≠ AB (breaks the cascade)
  have hdoffEF : ¬(d.onLine EF) := by
    euclid_apply (same_side_not_on_line d b EF)
    euclid_finish
  have hEFneAB : EF ≠ AB := fun heq => hdoffEF (heq ▸ hdAB)
  -- CE ≠ BF (from c off BF and c on CE)
  have hCEneBF : CE ≠ BF := fun heq => hcoffBF (heq ▸ hcCE)
  -- ¬(DG.intersectsLine BF) directly from hdfpar
  have hDGBF : ¬(DG.intersectsLine BF) := by euclid_finish
  -- ¬(d.onLine CE): if d on CE then c,d distinct on CE∩AB → CE=AB → e on AB+EF → EF∩AB
  have hdoffCE : ¬(d.onLine CE) := by
    intro hcon
    have hcd : c ≠ d := by euclid_finish
    have hCEeqAB : CE = AB := by
      euclid_apply (two_points_determine_line c d CE AB); euclid_finish
    exact hEFAB (by
      have heAB : e.onLine AB := hCEeqAB ▸ heCE
      euclid_apply (intersection_lines_common_point e EF AB); euclid_finish)
  -- DG ≠ CE
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  -- DG ≠ BF: if DG=BF then d,b distinct on DG∩AB → DG=AB → g on AB+EF → EF∩AB
  have hDGneBF : DG ≠ BF := by
    intro heq
    have hbDG : b.onLine DG := heq ▸ hbBF
    have hdb : d ≠ b := by euclid_finish
    have hDGeqAB : DG = AB := by
      euclid_apply (two_points_determine_line d b DG AB); euclid_finish
    exact hEFAB (by
      have hgAB : g.onLine AB := hDGeqAB ▸ hgDG
      euclid_apply (intersection_lines_common_point g EF AB); euclid_finish)
  -- Off-line: c and l off DG (for l.sameSide c DG)
  have hcoffDG : ¬(c.onLine DG) := by
    intro hcon
    exact hDGCE (by euclid_apply (intersection_lines_common_point c DG CE); euclid_finish)
  have hloffDG : ¬(l.onLine DG) := by
    intro hcon
    exact hDGCE (by euclid_apply (intersection_lines_common_point l DG CE); euclid_finish)
  -- Off-line: m and b off DG (for m.sameSide b DG)
  have hmoffDG : ¬(m.onLine DG) := by
    intro hcon
    exact hDGBF (by euclid_apply (intersection_lines_common_point m DG BF); euclid_finish)
  have hboffDG : ¬(b.onLine DG) := by
    intro hcon
    exact hDGBF (by euclid_apply (intersection_lines_common_point b DG BF); euclid_finish)
  -- ¬(c.sameSide b DG): d between c and b, d on DG
  euclid_apply (pasch_3 c d b DG)
  -- l.sameSide c DG: l and c both on CE; CE ∥ DG
  have hlcs : l.sameSide c DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing l c DG CE)
    euclid_finish
  -- m.sameSide b DG: m and b both on BF; BF ∥ DG
  have hmbs : m.sameSide b DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing m b DG BF)
    euclid_finish
  -- l and m on opposite sides of DG
  have step7_lhm_opp : ¬(l.sameSide m DG) := by euclid_finish
  -- Distinctness for pasch_4 l h m DG KM
  have hDGneKM : DG ≠ KM := fun heq => hloffDG (heq ▸ hlKM)
  have hlh : l ≠ h := fun heq => hloffDG (heq ▸ hhDG)
  have hmh : m ≠ h := fun heq => hmoffDG (heq ▸ hhDG)
  have hlm : l ≠ m := by euclid_finish
  euclid_apply (pasch_4 l h m DG KM)
  euclid_finish

end Elements.Book2