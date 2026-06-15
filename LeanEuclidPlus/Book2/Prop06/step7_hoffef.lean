import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: h ∉ EF. h ∈ DE; e ∈ DE ∩ EF, d ∈ DE ∩ AB. EF ≠ AB (e ∈ EF, ¬e ∈ AB) gives d ∉ EF
   (d ∈ AB ∥ EF). h ≠ e since h ∈ BG, e ∈ CE, BG ∥ CE distinct (BG ≠ CE from b ∈ BG, ¬b ∈ CE... here
   simplest: e ∈ CE, h ∈ KM∩BG; if h = e then e ∈ BG, but BG ∥ CE and e ∈ CE ⟹ e on both, BG=CE
   impossible). If h ∈ EF then h,e on EF and DE ⟹ DE = EF (h ≠ e), so d ∈ EF — contradiction. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_hoffef (b c d e h : Point) (AB DE EF CE BG : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (heEF : e.onLine EF) (hdAB : d.onLine AB)
    (heCE : e.onLine CE) (hhBG : h.onLine BG) (hbBG : b.onLine BG) (hbAB : b.onLine AB)
    (heoffAB : ¬(e.onLine AB)) (hboffCE : ¬(b.onLine CE))
    (hEFAB : ¬(EF.intersectsLine AB)) (hBGCE : ¬(BG.intersectsLine CE)) :
    ¬(h.onLine EF) := by
  intro hhEF
  have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hdoffEF : ¬(d.onLine EF) := by
    intro hdEF
    euclid_apply (intersection_lines_common_point d EF AB)
    euclid_finish
  have hhne : h ≠ e := by
    intro heq
    rw [heq] at hhBG
    euclid_apply (intersection_lines_common_point e BG CE)
    euclid_finish
  euclid_apply (two_points_determine_line h e EF DE)
  euclid_finish

end Elements.Book2
