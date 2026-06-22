import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: CGFB as formParallelogram b f c g BE CN AB HF (b,f on BE; c,g on CN; b,c on AB;
   f,g on HF; b.sameSide c HF; BE ∥ CN; AB ∥ HF). -/
theorem helper_2_7_step3_par1 (b f c g : Point) (BE CN AB HF : Line)
    (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfHF : f.onLine HF) (hgHF : g.onLine HF)
    (hCNBE : ¬(CN.intersectsLine BE)) (hHFAB : ¬(HF.intersectsLine AB))
    (hbchk : b.sameSide c HF) (hfg : f ≠ g) :
    formParallelogram b f c g BE CN AB HF := by
  euclid_intros
  have hBECN : ¬(BE.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm BE CN); euclid_finish
  have hABHF : ¬(AB.intersectsLine HF) := by
    intro hh; euclid_apply (intersection_symm AB HF); euclid_finish
  euclid_finish

end Elements.Book2
