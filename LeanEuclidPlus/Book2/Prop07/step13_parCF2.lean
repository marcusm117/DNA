import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the square CF (= CBFG) as formParallelogram c g b f CN BE AB HF (c,g on CN; b,f on BE;
   c,b on AB; g,f on HF; c.sameSide b HF; CN ∥ BE; AB ∥ HF). This orientation puts the corner b
   (where ∠c:b:f = ∠a:b:e = ∟) in the c-slot for rectangle_area. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_parCF2 (c g b f : Point) (CN BE AB HF : Line)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hgHF : g.onLine HF) (hfHF : f.onLine HF)
    (hCNBE : ¬(CN.intersectsLine BE)) (hHFAB : ¬(HF.intersectsLine AB))
    (hcsb : c.sameSide b HF) (hgf : g ≠ f) :
    formParallelogram c g b f CN BE AB HF := by
  euclid_intros
  have hABHF : ¬(AB.intersectsLine HF) := by
    intro hh; euclid_apply (intersection_symm AB HF); euclid_finish
  euclid_finish

end Elements.Book2
