import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.9 sub: the square CF (= CBFG) as formParallelogram c b g f AB HF CN BE (c,b on AB; g,f on HF;
   c,g on CN; b,f on BE; c.sameSide g BE; AB ∥ HF; CN ∥ BE). -/
theorem helper_2_7_step9_parCF (c b g f : Point) (AB HF CN BE : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hgHF : g.onLine HF) (hfHF : f.onLine HF)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hHFAB : ¬(HF.intersectsLine AB)) (hCNBE : ¬(CN.intersectsLine BE))
    (hcsg : c.sameSide g BE) (hbf : b ≠ f) :
    formParallelogram c b g f AB HF CN BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
