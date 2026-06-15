import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: ACGH is a parallelogram, formParallelogram a c h g AB HF AD CN (a,c on AB; h,g on HF;
   a,h on AD; c,g on CN; a.sameSide h CN; AB ∥ HF; AD ∥ CN). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_paracgh (a c h g : Point) (AB HF AD CN : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hhHF : h.onLine HF) (hgHF : g.onLine HF)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (hHFAB : ¬(HF.intersectsLine AB)) (hCNAD : ¬(CN.intersectsLine AD))
    (hahcf : a.sameSide h CN) (hcg : c ≠ g) :
    formParallelogram a c h g AB HF AD CN := by
  euclid_intros
  have hADCN : ¬(AD.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm AD CN); euclid_finish
  euclid_finish

end Elements.Book2
