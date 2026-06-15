import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: the bottom-left square DG (= DHGN) as formParallelogram h g d n HF DE AD CN
   (h,g on HF; d,n on DE; h,d on AD; g,n on CN; h.sameSide d CN; HF ∥ DE; AD ∥ CN). This orientation
   puts the corner d (where ∠h:d:n = ∠a:d:e = ∟) in the c-slot for rectangle_area. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step11_parDG (h g d n : Point) (HF DE AD CN : Line)
    (hhHF : h.onLine HF) (hgHF : g.onLine HF)
    (hdDE : d.onLine DE) (hnDE : n.onLine DE)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (hHFDE : ¬(HF.intersectsLine DE)) (hCNAD : ¬(CN.intersectsLine AD))
    (hhsd : h.sameSide d CN) (hgn : g ≠ n) :
    formParallelogram h g d n HF DE AD CN := by
  euclid_intros
  have hADCN : ¬(AD.intersectsLine CN) := by
    intro hh; euclid_apply (intersection_symm AD CN); euclid_finish
  euclid_finish

end Elements.Book2
