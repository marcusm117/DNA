import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: HGND as formParallelogram g n h d CN AD HF DE (g,n on CN; h,d on AD; g,h on HF;
   n,d on DE; g.sameSide h DE; CN ∥ AD; HF ∥ DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_par2 (g n h d : Point) (CN AD HF DE : Line)
    (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF)
    (hnDE : n.onLine DE) (hdDE : d.onLine DE)
    (hCNAD : ¬(CN.intersectsLine AD)) (hHFDE : ¬(HF.intersectsLine DE))
    (hghde : g.sameSide h DE) (hnd : n ≠ d) :
    formParallelogram g n h d CN AD HF DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
