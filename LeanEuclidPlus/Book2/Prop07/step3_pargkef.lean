import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: GFEN as formParallelogram g f n e HF DE CN BE (g,f on HF; n,e on DE; g,n on CN;
   f,e on BE; g.sameSide n BE; HF ∥ DE; CN ∥ BE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_pargkef (g f n e : Point) (HF DE CN BE : Line)
    (hgHF : g.onLine HF) (hfHF : f.onLine HF)
    (hnDE : n.onLine DE) (heDE : e.onLine DE)
    (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (hfBE : f.onLine BE) (heBE : e.onLine BE)
    (hHFDE : ¬(HF.intersectsLine DE)) (hCNBE : ¬(CN.intersectsLine BE))
    (hgfbe : g.sameSide n BE) (hke : f ≠ e) :
    formParallelogram g f n e HF DE CN BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
