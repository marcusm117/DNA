import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step3
  (d e f h : Point) (AD BF FH DE : Line)
  (hd_AD : d.onLine AD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
  (he_BF : e.onLine BF)
  (hDE_BF : DE ≠ BF)
  (hf_FH : f.onLine FH) (hh_FH : h.onLine FH)
  (hh_AD : h.onLine AD) (hf_BF : f.onLine BF)
  (hAD_BF : ¬AD.intersectsLine BF)
  (hFH_DE : ¬FH.intersectsLine DE)
  : distinctPointsOnLine f h FH ∧ ¬FH.intersectsLine DE := by
  refine ⟨⟨hf_FH, hh_FH, ?_⟩, hFH_DE⟩
  euclid_finish

end Elements.Book1
