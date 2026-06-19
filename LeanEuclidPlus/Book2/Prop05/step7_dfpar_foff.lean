import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- f∉DG: f∈BF; DG≠BF; ¬(DG.intersectsLine BF) → offLine_of_parallel_simple' (C₀′). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_foff (f : Point) (BF DG : Line)
    (hfBF : f.onLine BF)
    (hDGneBF : DG ≠ BF)
    (hDGBF : ¬(DG.intersectsLine BF)) :
    ¬(f.onLine DG) := by
  euclid_apply (offLine_of_parallel_simple' f BF DG (by assumption) (by assumption) (by assumption))
  assumption

end Elements.Book2
