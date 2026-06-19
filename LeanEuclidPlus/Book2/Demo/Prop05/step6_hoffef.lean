import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h ∉ EF. [AFTER: library call.] h,e distinct on BE; e also on EF; witness b on BE off EF
   ⟹ offLine_of_two_points'. h≠e derived from h∈DG, e∉DG (SMT). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_hoffef (b e h : Point) (BE EF DG : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hhDG : h.onLine DG)
    (hboffEF : ¬(b.onLine EF)) (heoffDG : ¬(e.onLine DG)) :
    ¬(h.onLine EF) := by
  have hhe : h ≠ e := fun heq => heoffDG (heq ▸ hhDG)
  exact offLine_of_two_points' h e b BE EF hhBE heBE hhe heEF hbBE hboffEF

end Elements.Book2
