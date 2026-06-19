import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: ¬h.onLine AB. [AFTER: library call.] h,b distinct on BE; b also on AB; witness e on BE
   off AB ⟹ offLine_of_two_points'. h≠b derived from h∈DG, b∉DG (SMT). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_bmf_hoffab (b e h : Point) (AB BE DG : Line)
    (hbAB : b.onLine AB) (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hhDG : h.onLine DG)
    (heoffAB : ¬(e.onLine AB)) (hboffDG : ¬(b.onLine DG)) :
    ¬(h.onLine AB) := by
  have hhb : h ≠ b := fun heq => hboffDG (heq ▸ hhDG)
  exact offLine_of_two_points' h b e BE AB hhBE hbBE hhb hbAB heBE heoffAB

end Elements.Book2
