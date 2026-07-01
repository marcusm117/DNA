import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- d.sameSide c₀ BE : d and c₀ are the two ends of the rectangle side DC, which is parallel to BE
-- (¬BE.intersectsLine DC), so they lie on the same side of BE. DC ≠ BE because e ∈ BE but e ∉ DC
-- (e.sameSide b₀ DC puts e off DC).
theorem helper_2_14_step14_ss (d c₀ e b₀ : Point) (DC BE : Line)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC)
    (h_eBE : e.onLine BE)
    (h_esb0 : e.sameSide b₀ DC)
    (h_par2 : ¬BE.intersectsLine DC) :
    d.sameSide c₀ BE := by
  have hpar : ¬(DC.intersectsLine BE) := by euclid_finish
  have hne : DC ≠ BE := by euclid_finish
  exact sameSide_of_parallel_both d c₀ DC BE h_dDC h_c0DC hne hpar

end Elements.Book2
