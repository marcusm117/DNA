import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step22_par
    (f a g h : Point) (AC GH FG AH : Line)
    (hfAC : f.onLine AC) (haAC : a.onLine AC)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hGHAC : ¬GH.intersectsLine AC) (hAHFG : ¬AH.intersectsLine FG)
    (hFGneAH : FG ≠ AH) (hah : a ≠ h) :
    formParallelogram f a g h AC GH FG AH := by
  euclid_intros
  have hACGH : ¬AC.intersectsLine GH := fun hh => hGHAC (intersection_symm AC GH hh)
  have hFGAH : ¬FG.intersectsLine AH := fun hh => hAHFG (intersection_symm FG AH hh)
  -- f, g on FG ∥ AH ⟹ f, g on the same side of AH.
  have hss : f.sameSide g AH := sameSide_of_parallel_both f g FG AH hfFG hgFG hFGneAH hFGAH
  euclid_finish

end Elements.Book2
