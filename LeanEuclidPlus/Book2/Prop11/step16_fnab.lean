import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step16_fnab
    (a b c f : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbAC : ¬b.onLine AC)
    (hbet_caf : between c a f) :
    ¬f.onLine AB := by
  have hfa : f ≠ a := by euclid_finish
  -- b is off AC (given), so AC, AB share only a ⟹ f (on AC, ≠ a) is off AB.
  exact offLine_of_two_points f a b AC AB hfAC haAC hfa haAB hbAB hbAC

end Elements.Book2
