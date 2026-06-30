import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step16_fncd
    (a b c d f : Point) (AC CD : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hang_acd : ∠ a:c:d = ∟)
    (hbet_caf : between c a f)
    (hab : a ≠ b) (hcd_ab : |(c─d)| = |(a─b)|) :
    ¬f.onLine CD := by
  have hca : c ≠ a := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hfc : f ≠ c := by euclid_finish
  -- d is off AC (right angle at c), so AC, CD share only c ⟹ f (on AC, ≠ c) is off CD.
  have hdnAC : ¬d.onLine AC := offLine_of_right_angle c a d AC hcAC haAC hca hcd hang_acd
  exact offLine_of_two_points f c d AC CD hfAC hcAC hfc hcCD hdCD hdnAC

end Elements.Book2
