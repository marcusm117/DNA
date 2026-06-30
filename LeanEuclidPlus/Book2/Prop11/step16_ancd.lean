import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step16_ancd
    (a b c d e : Point) (AC CD : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hang_acd : ∠ a:c:d = ∟)
    (hbet_aec : between a e c)
    (hab : a ≠ b) (hcd_ab : |(c─d)| = |(a─b)|) :
    ¬a.onLine CD := by
  have hca : c ≠ a := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hang : ∠ d:c:a = ∟ := by euclid_finish
  exact offLine_of_right_angle c d a CD hcCD hdCD hcd hca hang

end Elements.Book2
