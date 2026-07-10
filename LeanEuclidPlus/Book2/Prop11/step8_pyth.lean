import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem helper_2_11_step8_pyth
    (a b c e : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbet_aec : between a e c)
    (hang_bac : ∠ b:a:c = ∟) :
    |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by
  have hang : ∠ e:a:b = ∟ := by euclid_finish
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_47 a e b AC EB AB)
  euclid_finish

end Elements.Book2
