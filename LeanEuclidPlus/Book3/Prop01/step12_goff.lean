import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- g ∉ AB: both g and d are equidistant from a,b; midpoint uniqueness forces g=d, contradicts h_gNd
theorem helper_3_1_step12_goff (a b d g : Point) (AB : Line)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_bet_adb : between a d b)
    (h_gNd : g ≠ d)
    (h_ad_db : |(a─d)| = |(b─d)|)
    (h_ga_gb : |(g─a)| = |(g─b)|) :
    ¬g.onLine AB := by
  intro h_gon_AB
  euclid_finish

end Elements.Book3
