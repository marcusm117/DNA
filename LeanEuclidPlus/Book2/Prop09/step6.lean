import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step6 (2.9.6): AF is a genuine line through distinct points (a ≠ f).
-- Off-line chain rooted at the cheap anchor ¬e0.onLine AB:
--   ¬a.onLine CE   (witness e0 ∈ CE \ AB)
--   ¬e.onLine AB   (witness a ∈ AB \ CE)
--   ¬a.onLine EB   (a,b ∈ AB, a≠b, witness e ∈ EB \ AB)
--   a ≠ f          (f ∈ EB, a ∉ EB)
theorem helper_2_9_step6
  (a b c e e0 e1 f : Point) (AB CE EB AF : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (habneb : a ≠ b)
  (hacb : between a c b)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (heb_b : b.onLine EB) (heb_e : e.onLine EB)
  (hf_eb : f.onLine EB)
  (haf_a : a.onLine AF) (haf_f : f.onLine AF) :
  distinctPointsOnLine a f AF := by
  have hac : a ≠ c := by euclid_finish
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hec : e ≠ c := by euclid_finish
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c hac hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c hec hab_c hab_a haoffCE
  have haoffEB : ¬(a.onLine EB) :=
    offLine_of_two_points a b e AB EB hab_a hab_b habneb heb_b heb_e heoffAB
  exact ⟨haf_a, haf_f, fun h => haoffEB (h ▸ hf_eb)⟩

end Elements.Book2
