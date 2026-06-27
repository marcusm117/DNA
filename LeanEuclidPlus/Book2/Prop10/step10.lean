import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step10 (2.10.10): AG is a genuine line through distinct points (a ≠ g).
-- g ∈ EB, and a ∉ EB by the off-line chain rooted at ¬e0.onLine AD (mirror of Prop09 step6):
--   ¬a.onLine CE (witness e0) → ¬e.onLine AD (witness a) → ¬a.onLine EB (witness e) → a ≠ g.
set_option systemE.solverTime 30 in
theorem helper_2_10_step10
  (a b c e e0 e1 g : Point) (AD CE EB AG : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD)
  (hacb : between a c b)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hbte : between c e e1)
  (heb_b : b.onLine EB) (heb_e : e.onLine EB)
  (hg_eb : g.onLine EB)
  (hag_a : a.onLine AG) (hag_g : g.onLine AG) :
  distinctPointsOnLine a g AG := by
  have habneb : a ≠ b := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hec : e ≠ c := by euclid_finish
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c hac hce_c hce_e0 hne0
  have heoffAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c hec hab_c hab_a haoffCE
  have haoffEB : ¬(a.onLine EB) :=
    offLine_of_two_points a b e AD EB hab_a hab_b habneb heb_b heb_e heoffAD
  exact ⟨hag_a, hag_g, fun h => haoffEB (h ▸ hg_eb)⟩

end Elements.Book2
