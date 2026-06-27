import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step3 (2.10.3): EA and EB are genuine lines through distinct points.
-- e≠a, e≠b: e lies on the perpendicular CE; a,b lie on AD and (being ≠ c, with
-- e0 ∈ CE \ AD forcing CE≠AD) are off CE. The off-CE facts come from the shared
-- offLine_of_two_points lemma (witness e0); e.onLine CE from between.
theorem helper_2_10_step3
  (a b c e e0 e1 : Point) (AD CE EA EB : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD)
  (habt : between a c b)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hbte : between c e e1)
  (hEA_e : e.onLine EA) (hEA_a : a.onLine EA)
  (hEB_e : e.onLine EB) (hEB_b : b.onLine EB) :
  distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hac : a ≠ c := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have haoff : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c hac hce_c hce_e0 hne0
  have hboff : ¬(b.onLine CE) :=
    offLine_of_two_points b c e0 AD CE hab_b hab_c hbc hce_c hce_e0 hne0
  refine ⟨⟨hEA_e, hEA_a, ?_⟩, ⟨hEB_e, hEB_b, ?_⟩⟩
  · exact fun h => haoff (h ▸ heCE)
  · exact fun h => hboff (h ▸ heCE)

end Elements.Book2
