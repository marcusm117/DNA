import SystemE
import Book.Prop32
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step13 (2.10.13): ∠EAC and ∠AEC are each half a right-angle [Prop.~1.32].
-- proposition_32 gives the triangle angle-sum ∠EAC + ∠ACE + ∠CEA = 2∟; with the right angle
-- ∠ACE=∟ (step1/step12) and the base-angle equality ∠EAC=∠AEC (step11), linarith halves each.
theorem helper_2_10_step13
  (a b c e e0 e1 : Point) (AD EA CE : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hstep1 : ∠ a:c:e = ∟)
  (heq : ∠ e:a:c = ∠ a:e:c) :
  ∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2 := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hCEneAD : CE ≠ AD := fun h => hne0 (h ▸ hce_e0)
  have hformTri : formTriangle e a c EA AD CE := by euclid_finish
  have hsum : ∠ e:a:c + ∠ a:c:e + ∠ c:e:a = ∟ + ∟ := by
    euclid_apply (proposition_32 e a c b EA AD CE)
    euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hae : e ≠ a := by euclid_finish
  have hsym : ∠ c:e:a = ∠ a:e:c := angle_symm c e a ⟨hce, hae⟩
  refine ⟨by linarith, by linarith⟩

end Elements.Book2
