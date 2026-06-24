import SystemE
import Book.Prop05
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step7 (2.9.7): in isoceles △AEC (AC = CE), the base angles at A and E are equal.
-- proposition_5 needs a produced point beyond each base vertex (e1 beyond E; d'
-- beyond A via extend_point). formTriangle needs CE≠AB and the off-CE / off-AB
-- facts, which come from the ¬e0.onLine AB anchor (library lemmas, zero SMT).
theorem helper_2_9_step7
  (a b c e e0 e1 : Point) (AB EA CE : Line)
  (hab_a : a.onLine AB) (hab_c : c.onLine AB)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hce_ac : |(c─e)| = |(a─c)|) :
  ∠ e:a:c = ∠ a:e:c := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hCEneAB : CE ≠ AB := fun h => hne0 (h ▸ hce_e0)
  have hformTri : formTriangle c a e AB EA CE := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hdist : distinctPointsOnLine c a AB := ⟨hab_c, hab_a, hca⟩
  obtain ⟨d', hd'on, hbd⟩ := extend_point AB c a hdist
  have h1 : ∠ c:a:e = ∠ c:e:a := by
    euclid_apply (proposition_5 c a e d' e1 AB EA CE)
    euclid_finish
  euclid_finish

end Elements.Book2
