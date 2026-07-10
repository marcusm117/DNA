import SystemE
import Book1Variants.Prop05
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step11 (2.10.11): in isosceles △AEC (AC = CE), base angles ∠EAC = ∠AEC [Prop.~1.5].
-- proposition_5 needs a produced point beyond each base vertex (e1 beyond E; d' beyond A).
-- formTriangle needs CE≠AD + off-line facts, from the ¬e0.onLine AD anchor (library lemmas).
theorem helper_2_10_step11
  (a b c e e0 e1 : Point) (AD EA CE : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD)
  (hea_a : a.onLine EA) (hea_e : e.onLine EA)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hce_ac : |(c─e)| = |(a─c)|) :
  ∠ e:a:c = ∠ a:e:c := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c (by euclid_finish) hab_c hab_a haoffCE
  have hCEneAD : CE ≠ AD := fun h => hne0 (h ▸ hce_e0)
  have hformTri : formTriangle c a e AD EA CE := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hdist : distinctPointsOnLine c a AD := ⟨hab_c, hab_a, hca⟩
  obtain ⟨d', hd'on, hbd⟩ := extend_point AD c a hdist
  have h1 : ∠ c:a:e = ∠ c:e:a := by
    euclid_apply (proposition_5 c a e d' e1 AD EA CE)
    euclid_finish
  euclid_finish

end Elements.Book2
