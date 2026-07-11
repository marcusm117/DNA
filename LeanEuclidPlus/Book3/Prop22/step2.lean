import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_22_step2 (a b c : Point) (AC : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)   -- "the three angles of any triangle are equal to two right-angles"
  : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟ := by
  have hab : a ≠ b := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  have hformTri : formTriangle a b c AB BC AC := by euclid_finish
  have hdist : distinctPointsOnLine b c BC := by euclid_finish
  obtain ⟨d', hd'on, hbcd'⟩ := extend_point BC b c hdist
  euclid_apply (proposition_32 a b c d' AB BC AC)
  euclid_finish

end Elements.Book3
