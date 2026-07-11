import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_22_step9_tri (a c d : Point) (AC : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hdAC : ¬d.onLine AC) :
  ∠ d:a:c + ∠ a:c:d + ∠ c:d:a = ∟ + ∟ := by
  have had : a ≠ d := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points c d) as CD
  have hformTri : formTriangle a c d AC CD AD := by euclid_finish
  have hdist : distinctPointsOnLine c d CD := by euclid_finish
  obtain ⟨e', he'on, hcde'⟩ := extend_point CD c d hdist
  euclid_apply (proposition_32 a c d e' AC CD AD)
  euclid_finish

end Elements.Book3
