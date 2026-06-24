import SystemE
import Book.Prop32
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

-- step16 helper: ∠f:b:d + ∠b:f:d = ∟. △BFD angle-sum (proposition_32) with the right
-- angle ∠f:d:b = ∟ ⟹ the other two angles sum to ∟.
theorem helper_2_9_step16_sum
  (a b c d e f : Point) (AB CE DF EB : Line)
  (heb_b : b.onLine EB) (heb_f : f.onLine EB)
  (hdf_f : f.onLine DF) (hdf_d : d.onLine DF)
  (hformTri : formTriangle b f d EB DF AB)
  (hFDB : ∠ f:d:b = ∟) :
  ∠ f:b:d + ∠ b:f:d = ∟ := by
  have hfd : f ≠ d := by euclid_finish
  have hdist : distinctPointsOnLine f d DF := ⟨hdf_f, hdf_d, hfd⟩
  obtain ⟨d2, hd2on, hbd2⟩ := extend_point DF f d hdist
  euclid_apply (proposition_32 b f d d2 EB DF AB)
  euclid_finish

end Elements.Book2
