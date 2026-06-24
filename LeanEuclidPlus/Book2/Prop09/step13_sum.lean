import SystemE
import Book.Prop32
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

-- step13 helper: ∠g:e:f + ∠e:f:g = ∟. △EGF angle-sum (proposition_32) with the right
-- angle ∠e:g:f = ∟ ⟹ the other two angles sum to ∟.
theorem helper_2_9_step13_sum
  (a b c e f g : Point) (AB CE EB FG : Line)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hformTri : formTriangle e g f CE FG EB)
  (hegf : ∠ e:g:f = ∟) :
  ∠ g:e:f + ∠ e:f:g = ∟ := by
  have hgcf : g ≠ f := by euclid_finish
  have hdist : distinctPointsOnLine g f FG := ⟨hfg_g, hfg_f, hgcf⟩
  obtain ⟨d2, hd2on, hbd2⟩ := extend_point FG g f hdist
  euclid_apply (proposition_32 e g f d2 CE FG EB)
  euclid_finish

end Elements.Book2
