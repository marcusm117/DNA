import SystemE
import Book3.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_4_step7
    (b d f e : Point) (ABCD : Circle) (BD FE : Line)
    (hbcirc : b.onCircle ABCD)
    (hdcirc : d.onCircle ABCD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hbd : b ≠ d)
    (hCentre : f.isCentre ABCD)
    (hfFE : f.onLine FE) (hnfBD : ¬f.onLine BD)
    (hbet : between b e d)
    (heFE : e.onLine FE)
    (hassump1 : |(b─e)| = |(e─d)|) :
    ∠ f:e:b = ∟ := by
  have hdp : distinctPointsOnLine b d BD := ⟨hbBD, hdBD, hbd⟩
  have heBD : e.onLine BD := by euclid_finish
  have h : (|(b─e)| = |(e─d)| → ∠ b:e:f = ∟) ∧ (∠ b:e:f = ∟ → |(b─e)| = |(e─d)|) := by
    euclid_apply (proposition_3 b d f e ABCD BD FE ⟨hbcirc, hdcirc, hdp, hCentre, hfFE, hnfBD, heBD, heFE, hbet⟩)
  have hangle : ∠ b:e:f = ∟ := h.1 hassump1
  have hef : e ≠ f := by euclid_finish
  have heb : b ≠ e := by euclid_finish
  exact (angle_symm b e f ⟨heb, hef⟩).symm.trans hangle

end Elements.Book3
