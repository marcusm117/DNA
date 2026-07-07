import SystemE
import Book3.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_4_step5
    (a c f e : Point) (ABCD : Circle) (AC FE : Line)
    (hacirc : a.onCircle ABCD)
    (hccirc : c.onCircle ABCD)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hCentre : f.isCentre ABCD)
    (hfFE : f.onLine FE) (hnfAC : ¬f.onLine AC)
    (hbet : between a e c)
    (heFE : e.onLine FE)
    (hassump1 : |(a─e)| = |(e─c)|) :
    ∠ f:e:a = ∟ := by
  have hdp : distinctPointsOnLine a c AC := ⟨haAC, hcAC, hac⟩
  have heAC : e.onLine AC := by euclid_finish
  have h : (|(a─e)| = |(e─c)| → ∠ a:e:f = ∟) ∧ (∠ a:e:f = ∟ → |(a─e)| = |(e─c)|) := by
    euclid_apply (proposition_3 a c f e ABCD AC FE ⟨hacirc, hccirc, hdp, hCentre, hfFE, hnfAC, heAC, heFE, hbet⟩)
  have hangle : ∠ a:e:f = ∟ := h.1 hassump1
  have hef : e ≠ f := by euclid_finish
  have hea : a ≠ e := by euclid_finish
  exact (angle_symm a e f ⟨hea, hef⟩).symm.trans hangle

end Elements.Book3
