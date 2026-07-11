import SystemE
import Book3.Prop02.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- d, b lie on the circumference of each circle, so by III.2 the segment db falls inside each.
theorem helper_3_13_step15 (ABDC EBFD : Circle) (d b : Point)
    (step15_assumption1 :
      d.onCircle ABDC ∧ d.onCircle EBFD ∧ b.onCircle ABDC ∧ b.onCircle EBFD ∧ d ≠ b) :
    ∀ r : Point, between d r b → r.insideCircle ABDC ∧ r.insideCircle EBFD := by
  obtain ⟨hd_A, hd_E, hb_A, hb_E, hdb⟩ := step15_assumption1
  intro r hr
  euclid_apply (proposition_2 d b ABDC ⟨hd_A, hb_A, hdb⟩ r hr)
  euclid_apply (proposition_2 d b EBFD ⟨hd_E, hb_E, hdb⟩ r hr)
  euclid_finish

end Elements.Book3
