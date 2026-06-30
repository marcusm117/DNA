import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step3 (2.13.3): reorder step2's RHS — DA² (=|(d─a)|²) becomes |(a─d)|², DC² moves last.
-- Canonicalize |(d─a)|→|(a─d)|, then the residual is a ring identity (commutativity of +).
theorem helper_2_13_step3
  (c b d a : Point)
  (hstep2 : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| =
      2 * (|(c─b)| * |(b─d)|) + |(d─c)| * |(d─c)| + |(d─a)| * |(d─a)|)
  : |(c─b)| * |(c─b)| + |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| =
      2 * (|(c─b)| * |(b─d)|) + |(a─d)| * |(a─d)| + |(d─c)| * |(d─c)| := by
  have h : |(d─a)| = |(a─d)| := segment_symmetric d a
  rw [hstep2, h]; ring

end Elements.Book2
