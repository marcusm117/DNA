import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- step29: 4|ab||bc| + |ac|² = (|ab|+|bc|)².
   Faithful chain: step27 (4|ab||bd| + |ac|² = |ad|²), step28 (|bd| = |bc|), and
   |ad| = |ab|+|bd| (segment addition from `between a b d`). Since |bd| = |bc|,
   |ad| = |ab|+|bc|, so |ad|² is exactly the square on AB-and-BC-as-one-line.
   Pure term/rw — no euclid_finish, so the product terms pose no problem. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step29 (a b c d : Point)
    (h_abd : between a b d)
    (h_step27 : 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)|)
    (h_step28 : |(b─d)| = |(b─c)|) :
    4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
      (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) := by
  have h_ad_bd : |(a─b)| + |(b─d)| = |(a─d)| := between_if a b d h_abd
  rw [← h_step28, h_ad_bd]
  exact h_step27

end Elements.Book2
