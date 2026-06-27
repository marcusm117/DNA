import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.24: square on EC = square on CA. From |c─e| = |a─c| (EC = CA, the construction/step2 fact) by
   segment symmetry, then squaring. Pure rw (segment_symmetric), no SMT. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step24
  (a c e : Point)
  (hce_ac : |(c─e)| = |(a─c)|) :
  |(e─c)| * |(e─c)| = |(c─a)| * |(c─a)| := by
  have h : |(e─c)| = |(c─a)| := by
    rw [segment_symmetric e c, segment_symmetric c a, hce_ac]
  rw [h]

end Elements.Book2
