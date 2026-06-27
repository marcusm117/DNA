import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.28: square on FG = square on FE. From |g─f| = |e─f| (GF = EF, step23) by segment symmetry,
   then squaring. Pure rw. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step28
  (e f g : Point)
  (hstep23 : |(g─f)| = |(e─f)|) :
  |(f─g)| * |(f─g)| = |(f─e)| * |(f─e)| := by
  have h : |(f─g)| = |(f─e)| := by
    rw [segment_symmetric f g, segment_symmetric f e, hstep23]
  rw [h]

end Elements.Book2
