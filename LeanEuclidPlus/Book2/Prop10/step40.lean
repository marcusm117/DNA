import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.40: |DG| = |DB. From step20 (|b─d| = |g─d|) by segment symmetry (|d─g| = |g─d| = |b─d| = |d─b|).
   Pure rw. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step40
  (b d g : Point)
  (hstep20 : |(b─d)| = |(g─d)|) :
  |(d─g)| = |(d─b)| := by
  rw [segment_symmetric d g, segment_symmetric d b, hstep20]

end Elements.Book2
