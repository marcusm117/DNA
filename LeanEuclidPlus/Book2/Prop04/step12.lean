import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.12: CGKB is equilateral — |c─g| = |g─k| = |k─b| = |b─c|. From |b─c| = |c─g| (step8),
   |c─b| = |g─k| (step9), |c─g| = |k─b| (step10), |g─k| = |k─b| (step11) and distance symmetry. -/
theorem helper_2_4_step12 (b c g k : Point)
    (hstep8 : |(b─c)| = |(c─g)|)
    (hstep9 : |(c─b)| = |(g─k)|)
    (hstep10 : |(c─g)| = |(k─b)|)
    (hstep11 : |(g─k)| = |(k─b)|) :
    |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)| := by
  euclid_finish

end Elements.Book2
