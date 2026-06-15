import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.11: |(g─k)| = |(k─b)|. Chain from the earlier equalities: |g─k| = |c─b| (step9) = |b─c|
   (distance symmetry) = |c─g| (step8) = |k─b| (step10). -/
theorem helper_2_4_step11 (b c g k : Point)
    (hstep8 : |(b─c)| = |(c─g)|)
    (hstep9 : |(c─b)| = |(g─k)|)
    (hstep10 : |(c─g)| = |(k─b)|) :
    |(g─k)| = |(k─b)| := by
  euclid_finish

end Elements.Book2
