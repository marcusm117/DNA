import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: |(d─h)| = |(a─c)|. h is between a and d on AD, so |a─h| + |h─d| = |a─d| = |a─b|
   (square side). With |a─h| = |b─c| (the rectangle ABFH side, = BF = BC) and |a─c| + |c─b| = |a─b|
   (c between a and b), we get |h─d| = |a─b| − |b─c| = |a─c|, i.e. |d─h| = |a─c|. -/
theorem helper_2_7_step11_dhac (a b c d h : Point)
    (hacb : between a c b) (hahd : between a h d)
    (hadab : |(a─d)| = |(a─b)|) (hahbc : |(a─h)| = |(b─c)|) :
    |(d─h)| = |(a─c)| := by
  euclid_finish

end Elements.Book2
