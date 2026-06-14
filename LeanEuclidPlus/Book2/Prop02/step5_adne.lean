import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: a ≠ d. |a─d| = |a─b| and a ≠ b (from between a c b), so |a─d| > 0; hence a
   and d are distinct. -/
theorem helper_2_2_step5_adne (a b c d : Point)
    (had : |(a─d)| = |(a─b)|) (hacb : between a c b) :
    a ≠ d := by
  euclid_finish

end Elements.Book2
