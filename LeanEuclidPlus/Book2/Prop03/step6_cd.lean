import SystemE

namespace Elements.Book2

/- sub-fact: c ≠ d. |c─d| = |c─b| and c ≠ b (between a c b), so |c─b| > 0 = |c─d| would fail if
   c = d; hence c ≠ d. -/
set_option systemE.solverTime 30 in
theorem helper_2_step6_cd (a b c d : Point)
    (hacb : between a c b) (hcdlen : |(c─d)| = |(c─b)|) : c ≠ d := by
  euclid_finish

end Elements.Book2
