import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- II.5 instance for chord BD cut equally at midpoint m, unequally at e (see gapDiam_ac_ii5 / step7).
theorem helper_3_35_step15_ii5 (b d e m : Point) (BD : Line)
  (hbet2 : between b e d) (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hmBD : m.onLine BD)
  (hbisect : |(m─b)| = |(m─d)|)
  : |(b─e)| * |(e─d)| + |(m─e)| * |(m─e)| = |(m─d)| * |(m─d)| := by
  by_cases hem : e = m
  · subst hem
    euclid_finish
  · by_cases hord : between b m e
    · have h2 : between m e d := by euclid_finish
      euclid_finish
    · have h2 : between b e m := by euclid_finish
      have h3 : between e m d := by euclid_finish
      euclid_finish

end Elements.Book3
