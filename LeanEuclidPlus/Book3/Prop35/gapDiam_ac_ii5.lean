import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The II.5 identity for the chord AC cut equally at the midpoint m and unequally at e. II.5 itself
-- (Book2/Prop05) is not yet a proven lemma in this repo, so we prove the instance directly: once the
-- collinear order of a, m, e, c is fixed, the length algebra is closed by euclid_finish (exactly as in
-- the diameter case, where the midpoint's betweenness was already explicit).
theorem helper_3_35_gapDiam_ac_ii5 (a c e m : Point) (AC : Line)
  (hbet1 : between a e c) (haAC : a.onLine AC) (hcAC : c.onLine AC) (hmAC : m.onLine AC)
  (hbisect : |(m─a)| = |(m─c)|)
  : |(a─e)| * |(e─c)| + |(m─e)| * |(m─e)| = |(m─c)| * |(m─c)| := by
  by_cases hem : e = m
  · subst hem
    euclid_finish
  · by_cases hord : between a m e
    · -- order a, m, e, c
      have h2 : between m e c := by euclid_finish
      euclid_finish
    · -- order a, e, m, c
      have h2 : between a e m := by euclid_finish
      have h3 : between e m c := by euclid_finish
      euclid_finish

end Elements.Book3
