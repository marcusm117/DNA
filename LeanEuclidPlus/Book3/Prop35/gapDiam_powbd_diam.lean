import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_gapDiam_powbd_diam (b d e f : Point) (ABCD : Circle) (BD : Line)
  (hb : b.onCircle ABCD) (hd : d.onCircle ABCD) (hbet2 : between b e d)
  (hfc : f.isCentre ABCD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
  (hf_bd : f.onLine BD)
  : |(b─e)| * |(e─d)| + |(f─e)| * |(f─e)| = |(f─b)| * |(f─b)| := by
  -- F is the midpoint of the diameter BD (|fb|=|fd|). Fix the order of e relative to F, then the
  -- length algebra closes; the explicit betweenness keeps euclid_finish under the cap.
  by_cases hef : e = f
  · subst hef
    euclid_finish
  · by_cases hord : between b f e
    · have h2 : between f e d := by euclid_finish
      euclid_finish
    · have h2 : between b e f := by euclid_finish
      have h3 : between e f d := by euclid_finish
      euclid_finish

end Elements.Book3
