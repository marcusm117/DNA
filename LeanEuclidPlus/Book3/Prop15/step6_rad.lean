import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Equal radii: |e─b| = |e─m| (both on circle ABCD with centre e)
theorem helper_3_15_step6_rad
    (b m e : Point) (ABCD : Circle)
    (h_centre : e.isCentre ABCD) (hb_on : b.onCircle ABCD) (hm_on : m.onCircle ABCD) :
    |(e─b)| = |(e─m)| := by
  euclid_finish

end Elements.Book3
