import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13 sub: d.sameSide c BE. c,d both on AB, and AB meets BE only at b. between c d b ⟹ b is NOT
   between c and d, so the segment cd does not cross BE; both lie off BE (else they'd equal b), hence
   on the same side. Mirror of step6_ssbd. -/
theorem helper_2_5_step13_dhdb_ssdc (b c d : Point) (AB BE : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE)
    (hcdb : between c d b)
    (hABBE : AB ≠ BE) :
    d.sameSide c BE := by
  euclid_intros
  have hcb : c ≠ b := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  have hcoff : ¬(c.onLine BE) := by
    by_contra hcon
    euclid_apply (intersection_lines_common_point c BE AB)
    euclid_finish
  have hdoff : ¬(d.onLine BE) := by
    by_contra hdon
    euclid_apply (intersection_lines_common_point d BE AB)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d c BE AB)
  euclid_finish

end Elements.Book2
