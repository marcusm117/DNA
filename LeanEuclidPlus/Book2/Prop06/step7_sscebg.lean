import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: c.sameSide e BG (c and e both on CE, which is parallel to BG). c,e off BG (a common
   point of CE and BG would force them to meet, contradicting BG ∦ CE; BG ≠ CE since b ∈ BG, ¬b ∈ CE).
   Off BG and not separable, c and e share a side. -/
theorem helper_2_6_step7_sscebg (b c e : Point) (CE BG : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hbBG : b.onLine BG)
    (hboffCE : ¬(b.onLine CE))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    c.sameSide e BG := by
  euclid_intros
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hcoff : ¬(c.onLine BG) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point c BG CE)
    euclid_finish
  have heoff : ¬(e.onLine BG) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point e BG CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing c e BG CE)
  euclid_finish

end Elements.Book2
