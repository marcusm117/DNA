import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: c and l (both on CE) are on the same side of BG. c,l off BG (a common point of CE and BG
   would force them to meet, contradicting CE ∦ BG; BG ≠ CE since b ∈ BG, ¬b ∈ CE). Off BG and not
   separable, c and l share a side. -/
theorem helper_2_6_step7_sscl (b c l : Point) (CE BG : Line)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE) (hbBG : b.onLine BG)
    (hboffCE : ¬(b.onLine CE))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    c.sameSide l BG := by
  euclid_intros
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hcoff : ¬(c.onLine BG) := by
    by_contra hcon
    euclid_apply (intersection_lines_common_point c BG CE)
    euclid_finish
  have hloff : ¬(l.onLine BG) := by
    by_contra hlon
    euclid_apply (intersection_lines_common_point l BG CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing c l BG CE)
  euclid_finish

end Elements.Book2
