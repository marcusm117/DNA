import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: e ∉ BG. e ∈ CE, BG ∥ CE (¬BG.intersectsLine CE) and BG ≠ CE (b ∈ BG, ¬b ∈ CE). A point
   on CE cannot lie on the parallel BG. -/
theorem helper_2_6_step7_eoffbg (b e : Point) (CE BG : Line)
    (heCE : e.onLine CE) (hbBG : b.onLine BG)
    (hboffCE : ¬(b.onLine CE))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    ¬(e.onLine BG) := by
  intro heBG
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  euclid_apply (intersection_lines_common_point e BG CE)
  euclid_finish

end Elements.Book2
