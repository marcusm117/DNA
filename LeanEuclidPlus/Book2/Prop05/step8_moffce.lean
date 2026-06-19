import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(m.onLine CE). m ∈ BF; BF ∥ CE (hCEBF). BF ≠ CE because b ∈ BF is off CE
   (step8_boffce). A common point of BF,CE would then force them to meet. -/
theorem helper_2_5_step8_moffce (b c m : Point) (CE BF : Line)
    (hmBF : m.onLine BF) (hbBF : b.onLine BF) (hcCE : c.onLine CE)
    (hboffCE : ¬(b.onLine CE))
    (hCEBF : ¬(CE.intersectsLine BF)) :
    ¬(m.onLine CE) := by
  intro hmCE
  have hBFneCE : BF ≠ CE := fun heq => hboffCE (heq ▸ hbBF)
  euclid_apply (intersection_lines_common_point m BF CE)
  euclid_finish

end Elements.Book2
