import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: ¬d.sameSide e BG (d and e on opposite sides of the middle vertical BG). On AB, b ∈ BG is
   between c and d, so by pasch_3 c and d are on opposite sides of BG (step7_cnsdBG: ¬c.sameSide d BG).
   c and e lie on CE ∥ BG, hence on the same side (step7_sscebg: c.sameSide e BG). If d.sameSide e then
   with c.sameSide e (symm) same_side_trans would give c.sameSide d — contradicting step7_cnsdBG. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_dnseBG (c d e : Point) (BG : Line)
    (hcnsd : ¬(c.sameSide d BG)) (hssce : c.sameSide e BG) :
    ¬(d.sameSide e BG) := by
  intro hdse
  euclid_apply (same_side_symm c e BG)
  euclid_apply (same_side_symm d e BG)
  euclid_apply (same_side_trans e c d BG)
  euclid_finish

end Elements.Book2
