import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: h ∉ EF. h ∈ BE; e ∈ BE ∩ EF and ¬b ∈ EF (step6_boffef) gives BE ≠ EF. h ≠ e because
   h ∈ DG but e ∉ DG (step6_eoffdg). If h ∈ EF then h, e are two distinct points on both BE and EF,
   forcing BE = EF — contradiction. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_hoffef (b e h : Point) (BE EF DG : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hhDG : h.onLine DG)
    (hboffEF : ¬(b.onLine EF)) (heoffDG : ¬(e.onLine DG)) :
    ¬(h.onLine EF) := by
  intro hhEF
  have hBEneEF : BE ≠ EF := fun heq => hboffEF (heq ▸ hbBE)
  have hhe : h ≠ e := fun heq => heoffDG (heq ▸ hhDG)
  euclid_apply (two_points_determine_line h e EF BE)
  euclid_finish

end Elements.Book2
