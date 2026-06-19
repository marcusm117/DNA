import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(h.onLine EF). h ∈ BE with between b h e; e ∈ EF; b ∉ EF (step8_boffef).
   If h ∈ EF then e,h ∈ EF ∩ BE with e ≠ h (between b h e ⟹ h ≠ e), so EF = BE, hence
   b ∈ EF — contradicting b ∉ EF. -/
theorem helper_2_5_step8_hoffef (b e h : Point) (EF BE : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE) (heEF : e.onLine EF)
    (hbhe : between b h e)
    (hboffEF : ¬(b.onLine EF)) :
    ¬(h.onLine EF) := by
  intro hhEF
  have heh : e ≠ h := by euclid_finish
  have hEFisBE : EF = BE := by
    euclid_apply (two_points_determine_line e h EF BE)
    euclid_finish
  exact hboffEF (hEFisBE ▸ hbBE)

end Elements.Book2
