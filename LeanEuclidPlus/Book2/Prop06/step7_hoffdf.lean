import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: h ∉ DF. h ∈ BG, BG ∥ DF (¬BG.intersectsLine DF) and BG ≠ DF (b ∈ BG, ¬b ∈ DF). A point
   on BG cannot lie on the parallel DF. -/
theorem helper_2_6_step7_hoffdf (b h : Point) (BG DF : Line)
    (hhBG : h.onLine BG) (hbBG : b.onLine BG)
    (hboffDF : ¬(b.onLine DF))
    (hBGDF : ¬(BG.intersectsLine DF)) :
    ¬(h.onLine DF) := by
  intro hhDF
  have hBGneDF : BG ≠ DF := fun heq => hboffDF (heq ▸ hbBG)
  euclid_apply (intersection_lines_common_point h DF BG)
  euclid_finish

end Elements.Book2
