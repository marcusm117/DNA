import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: h and g (both on BG) are on the same side of DF. h,g off DF (a common point of BG and DF
   would force them to meet, contradicting BG ∦ DF; BG ≠ DF since b ∈ BG, ¬b ∈ DF). Off DF and not
   separable, h and g share a side. -/
theorem helper_2_6_step7_sshg (b g h : Point) (BG DF : Line)
    (hhBG : h.onLine BG) (hgBG : g.onLine BG) (hbBG : b.onLine BG)
    (hboffDF : ¬(b.onLine DF))
    (hBGDF : ¬(BG.intersectsLine DF)) :
    h.sameSide g DF := by
  euclid_intros
  have hBGneDF : BG ≠ DF := fun heq => hboffDF (heq ▸ hbBG)
  have hhoff : ¬(h.onLine DF) := by
    by_contra hhon
    euclid_apply (intersection_lines_common_point h DF BG)
    euclid_finish
  have hgoff : ¬(g.onLine DF) := by
    by_contra hgon
    euclid_apply (intersection_lines_common_point g DF BG)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing h g DF BG)
  euclid_finish

end Elements.Book2
