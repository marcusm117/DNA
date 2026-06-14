import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.8 (length): b and g (both on BF) are on the same side of DK. b,g are off DK
   (a common point of DK and BF would force them to meet, contradicting DK ∦ BF — DK ≠ BF since
   d ≠ b on DK∩BC while f on BF is off BC). Being off DK and not separable across it, share a side. -/
theorem helper_2_1_step8_len_ss (b d e f g : Point) (BC BF DK : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC) (hbde : between b d e)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hdDK : d.onLine DK) (hDKBF : ¬(DK.intersectsLine BF)) :
    b.sameSide g DK := by
  euclid_intros
  euclid_apply (between_symm b d e)
  have hboff : ¬(b.onLine DK) := by
    by_contra hbon
    euclid_apply (intersection_lines_common_point b DK BF)
    euclid_finish
  have hgoff : ¬(g.onLine DK) := by
    by_contra hgon
    euclid_apply (intersection_lines_common_point g DK BF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b g DK BF)
  euclid_finish

end Elements.Book2
