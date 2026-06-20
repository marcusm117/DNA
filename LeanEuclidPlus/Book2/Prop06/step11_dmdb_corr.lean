import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: ∠ d:h:b = ∠ c:e:d. BG (through b,h) ∥ CE (through c,e), cut by the diagonal DE
   (through d,h,e) with h between d and e. proposition_29'''' gives the corresponding angle
   ∠ d:h:b = ∠ h:e:c; ray e→h coincides with e→d (h between d,e) so ∠ c:e:h = ∠ c:e:d, and angle
   symmetries rewrite to ∠ d:h:b = ∠ c:e:d. (Mirror of Prop05 step13_dhdb_corr.) -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11_dmdb_corr (b c d e h : Point) (BG CE DE : Line)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDE : d.onLine DE) (hhDE : h.onLine DE) (heDE : e.onLine DE)
    (hdhe : between d h e) (hbcDE : b.sameSide c DE)
    (hBGCE : ¬(BG.intersectsLine CE)) :
    ∠ d:h:b = ∠ c:e:d := by
  euclid_intros
  -- corresponding angles via proposition_29'''': ∠ d:h:b = ∠ h:e:c
  have hcorr : ∠ d:h:b = ∠ h:e:c := by
    euclid_apply (proposition_29'''' b c d h e BG CE DE)
    euclid_finish
  -- ray e→h coincides with e→d (h between d,e), so ∠ h:e:c = ∠ d:e:c
  have hray : ∠ h:e:c = ∠ d:e:c := by
    euclid_apply (equal_angles e h d c c DE CE)
    euclid_finish
  euclid_finish

end Elements.Book2
