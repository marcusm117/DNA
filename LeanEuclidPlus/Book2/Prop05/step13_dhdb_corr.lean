import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.13 sub: ∠ d:h:b = ∠ c:e:b. DG (through d,h) ∥ CE (through c,e), cut by the diagonal BE
   (through b,h,e) with h between b and e. proposition_29'''' gives the corresponding angle
   ∠ b:h:d = ∠ h:e:c; ray e→h coincides with e→b (h between b,e) so ∠ c:e:h = ∠ c:e:b, and
   angle symmetries rewrite to ∠ d:h:b = ∠ c:e:b. (Mirror of Prop04 step5_corr.) -/
theorem helper_2_5_step13_dhdb_corr (b c d e h : Point) (DG CE BE : Line)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbhe : between b h e) (hdcBE : d.sameSide c BE)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    ∠ d:h:b = ∠ c:e:b := by
  euclid_intros
  -- corresponding angles via proposition_29'''': ∠ b:h:d = ∠ h:e:c
  have hcorr : ∠ b:h:d = ∠ h:e:c := by
    euclid_apply (proposition_29'''' d c b h e DG CE BE)
    euclid_finish
  -- ray e→h coincides with e→b (h between b and e), so ∠ c:e:h = ∠ c:e:b
  have hray : ∠ c:e:h = ∠ c:e:b := by
    euclid_apply (equal_angles e h b c c BE CE)
    euclid_finish
  -- symmetries (∠ d:h:b = ∠ b:h:d, ∠ h:e:c = ∠ c:e:h) close the chain
  euclid_finish

end Elements.Book2
