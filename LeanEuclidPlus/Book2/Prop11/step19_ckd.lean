import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step19_ckd
    (a b c d h k : Point) (AC BD GH CD : Line)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hkGH : k.onLine GH) (hhGH : h.onLine GH)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbet_ahb : between a h b)
    (hACGH : ¬AC.intersectsLine GH) (hBDGH : ¬BD.intersectsLine GH)
    (hACneGH : AC ≠ GH) (hBDneGH : BD ≠ GH) (hGHneCD : GH ≠ CD) :
    between c k d := by
  -- a and b opposite across GH (h between them, h on GH).
  have hab_opp : ¬a.sameSide b GH := pasch_3 a h b GH ⟨hbet_ahb, hhGH⟩
  -- c (with a on AC ∥ GH) and d (with b on BD ∥ GH) inherit opposite sides.
  have hca : c.sameSide a GH := sameSide_of_parallel_both c a AC GH hcAC haAC hACneGH hACGH
  have hdb : d.sameSide b GH := sameSide_of_parallel_both d b BD GH hdBD hbBD hBDneGH hBDGH
  have hcd_opp : ¬c.sameSide d GH := by euclid_finish
  have hck : c ≠ k := by euclid_finish
  have hdk : d ≠ k := by euclid_finish
  have hcd : c ≠ d := by euclid_finish
  -- k = GH ∩ CD lies between c and d (opposite sides of GH).
  exact pasch_4 c k d GH CD ⟨hGHneCD, hkGH, hkCD, ⟨hcCD, hdCD, hcd⟩, hck, hdk, hcd_opp⟩

end Elements.Book2
