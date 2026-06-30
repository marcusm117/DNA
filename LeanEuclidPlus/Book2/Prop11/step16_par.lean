import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step16_par
    (f c g k h : Point) (AC GH FG CD : Line)
    (hfAC : f.onLine AC) (hcAC : c.onLine AC)
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hhGH : h.onLine GH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hcCD : c.onLine CD) (hkCD : k.onLine CD)
    (hhoff : ¬h.onLine AC)
    (hGHAC : ¬GH.intersectsLine AC)
    (hfgcd : ¬FG.intersectsLine CD)
    (hFGneCD : FG ≠ CD) :
    formParallelogram f c g k AC GH FG CD := by
  euclid_intros
  have hACGH : ¬AC.intersectsLine GH := fun hh => hGHAC (intersection_symm AC GH hh)
  -- f, g on FG ∥ CD ⟹ f, g on the same side of CD.
  have hss : f.sameSide g CD := sameSide_of_parallel_both f g FG CD hfFG hgFG hFGneCD hfgcd
  -- c ∉ GH (c on AC ∥ GH, witness h on GH off AC) ⟹ c ≠ k (k on GH).
  have hcnGH : ¬c.onLine GH := offLine_of_parallel c h AC GH hcAC hhGH hhoff hGHAC
  have hck : c ≠ k := fun heq => hcnGH (heq ▸ hkGH)
  euclid_finish

end Elements.Book2
