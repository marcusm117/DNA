import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step19_ghk
    (a b c f g h k : Point) (AB AC FG CD GH : Line)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hkGH : k.onLine GH)
    (haAB : a.onLine AB) (hhAB : h.onLine AB)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hcCD : c.onLine CD) (hkCD : k.onLine CD)
    (hbet_fac : between f a c)
    (hFGAB : ¬FG.intersectsLine AB) (hCDAB : ¬CD.intersectsLine AB)
    (hFGneAB : FG ≠ AB) (hCDneAB : CD ≠ AB) (hABneGH : AB ≠ GH) :
    between g h k := by
  -- f and c are on opposite sides of AB (a between them, a on AB).
  have hfc_opp : ¬f.sameSide c AB := pasch_3 f a c AB ⟨hbet_fac, haAB⟩
  -- g (with f on FG ∥ AB) and k (with c on CD ∥ AB) inherit opposite sides ⟹ g, k opposite across AB.
  have hgf : g.sameSide f AB := sameSide_of_parallel_both g f FG AB hgFG hfFG hFGneAB hFGAB
  have hkc : k.sameSide c AB := sameSide_of_parallel_both k c CD AB hkCD hcCD hCDneAB hCDAB
  have hgk_opp : ¬g.sameSide k AB := by euclid_finish
  have hgh : g ≠ h := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hgk : g ≠ k := by euclid_finish
  -- h = GH ∩ AB lies between g and k (opposite sides of AB).
  exact pasch_4 g h k AB GH ⟨hABneGH, hhAB, hhGH, ⟨hgGH, hkGH, hgk⟩, hgh, hkh, hgk_opp⟩

end Elements.Book2
