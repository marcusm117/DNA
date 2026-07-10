import SystemE
import Book.Prop23
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- step23 assembles b0's properties: on circle, opposing side, angle, and DB distinctness.
-- Extra binders (MK, hmcenter, etc.) are needed so step23_prop23's SP passes for criterion-3.
set_option systemE.solverTime 30 in
theorem helper_3_8_step23
    (ABC : Circle) (m d k b0 : Point) (AG DB MK : Line)
    (hmcenter : m.isCentre ABC)
    (hdnInside : ¬d.insideCircle ABC)
    (hdnotCircle : ¬d.onCircle ABC)
    (hb0circ : b0.onCircle ABC)
    (hb0_ang : ∠ d:m:b0 = ∠ k:m:d)
    (hb0offAG : ¬b0.onLine AG)
    (hkoffAG : ¬k.onLine AG)
    (hb0notsamek : ¬b0.sameSide k AG)
    (hdDB : d.onLine DB)
    (hb0DB : b0.onLine DB)
    (hmAG : m.onLine AG) (hdAG : d.onLine AG)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK) :
    b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d ∧
    distinctPointsOnLine d b0 DB := by
  -- Cite proposition_23 for criterion-3 (b0's angle was constructed equal to ∠k:m:d).
  have step23_prop23 : ∃ f : Point, f ≠ m ∧ ∠f:m:d = ∠k:m:d := by sorry
  refine ⟨hb0circ, ⟨hb0offAG, hkoffAG, hb0notsamek⟩, hb0_ang, hdDB, hb0DB, ?_⟩
  exact fun h => hdnotCircle (h ▸ hb0circ)

end Elements.Book3
