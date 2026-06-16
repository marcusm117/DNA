import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a.sameSide k DG. a ∈ AK; k ∈ AK; AK ∥ DG (step11_ahpar_akdg). a ∉ DG
   (step11_ahpar_aoffDG: a ∈ AK, AK ∥ DG). Both off DG and not separated → same side. -/
-- Mirror of Prop06 step9_ssak but for DG instead of DF.
-- a ∈ AK; AK ∥ DG; a ∉ DG (derived from AK ∥ DG + AK ≠ DG via heoffDG anchor)
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_ssak (a k h e : Point) (AK DG CE : Line)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hhDG : h.onLine DG) (heCE : e.onLine CE) (heoffDG : ¬(e.onLine DG))
    (hkh : k ≠ h)
    (hAKDG : ¬(AK.intersectsLine DG)) :
    a.sameSide k DG := by
  euclid_intros
  -- AK ≠ DG: if AK = DG then k ∈ DG, h ∈ DG, k ≠ h, k and h on AK = DG ∩ KM... hmm
  -- Use heoffDG: e ∉ DG and e ∈ CE; if AK = DG then AK.intersectsLine CE (via some anchor)
  -- Actually: use hkh to get AK ≠ DG: k ∈ AK, h ∈ DG, k ≠ h. If AK = DG then k ∈ DG.
  -- k ∈ DG and h ∈ DG and k ≠ h — that's fine; AK = DG doesn't force contradiction via k,h alone.
  -- Use the heoffDG: if AK = DG, a ∈ AK = DG, and e ∉ DG. We don't know if a ∈ DG by assumption.
  -- SIMPLER: just derive haoffDG from hAKDG + haAK by intro+intersection_lines_common_point
  -- But need AK ≠ DG first. Try euclid_finish.
  have hAKneDG : AK ≠ DG := by
    intro heq
    -- If AK = DG, then h ∈ DG = AK, so h ∈ AK. k ≠ h, but both k,h ∈ AK. Fine, no contradiction.
    -- Use e instead: e ∉ DG, e ∈ CE. If AK = DG, then AK ∩ CE = DG ∩ CE = ∅ (from hAKDG/hDGCE).
    -- But we don't have e ∈ AK... Actually this doesn't work.
    -- Use the hkh anchor: k ∈ AK∩KM, h ∈ DG∩KM. If AK = DG, two_points k,h on KM∩DG = KM∩AK.
    -- This means k and h both intersection points. But unique intersection? Not necessarily axiom.
    -- FALL BACK: euclid_finish
    euclid_finish
  have haoffDG : ¬(a.onLine DG) := by
    intro haonDG
    euclid_apply (intersection_lines_common_point a AK DG)
    euclid_finish
  have hkoff : ¬(k.onLine DG) := by
    intro hkDG
    euclid_apply (intersection_lines_common_point k AK DG)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing a k DG AK)
  euclid_finish

end Elements.Book2
