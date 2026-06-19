import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: AK ≠ DG. Mirrors step11_ahpar_akdg's AK≠DG sub-proof.
   If AK=DG: k∈DG; k,h ∈ DG∩KM, k≠h → DG=KM → l∈DG (l∈KM=DG) → l∈DG∩CE (l∈CE) →
   DG≠CE (d∈DG, d∉CE = hdoffCE) → intersection_lines_common_point l DG CE → DG∩CE →
   contradicts hDGCE. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_aoffDG_ne (d k h l : Point) (AK DG CE KM : Line)
    (hdDG : d.onLine DG) (hdoffCE : ¬(d.onLine CE))
    (hkAK : k.onLine AK) (hkKM : k.onLine KM) (hhDG : h.onLine DG) (hhKM : h.onLine KM)
    (hlKM : l.onLine KM) (hlCE : l.onLine CE)
    (hkh : k ≠ h)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    AK ≠ DG := by
  intro heq
  have hkDG : k.onLine DG := heq ▸ hkAK
  have hDGisKM : DG = KM := by
    euclid_apply (two_points_determine_line k h DG KM)
    euclid_finish
  have hlDG : l.onLine DG := hDGisKM ▸ hlKM
  have hDGneCE : DG ≠ CE := fun h => hdoffCE (h ▸ hdDG)
  euclid_apply (intersection_lines_common_point l DG CE)
  euclid_finish

end Elements.Book2
