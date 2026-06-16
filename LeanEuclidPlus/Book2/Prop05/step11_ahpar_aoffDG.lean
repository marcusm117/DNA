import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a ∉ DG. a ∈ AK; AK ∥ DG (step11_ahpar_akdg). AK ≠ DG from l ∈ KM∩CE
   and l ∉ DG (DG∩KM = {h}, l ≠ h from between k l h): if AK = DG then l ∈ DG → DG∩CE at l.
   Pass AK ≠ DG directly via step11_ahpar_akdg. -/
-- AK ≠ DG: k ∈ AK∩KM, h ∈ DG∩KM, k ≠ h, d ∈ DG, d ∈ AB, KM∥AB.
-- If AK = DG: k ∈ DG and h ∈ DG, k ≠ h → two_points(k,h,DG,KM) → DG = KM → d ∈ KM
--   → d ∈ AB ∩ KM → AB∩KM contradiction.
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_aoffDG (a d k h : Point) (AB AK DG KM : Line)
    (haAK : a.onLine AK) (hdDG : d.onLine DG) (hdAB : d.onLine AB)
    (hkAK : k.onLine AK) (hkKM : k.onLine KM) (hhDG : h.onLine DG) (hhKM : h.onLine KM)
    (hkh : k ≠ h)
    (hAKDG : ¬(AK.intersectsLine DG)) (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(a.onLine DG) := by
  intro haonDG
  have hAKneDG : AK ≠ DG := by
    intro heq
    -- k ∈ DG (k ∈ AK = DG), h ∈ DG, k ≠ h → DG = KM
    have hkDG : k.onLine DG := heq ▸ hkAK
    have hDGisKM : DG = KM := by
      euclid_apply (two_points_determine_line k h DG KM)
      euclid_finish
    -- d ∈ DG = KM and d ∈ AB → AB ∩ KM at d → contradicts hKMAB
    have hdKM : d.onLine KM := hDGisKM ▸ hdDG
    have hKMneAB : KM ≠ AB := by
      intro heq2; exact hKMAB (by rw [heq2]; euclid_finish)
    euclid_apply (intersection_lines_common_point d KM AB)
    euclid_finish
  euclid_apply (intersection_lines_common_point a AK DG)
  euclid_finish

end Elements.Book2
