import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.11 sub: formParallelogram a d h k AB KM AK DG. AK ∥ DG from AK ∥ CE ∥ DG (Prop.1.30).
   AB ∥ KM from hKMAB (symm). k ≠ h from between k l h (step11_klh). a.sameSide d KM
   needed (both on AB, KM ∥ AB). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar (a d e h k l : Point) (AB KM AK DG CE : Line)
    (haAB : a.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (haoffCE : ¬(a.onLine CE)) (hdoffCE : ¬(d.onLine CE)) (heoffDG : ¬(e.onLine DG))
    (hklh : between k l h) (hdhg : between d h g)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hAKCE : ¬(AK.intersectsLine CE)) (hDGCE : ¬(DG.intersectsLine CE)) :
    formParallelogram a d k h AB KM AK DG := by
  euclid_intros
  -- a.sameSide k DG (A.sameSide C L4=DG), AK ∥ DG, AB ∥ KM (symm), k≠h, d≠h
  -- k ≠ h from between k l h (l strictly between them on KM)
  have step11_ahpar_kh : k ≠ h := by sorry
  -- d ≠ h: d ∈ AB, h ∈ KM, distinct lines
  have step11_ahpar_dh : d ≠ h := by sorry
  -- AK ∥ DG: from AK ∥ CE ∥ DG (proposition_30). AK ≠ DG from k ∈ AK∩KM and h ∈ DG∩KM and k≠h.
  have step11_ahpar_akdg : ¬(AK.intersectsLine DG) := by sorry
  -- a ∉ DG (needed for ssak): a ∈ AK, AK ∥ DG (step11_ahpar_akdg gives AK ≠ DG from context)
  have step11_ahpar_aoffDG : ¬(a.onLine DG) := by sorry
  -- a.sameSide k DG (position 8 = A.sameSide C L4=DG)
  have step11_ahpar_ssak : a.sameSide k DG := by sorry
  -- AB ∥ KM (¬AB∩KM via intersection_symm from hKMAB)
  have step11_ahpar_abkm : ¬(AB.intersectsLine KM) := by sorry
  exact ⟨haAB, hdAB, hkKM, hhKM, haAK, hkAK, ⟨hdDG, hhDG, step11_ahpar_dh⟩, step11_ahpar_ssak,
         step11_ahpar_abkm, step11_ahpar_akdg⟩

end Elements.Book2
