import SystemE
import Book2.Prop05.step11_ahpar_aoffDG_ne
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a ∉ DG. AK ∥ DG (hAKDG), AK ≠ DG (step11_ahpar_aoffDG_ne sub-node,
   mirrors akdg.lean AK≠DG sub-proof). euclid_intros introduces a.onLine DG;
   intersection_lines_common_point a AK DG closes. -/
theorem helper_2_5_step11_ahpar_aoffDG (a d k h l : Point) (AK DG CE KM : Line)
    (haAK : a.onLine AK) (hdDG : d.onLine DG) (hdoffCE : ¬(d.onLine CE))
    (hkAK : k.onLine AK) (hkKM : k.onLine KM) (hhDG : h.onLine DG) (hhKM : h.onLine KM)
    (hlKM : l.onLine KM) (hlCE : l.onLine CE)
    (hkh : k ≠ h)
    (hAKDG : ¬(AK.intersectsLine DG)) (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(a.onLine DG) := by
  euclid_intros
  have step11_ahpar_aoffDG_ne : AK ≠ DG := by euclid_apply (helper_2_5_step11_ahpar_aoffDG_ne d k h l AK DG CE KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (intersection_lines_common_point a AK DG)
  euclid_finish

end Elements.Book2
