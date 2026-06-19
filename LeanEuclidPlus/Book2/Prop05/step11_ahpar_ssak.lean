import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: a.sameSide k DG. a,k both on AK (∥ DG). a∉DG already proved (haoffDG).
   k∉DG via intersection_lines_common_point. Then by_contra + intersection_lines_opposing. -/
theorem helper_2_5_step11_ahpar_ssak (a k : Point) (AK DG : Line)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (haoffDG : ¬(a.onLine DG))
    (hAKDG : ¬(AK.intersectsLine DG)) :
    a.sameSide k DG := by
  euclid_intros
  have hAKneDG : AK ≠ DG := fun heq => haoffDG (heq ▸ haAK)
  have hkoff : ¬(k.onLine DG) := by
    intro hon
    euclid_apply (intersection_lines_common_point k AK DG)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing a k DG AK)
  euclid_finish

end Elements.Book2
