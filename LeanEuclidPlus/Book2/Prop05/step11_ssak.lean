import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: k.sameSide a CE. k ∈ AK; a ∈ AK; AK ∥ CE (hAKCE). a ∉ CE (step11_doffCE analog:
   AK ≠ CE from step11_DGneCE → a ∉ CE via AK ≠ CE). Mirror of Prop06 step9_ssak. -/
theorem helper_2_5_step11_ssak (a k : Point) (AK CE : Line)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (haoffCE : ¬(a.onLine CE))
    (hAKCE : ¬(AK.intersectsLine CE)) :
    k.sameSide a CE := by
  euclid_intros
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  have hkoff : ¬(k.onLine CE) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point k AK CE)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing k a AK CE)
  euclid_finish

end Elements.Book2
