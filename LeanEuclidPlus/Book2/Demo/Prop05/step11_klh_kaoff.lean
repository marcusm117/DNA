import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: k ∉ CE. k ∈ AK; AK ∥ CE. AK ≠ CE follows from ¬AK.intersectsLine CE.
   If k ∈ CE then intersection_lines_common_point k AK CE gives AK.intersectsLine CE — contradiction. -/
/- k ∉ CE. k ∈ AK; a ∈ AK, a ∉ CE (from aaoff). So AK ≠ CE. Then k ∈ CE ∧ k ∈ AK + distinctness
   → intersection_lines_common_point k AK CE gives AK.intersectsLine CE — contradicts hAKCE. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_klh_kaoff (a k : Point) (AK CE : Line)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (haoffCE : ¬(a.onLine CE))
    (hAKCE : ¬(AK.intersectsLine CE)) :
    ¬(k.onLine CE) := by
  intro hkCE
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  euclid_apply (intersection_lines_common_point k AK CE)
  euclid_finish

end Elements.Book2
