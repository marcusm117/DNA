import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: a.sameSide k DF (a and k both on AK, which is parallel to DF). a,k off DF (a common
   point of AK and DF would force them to meet, contradicting AK ∦ DF; AK ≠ DF since a ∈ AK, ¬a ∈ DF).
   Off DF and not separable, a and k share a side. a ∉ DF supplied (step9_aoffdf). -/
theorem helper_2_6_step9_ssak (a k : Point) (AK DF : Line)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (haoffDF : ¬(a.onLine DF))
    (hAKDF : ¬(AK.intersectsLine DF)) :
    a.sameSide k DF := by
  euclid_intros
  have hAKneDF : AK ≠ DF := fun heq => haoffDF (heq ▸ haAK)
  have hkoff : ¬(k.onLine DF) := by
    by_contra hon
    euclid_apply (intersection_lines_common_point k DF AK)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing a k DF AK)
  euclid_finish

end Elements.Book2
