import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: k and a (both on the left vertical AK) are on the same side of the right
   vertical CE. a ∉ CE (step6_sska_aoff), so AK ≠ CE (a witnesses it); then k ∉ CE (a shared point
   would force AK,CE to meet, contradicting AK ∦ CE). Off CE and not separable across it, k and a
   share a side (intersection_lines_opposing contrapositive). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step6_sska (a b c d e k : Point) (AB CE AK : Line)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hAKCE : ¬(AK.intersectsLine CE)) :
    k.sameSide a CE := by
  euclid_intros
  have step6_sska_aoff : ¬(a.onLine CE) := by sorry
  have hAKneCE : AK ≠ CE := fun h => step6_sska_aoff (h ▸ haAK)
  have hkoff : ¬(k.onLine CE) := by
    by_contra hkon
    euclid_apply (intersection_lines_common_point k CE AK)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing k a CE AK)
  euclid_finish

end Elements.Book2
