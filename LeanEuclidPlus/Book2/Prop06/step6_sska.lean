import SystemE
import Book2.Prop06.step6_sska_aoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: k and a (both on the left vertical AK) are on the same side of the right
   vertical CE. a ∉ CE (step6_sska_aoff), so AK ≠ CE (a witnesses it); then k ∉ CE (a shared point
   would force AK,CE to meet, contradicting AK ∦ CE). Off CE and not separable across it, k and a
   share a side (intersection_lines_opposing contrapositive). -/
theorem helper_2_6_step6_sska (a b c d e k : Point) (AB CE AK : Line)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hAKCE : ¬(AK.intersectsLine CE)) :
    k.sameSide a CE := by
  euclid_intros
  have step6_sska_aoff : ¬(a.onLine CE) := by euclid_apply (helper_2_6_step6_sska_aoff a b c d e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have hAKneCE : AK ≠ CE := fun h => step6_sska_aoff (h ▸ haAK)
  have hkoff : ¬(k.onLine CE) := by
    by_contra hkon
    euclid_apply (intersection_lines_common_point k CE AK)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing k a CE AK)
  euclid_finish

end Elements.Book2
