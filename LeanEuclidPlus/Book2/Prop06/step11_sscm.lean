import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.11 sub: c.sameSide m AK. c and d (both on AB) are on the same side of AK (AK ∩ AB = a, and the
   order a–c–b–d puts c, d both on the b-side of a, so a is not between them); d and m (both on DF ∥ AK)
   are on the same side of AK. Transitivity gives c.sameSide m AK. Off-line anchors derived in-body. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11_sscm (a b c d m : Point) (AB AK CE DF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (haAK : a.onLine AK)
    (hcCE : c.onLine CE)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF)
    (hacb : between a c b) (habd : between a b d)
    (haoffCE : ¬(a.onLine CE)) (haoffDF : ¬(a.onLine DF))
    (hAKCE : ¬(AK.intersectsLine CE)) (hAKDF : ¬(AK.intersectsLine DF)) :
    c.sameSide m AK := by
  euclid_intros
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  have hAKneDF : AK ≠ DF := fun heq => haoffDF (heq ▸ haAK)
  have hcoffAK : ¬(c.onLine AK) := by
    intro hon; euclid_apply (intersection_lines_common_point c AK CE); euclid_finish
  have hdoffAK : ¬(d.onLine AK) := by
    intro hon; euclid_apply (intersection_lines_common_point d AK DF); euclid_finish
  have hmoffAK : ¬(m.onLine AK) := by
    intro hon; euclid_apply (intersection_lines_common_point m AK DF); euclid_finish
  -- c.sameSide d AK: c, d on AB, a (= AK ∩ AB) not between them
  have hcd_ss : c.sameSide d AK := by
    by_contra hns; euclid_apply (intersection_lines_opposing c d AK AB); euclid_finish
  -- d.sameSide m AK: d, m on DF ∥ AK
  have hdm_ss : d.sameSide m AK := by
    by_contra hns; euclid_apply (intersection_lines_opposing d m AK DF); euclid_finish
  euclid_finish

end Elements.Book2
