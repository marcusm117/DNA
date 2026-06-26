import SystemE
import Book2.Prop07.step11_bse
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: n (= CN ∩ DE) is between d and e on DE. The vertical CN separates d from e: a, b are
   on opposite sides of CN (c ∈ CN between a, b on AB, pasch_3); a, d on the same side (both on
   AD ∥ CN, step3_bgd_ss = a.sameSide d CN); b, e on the same side (both on BE ∥ CN, step11_bse);
   hence d, e on opposite sides of CN, and the crossing n of DE with CN lies between them (pasch_4). -/
theorem helper_2_7_step11_dne (a b c d e n g : Point) (AB CN AD BE DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcCN : c.onLine CN) (hnCN : n.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hCNAD : ¬(CN.intersectsLine AD)) (hCNBE : ¬(CN.intersectsLine BE))
    (hADCN : AD ≠ CN) (hCNBEne : CN ≠ BE)
    (hadcn : a.sameSide d CN) :
    between d n e := by
  euclid_intros
  have step11_bse : b.sameSide e CN := by euclid_apply (helper_2_7_step11_bse b e BE CN (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show CN ≠ BE; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine BE); assumption)))
  euclid_apply (pasch_3 a c b CN)
  euclid_apply (pasch_4 d n e CN DE)
  euclid_finish

end Elements.Book2
