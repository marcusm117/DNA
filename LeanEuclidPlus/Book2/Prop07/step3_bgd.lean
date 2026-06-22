import SystemE
import Book2.Prop07.step3_bgd_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: g (= CN ∩ BD) is between b and d on the diagonal BD. CN (vertical through c) separates
   b from d: c is between a and b on AB so a, b are on opposite sides of CN (pasch_3); a, d are on the
   same side of CN (step3_bgd_ss); hence b, d on opposite sides of CN, and the crossing point g of BD
   with CN lies between them (pasch_4). -/
theorem helper_2_7_step3_bgd (a b c d g : Point) (AB CN AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d) (hbad : ∠ b:a:d = ∟)
    (hCNAD : ¬(CN.intersectsLine AD)) :
    between b g d := by
  euclid_intros
  have step3_bgd_ss : a.sameSide d CN := by euclid_apply (helper_2_7_step3_bgd_ss a b c d AB CN AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (pasch_3 a c b CN)
  euclid_apply (pasch_4 b g d CN BD)
  euclid_finish

end Elements.Book2
