import SystemE
import Book2.Prop04.step5_bgd_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.5 sub: g (= CF ∩ BD) is between b and d on the diagonal BD. CF (vertical through c) separates
   b from d: c is between a and b on AB so a, b are on opposite sides of CF (pasch_3); a, d are on the
   same side of CF (both on AD, which is parallel to CF); hence b, d on opposite sides of CF, and the
   crossing point g of BD with CF lies between them (pasch_4). -/
theorem helper_2_4_step5_bgd (a b c d g : Point) (AB CF AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d) (hbad : ∠ b:a:d = ∟)
    (hCFAD : ¬(CF.intersectsLine AD)) :
    between b g d := by
  euclid_intros
  have step5_bgd_ss : a.sameSide d CF := by euclid_apply (helper_2_4_step5_bgd_ss a b c d AB CF AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- a, b on opposite sides of CF (c between them, c on CF)
  euclid_apply (pasch_3 a c b CF)
  euclid_apply (pasch_4 b g d CF BD)
  euclid_finish

end Elements.Book2
