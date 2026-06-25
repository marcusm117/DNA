import SystemE
import Book2.Prop07.step3_ahcf
import Book2.Prop07.step4_fsb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: g (= CN ∩ HF) is between h and f on HF. The vertical line CN separates h from f:
   a, b are on opposite sides of CN (c ∈ CN is between a and b on AB, pasch_3); a and h are on the
   same side of CN (both on AD ∥ CN, step3_ahcf); f and b are on the same side of CN (both on
   BE ∥ CN, step4_fsb); hence h and f are on opposite sides of CN, and the crossing point g of HF
   with CN lies between them (pasch_4). -/
theorem helper_2_7_step4_hgf (a b c d h g f : Point) (AB CN AD BE HF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hhHF : h.onLine HF) (hgHF : g.onLine HF) (hfHF : f.onLine HF)
    (hCNAD : ¬(CN.intersectsLine AD)) (hCNBE : ¬(CN.intersectsLine BE))
    (hADCN : AD ≠ CN) (hCNBEne : CN ≠ BE) :
    between h g f := by
  euclid_intros
  have step3_ahcf : a.sameSide h CN := by euclid_apply (helper_2_7_step3_ahcf a h AD CN (by assumption) (by assumption) (by assumption) (by assumption))
  have step4_fsb : f.sameSide b CN := by euclid_apply (helper_2_7_step4_fsb f b BE CN (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (pasch_3 a c b CN)
  euclid_apply (pasch_4 h g f CN HF)
  euclid_finish

end Elements.Book2
