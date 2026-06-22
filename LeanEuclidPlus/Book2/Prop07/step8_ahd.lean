import SystemE
import Book2.Prop07.step8_abhf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: h (= HF ∩ AD) is between a and d on AD. The horizontal line HF separates a from d:
   b and d are on opposite sides of HF (g ∈ HF is between b and d on BD, step3_bgd + pasch_3);
   a and b are on the same side of HF (both on AB ∥ HF, step8_abhf); hence a and d are on opposite
   sides of HF, and the crossing point h of AD with HF lies between them (pasch_4). -/
theorem helper_2_7_step8_ahd (a b d g h : Point) (AB HF BD AD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF)
    (haAD : a.onLine AD) (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hHFAB : ¬(HF.intersectsLine AB)) (hABHF : AB ≠ HF)
    (hbgd : between b g d) :
    between a h d := by
  euclid_intros
  have step8_abhf : a.sameSide b HF := by euclid_apply (helper_2_7_step8_abhf a b AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (pasch_3 b g d HF)
  euclid_apply (pasch_4 a h d HF AD)
  euclid_finish

end Elements.Book2
