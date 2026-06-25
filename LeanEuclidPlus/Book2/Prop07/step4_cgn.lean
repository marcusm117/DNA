import SystemE
import Book2.Prop07.step3_bchk
import Book2.Prop07.step4_nsd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: g (= CN ∩ HF) is between c and n on CN. The horizontal line HF separates c from n:
   b and d are on opposite sides of HF (g ∈ HF is between b and d on BD, step3_bgd + pasch_3);
   c and b are on the same side of HF (both on AB ∥ HF, step3_bchk); n and d are on the same side
   of HF (both on DE ∥ HF, step4_nsd); hence c and n are on opposite sides of HF, and the crossing
   point g of CN with HF lies between them (pasch_4). -/
theorem helper_2_7_step4_cgn (b c d n g : Point) (AB DE HF BD CN : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hnDE : n.onLine DE) (hdDE : d.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hcCN : c.onLine CN) (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (hHFAB : ¬(HF.intersectsLine AB)) (hHFDE : ¬(HF.intersectsLine DE))
    (hABHF : AB ≠ HF) (hHFDEne : HF ≠ DE)
    (hbgd : between b g d) :
    between c g n := by
  euclid_intros
  have step3_bchk : b.sameSide c HF := by euclid_apply (helper_2_7_step3_bchk b c AB HF (by assumption) (by assumption) (by assumption) (by assumption))
  have step4_nsd : n.sameSide d HF := by euclid_apply (helper_2_7_step4_nsd n d DE HF (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (pasch_3 b g d HF)
  euclid_apply (pasch_4 c g n HF CN)
  euclid_finish

end Elements.Book2
