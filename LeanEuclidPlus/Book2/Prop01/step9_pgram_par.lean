import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.9: EL ∦ CH, because both are parallel to BF (proposition_30). The line
   distinctness preconditions are established from the BC anchor points b,e,c (distinct, from the
   order b-d-e-c) and the off-BC anchors f on BF, l on EL, h on CH. -/
theorem helper_2_1_step9_pgram_par (b c d e f h l : Point) (BC BF EL CH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hloffBC : ¬(l.onLine BC))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hhoffBC : ¬(h.onLine BC))
    (hELBF : ¬(EL.intersectsLine BF)) (hCHBF : ¬(CH.intersectsLine BF)) :
    ¬(EL.intersectsLine CH) := by
  euclid_intros
  have hbe : b ≠ e := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hec : e ≠ c := by euclid_finish
  have hELCH : EL ≠ CH := by euclid_finish
  have hCHBF' : CH ≠ BF := by euclid_finish
  have hBFEL : BF ≠ EL := by euclid_finish
  euclid_apply (proposition_30 EL CH BF)
  euclid_finish

end Elements.Book2
