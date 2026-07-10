import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.8: DK ∦ EL, because both are parallel to BF (proposition_30). The line
   distinctness preconditions are established from the BC anchor points b,d,e (distinct, from the
   order b-d-e-c) and the off-BC anchors f on BF, k on DK, l on EL. -/
theorem helper_2_1_step8_pgram_par (b d e f k l : Point) (BC BF DK EL : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hkoffBC : ¬(k.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hloffBC : ¬(l.onLine BC))
    (hDKBF : ¬(DK.intersectsLine BF)) (hELBF : ¬(EL.intersectsLine BF)) :
    ¬(DK.intersectsLine EL) := by
  euclid_intros
  have hbd : b ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hDKEL : DK ≠ EL := by euclid_finish
  have hELBF' : EL ≠ BF := by euclid_finish
  have hBFDK : BF ≠ DK := by euclid_finish
  euclid_apply (proposition_30 DK EL BF)
  euclid_finish

end Elements.Book2
