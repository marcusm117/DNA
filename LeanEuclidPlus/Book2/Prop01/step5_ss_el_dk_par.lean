import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.5: EL ∦ DK, because both are parallel to BF (proposition_30). The line
   distinctness preconditions are established from the BC anchor points b,d,e (distinct) and the
   off-BC anchors f on BF, l on EL, k on DK. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5_ss_el_dk_par (b d e f k l : Point) (BC BF DK EL : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hloffBC : ¬(l.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hkoffBC : ¬(k.onLine BC))
    (hDKBF : ¬(DK.intersectsLine BF)) (hELBF : ¬(EL.intersectsLine BF)) :
    ¬(EL.intersectsLine DK) := by
  euclid_intros
  have hELDK : EL ≠ DK := by euclid_finish
  have hDKBF' : DK ≠ BF := by euclid_finish
  have hBFEL : BF ≠ EL := by euclid_finish
  euclid_apply (proposition_30 EL DK BF)
  euclid_finish

end Elements.Book2
