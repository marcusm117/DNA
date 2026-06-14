import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.5: CH ∦ EL, because both are parallel to BF (proposition_30). The line
   distinctness preconditions are established from the BC anchor points: CH meets BC at c, EL at
   e, BF at b, with b,c,e distinct (and f on BF off BC, h on CH off BC anchor the verticals). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5_ss_ch_el_par (b c e f h : Point) (BC BF EL CH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbc : b ≠ c) (hbe : b ≠ e) (hec : e ≠ c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hhoffBC : ¬(h.onLine BC))
    (heEL : e.onLine EL)
    (hCHBF : ¬(CH.intersectsLine BF)) (hELBF : ¬(EL.intersectsLine BF)) :
    ¬(CH.intersectsLine EL) := by
  euclid_intros
  have hCHEL : CH ≠ EL := by euclid_finish
  have hELBF' : EL ≠ BF := by euclid_finish
  have hBFCH : BF ≠ CH := by euclid_finish
  euclid_apply (proposition_30 CH EL BF)
  euclid_finish

end Elements.Book2
