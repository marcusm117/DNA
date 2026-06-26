import SystemE
import Book.Prop34
import Book2.Prop01.step9_len_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.9: |e─l| = |a₁a₂|. BGLE is a parallelogram (rails BC at b,e and GH at g,l;
   sides BF at b,g and EL at e,l), so opposite sides |b─g| = |e─l| (proposition_34'); and
   |b─g| = |a₁a₂| (step2). The parallelogram is supplied as the sub-node step9_len_pgram. -/
theorem helper_2_1_step9_len (a₁ a₂ b d e f g l : Point) (BC GH BF EL : Line)
    (hbg : |(b─g)| = |(a₁─a₂)|)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e)
    (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hlGH : l.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hbBF : b.onLine BF) (hf'BF : f'.onLine BF) (hbgf' : between b g f')
    (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF)) :
    |(e─l)| = |(a₁─a₂)| := by
  euclid_intros
  euclid_apply (between_same_line_in b g f' BF)
  have step9_len_pgram : formParallelogram b e g l BC GH BF EL := by euclid_apply (helper_2_1_step9_len_pgram b d e f g l BC GH BF EL (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(g.onLine BC); assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)))
  euclid_apply (proposition_34' b e g l BC GH BF EL)
  euclid_finish

end Elements.Book2
