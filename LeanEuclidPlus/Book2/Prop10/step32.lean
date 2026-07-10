import SystemE
import Book1Variants.Prop34
import Mathlib.Tactic.Linarith
import Book2.Prop10.step21_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.32: |EF| = |CD| [Prop.~1.34]. Opposite sides of the parallelogram CEFD are equal
   (proposition_34's |C─D| = |E─F| conjunct). Reuses the shared formParallelogram (step21_pgram); the
   diagonal ED is built locally. linarith closes from the proposition_34 conclusion. -/
theorem helper_2_10_step32
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE) :
  |(e─f)| = |(c─d)| := by
  have step21_pgram : formParallelogram c e d f CE FD AD EF := by euclid_apply (helper_2_10_step21_pgram a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)))
  euclid_apply (line_from_points e d) as ED
  euclid_apply (proposition_34 c e d f CE FD AD EF ED)
  linarith

end Elements.Book2
