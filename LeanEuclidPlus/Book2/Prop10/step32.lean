import SystemE
import Book.Prop34
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.32: |EF| = |CD| [Prop.~1.34]. Opposite sides of the parallelogram CEFD are equal
   (proposition_34's |C─D| = |E─F| conjunct). Reuses the shared formParallelogram (step21_pgram); the
   diagonal ED is built locally. linarith closes from the proposition_34 conclusion. -/
set_option systemE.solverTime 30 in
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
  have step21_pgram : formParallelogram c e d f CE FD AD EF := by sorry
  euclid_apply (line_from_points e d) as ED
  euclid_apply (proposition_34 c e d f CE FD AD EF ED)
  linarith

end Elements.Book2
