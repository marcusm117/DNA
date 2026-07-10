import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
import Mathlib.Tactic.Linarith
import Book2.Prop10.step21_pgram
import Book2.Prop10.step21_fright
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.30: square on EG = squares on GF + FE [Prop.~1.47]. △EGF is right-angled at F (∠e:f:g = ∟),
   so proposition_47 gives |e─g|² = |e─f|² + |f─g|². The right angle + parallelogram CEFD are REUSED
   shared helpers (step21_fright consumes step21_pgram). The triangle side EG is local; segment symmetry
   (hef2, hgf2) reconciles orientations; linarith (no args) uses the prop_47 conclusion `h` + them. -/
theorem helper_2_10_step30
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hg_eb : g.onLine EB) (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hright : ∠ a:c:e = ∟) :
  |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| := by
  have step21_pgram : formParallelogram c e d f CE FD AD EF := by euclid_apply (helper_2_10_step21_pgram a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)))
  have step21_fright : ∠ e:f:g = ∟ := by euclid_apply (helper_2_10_step21_fright a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show formParallelogram c e d f CE FD AD EF; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))
  euclid_apply (line_from_points e g) as EG
  have hef2 : |(e─f)| * |(e─f)| = |(f─e)| * |(f─e)| := by rw [segment_symmetric e f]
  have hgf2 : |(f─g)| * |(f─g)| = |(g─f)| * |(g─f)| := by rw [segment_symmetric f g]
  euclid_apply (proposition_47 f e g EF EG FD)
  linarith

end Elements.Book2
