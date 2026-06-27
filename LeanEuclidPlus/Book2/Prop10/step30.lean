import SystemE
import Book.Prop47
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.30: square on EG = squares on GF + FE [Prop.~1.47]. △EGF is right-angled at F (∠e:f:g = ∟),
   so proposition_47 gives |e─g|² = |e─f|² + |f─g|². The right angle + parallelogram CEFD are REUSED
   shared helpers (step21_fright consumes step21_pgram). The triangle side EG is local; segment symmetry
   (hef2, hgf2) reconciles orientations; linarith (no args) uses the prop_47 conclusion `h` + them. -/
set_option systemE.solverTime 30 in
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
  have step21_pgram : formParallelogram c e d f CE FD AD EF := by sorry
  have step21_fright : ∠ e:f:g = ∟ := by sorry
  euclid_apply (line_from_points e g) as EG
  have hef2 : |(e─f)| * |(e─f)| = |(f─e)| * |(f─e)| := by rw [segment_symmetric e f]
  have hgf2 : |(f─g)| * |(f─g)| = |(g─f)| * |(g─f)| := by rw [segment_symmetric f g]
  euclid_apply (proposition_47 f e g EF EG FD)
  linarith

end Elements.Book2
