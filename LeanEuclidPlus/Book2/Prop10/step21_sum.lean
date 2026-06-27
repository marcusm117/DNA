import SystemE
import Book.Prop32
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.21 sub: the three angles of △EFG sum to ∟+∟ (proposition_32). The triangle side EG is built
   locally (line_from_points e g). The raw sum is reoriented to ∠f:e:g + ∠e:f:g + ∠e:g:f via
   angle_symm so the parent's linarith can use it directly. No ∟/2 facts here (pure geometry). -/
theorem helper_2_10_step21_sum
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD) (hf_fd : f.onLine FD)
  (hg_eb : g.onLine EB) (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE) :
  ∠ f:e:g + ∠ e:f:g + ∠ e:g:f = ∟ + ∟ := by
  euclid_apply (line_from_points e g) as EG
  have hef : e ≠ f := by euclid_finish
  have hfg : f ≠ g := by euclid_finish
  have hge : g ≠ e := by euclid_finish
  have hfg_dist : distinctPointsOnLine f g FD := ⟨hf_fd, hg_fd, hfg⟩
  obtain ⟨e2, he2on, hbe2⟩ := extend_point FD f g hfg_dist
  have hftri : formTriangle e f g EF FD EG := by euclid_finish
  have hraw : ∠ e:f:g + ∠ f:g:e + ∠ g:e:f = ∟ + ∟ := by
    euclid_apply (proposition_32 e f g e2 EF FD EG)
    euclid_finish
  have hs1 : ∠ f:g:e = ∠ e:g:f := angle_symm f g e ⟨hfg, hge⟩
  have hs2 : ∠ g:e:f = ∠ f:e:g := angle_symm g e f ⟨hge, hef⟩
  linarith [hraw, hs1, hs2]

end Elements.Book2
