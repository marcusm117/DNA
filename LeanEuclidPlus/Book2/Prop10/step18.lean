import SystemE
import Book.Prop32
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

/- 2.10.18: ∠DGB = ∟/2. Remaining angle of △BDG: the three angles sum to ∟+∟ (proposition_32), with
   ∠DBG = ∟/2 (step16) and ∠BDG = ∟ (step17), so ∠DGB = (∟+∟) − ∟ − ∟/2 = ∟/2. The formTriangle
   fact is its own sub-node (step18_tri, rich context for the line-distinctness). KEEP ∟/2 OUT OF THE
   SMT: clear it for every euclid_finish block (it crashes the translator); linarith re-uses it. -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step18
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hdbg : ∠ d:b:g = ∟ / 2)
  (hbdg : ∠ b:d:g = ∟) :
  ∠ d:g:b = ∟ / 2 := by
  have step18_tri : formTriangle g b d EB AD FD := by sorry
  have hbd : b ≠ d := by clear hdbg; euclid_finish
  have hbd_dist : distinctPointsOnLine b d AD := ⟨hab_b, hab_d, hbd⟩
  obtain ⟨d2, hd2on, hbd2⟩ := extend_point AD b d hbd_dist
  have hsum : ∠ g:b:d + ∠ b:d:g + ∠ d:g:b = ∟ + ∟ := by
    clear hdbg
    euclid_apply (proposition_32 g b d d2 EB AD FD)
    euclid_finish
  have hgb : g ≠ b := by clear hdbg; euclid_finish
  have hs : ∠ g:b:d = ∠ d:b:g := angle_symm g b d ⟨hgb, hbd⟩
  linarith [hsum, hs, hdbg, hbdg]

end Elements.Book2
