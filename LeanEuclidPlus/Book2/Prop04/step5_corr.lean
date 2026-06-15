import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.5 sub: ∠ c:g:b = ∠ a:d:b. CF (through g, c) ∥ AD (through d, a), cut by transversal BD
   (through b, g, d) with foot g between b and d and c, a on the same side of BD. proposition_29''''
   gives ∠ b:g:c = ∠ g:d:a (external = interior-opposite); angle symmetry (at g) plus equal_angles
   (ray d→g coincides with d→b, since g is between b and d) rewrite this to ∠ c:g:b = ∠ a:d:b. -/
theorem helper_2_4_step5_corr (a b c d g : Point) (CF AD BD : Line)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (had : a ≠ d) (hgd : g ≠ d)
    (hbgd : between b g d) (hcaBD : c.sameSide a BD)
    (hCFAD : ¬(CF.intersectsLine AD)) :
    ∠ c:g:b = ∠ a:d:b := by
  euclid_intros
  -- corresponding angles: ∠ b:g:c = ∠ g:d:a
  have hcorr : ∠ b:g:c = ∠ g:d:a := by
    euclid_apply (proposition_29'''' c a b g d CF AD BD)
    euclid_finish
  -- ray d→g coincides with d→b (g between b, d), so ∠ g:d:a = ∠ b:d:a
  have hray : ∠ g:d:a = ∠ b:d:a := by
    euclid_apply (equal_angles d g b a a BD AD)
    euclid_finish
  -- symmetries: ∠ c:g:b = ∠ b:g:c and ∠ b:d:a = ∠ a:d:b
  have hsg : (∠ c:g:b : ℝ) = ∠ b:g:c := angle_symm c g b ⟨by euclid_finish, by euclid_finish⟩
  have hsd : (∠ b:d:a : ℝ) = ∠ a:d:b := angle_symm b d a ⟨hbd, fun h => had h.symm⟩
  rw [hsg, hcorr, hray, hsd]

end Elements.Book2
