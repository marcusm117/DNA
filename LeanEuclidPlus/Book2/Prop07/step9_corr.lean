import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.9 sub: ∠ c:g:b = ∠ a:d:b. CN (through g, c) ∥ AD (through d, a), cut by transversal BD
   (through b, g, d) with foot g between b and d and c, a on the same side of BD. proposition_29''''
   gives ∠ b:g:c = ∠ g:d:a; angle symmetry plus equal_angles rewrite this to ∠ c:g:b = ∠ a:d:b. -/
theorem helper_2_7_step9_corr (a b c d g : Point) (CN AD BD : Line)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (had : a ≠ d) (hgd : g ≠ d)
    (hbgd : between b g d) (hcaBD : c.sameSide a BD)
    (hCNAD : ¬(CN.intersectsLine AD)) :
    ∠ c:g:b = ∠ a:d:b := by
  euclid_intros
  have hcorr : ∠ b:g:c = ∠ g:d:a := by
    euclid_apply (proposition_29'''' c a b g d CN AD BD)
    euclid_finish
  have hray : ∠ g:d:a = ∠ b:d:a := by
    euclid_apply (equal_angles d g b a a BD AD)
    euclid_finish
  have hsg : (∠ c:g:b : ℝ) = ∠ b:g:c := angle_symm c g b ⟨by euclid_finish, by euclid_finish⟩
  have hsd : (∠ b:d:a : ℝ) = ∠ a:d:b := angle_symm b d a ⟨hbd, fun h => had h.symm⟩
  rw [hsg, hcorr, hray, hsd]

end Elements.Book2
