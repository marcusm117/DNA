import SystemE
import Book.Prop06
import Book2.Prop04.step8_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.8: |(b─c)| = |(c─g)|. In triangle c,g,b (sides c─g on CF, g─b on BD, b─c on AB) the base
   angles at g and b are equal — ∠ c:g:b = ∠ g:b:c (step7), recast to ∠ c:g:b = ∠ c:b:g by symmetry
   — so the sides subtending them are equal: |c─g| = |c─b| [Prop.~1.6], i.e. |b─c| = |c─g|.
   The triangle's three lines are pairwise distinct (sub-nodes derive CF≠BD, BD≠AB, AB≠CF from the
   parallels HK∥AB and the perpendiculars). -/
theorem helper_2_4_step8 (a b c d g h : Point) (AB CF AD BD HK : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hHKAB : ¬(HK.intersectsLine AB))
    (hbd : b ≠ d) (hab : a ≠ b)
    (hadab : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hCFAD : ¬(CF.intersectsLine AD))
    (hstep7 : ∠ c:g:b = ∠ g:b:c) :
    |(b─c)| = |(c─g)| := by
  euclid_intros
  -- a ≠ d (side a─d = a─b > 0)
  have had : a ≠ d := by euclid_finish
  -- the triangle c,g,b (sides CF, BD, AB) — its formation also pins b≠c, c≠g, b≠g
  have step8_tri : formTriangle c g b CF BD AB := by euclid_apply (helper_2_4_step8_tri a b c d g AB CF AD BD HK (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  -- recast step7 into prop6's base-angle form: ∠ c:g:b = ∠ c:b:g
  have hbase : ∠ c:g:b = ∠ c:b:g := by
    have hbc : b ≠ c := by euclid_finish
    have hbg : b ≠ g := by euclid_finish
    have hsym : (∠ g:b:c : ℝ) = ∠ c:b:g := angle_symm g b c ⟨hbg.symm, hbc⟩
    rw [hstep7, hsym]
  euclid_apply (proposition_6 c g b CF BD AB)
  euclid_finish

end Elements.Book2
