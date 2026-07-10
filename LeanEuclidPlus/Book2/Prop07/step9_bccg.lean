import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.7.9 sub: |(b─c)| = |(c─g)|. In triangle c,g,b (sides c─g on CN, g─b on BD, b─c on AB) the base
   angles at g and b are equal — ∠ c:g:b = ∠ g:b:c (step9_cgb), recast to ∠ c:g:b = ∠ c:b:g by
   symmetry — so the subtending sides are equal: |c─g| = |c─b| [Prop.~1.6], i.e. |b─c| = |c─g|. -/
theorem helper_2_7_step9_bccg (a b c d g : Point) (AB CN AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbd : b ≠ d) (hab : a ≠ b)
    (hadab : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hCNAD : ¬(CN.intersectsLine AD))
    (hstep9_tri : formTriangle c g b CN BD AB)
    (hstep7 : ∠ c:g:b = ∠ g:b:c) :
    |(b─c)| = |(c─g)| := by
  euclid_intros
  have had : a ≠ d := by euclid_finish
  have step9_tri : formTriangle c g b CN BD AB := hstep9_tri
  have hbase : ∠ c:g:b = ∠ c:b:g := by
    have hbc : b ≠ c := by euclid_finish
    have hbg : b ≠ g := by euclid_finish
    have hsym : (∠ g:b:c : ℝ) = ∠ c:b:g := angle_symm g b c ⟨hbg.symm, hbc⟩
    rw [hstep7, hsym]
  euclid_apply (proposition_6 c g b CN BD AB)
  euclid_finish

end Elements.Book2
