import SystemE
import Book2.Prop07.step3_cab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.9 sub: c, g, b form a triangle with sides CN (c,g), BD (g,b), AB (b,c). Pairwise line
   distinctness: AB ≠ CN (g ∈ CN, g ∉ AB since g ∈ HF ∥ AB); CN ≠ BD (share g; c ∈ CN ∩ AB would
   force AB = BD, contradicting d); BD ≠ AB (d ∈ BD, d ∉ AB). -/
theorem helper_2_7_step9_tri (a b c d g : Point) (AB CN AD BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hCNAD : ¬(CN.intersectsLine AD))
    (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟)
    (hgnAB : ¬(g.onLine AB)) :
    formTriangle c g b CN BD AB := by
  euclid_intros
  have step3_cab : c.onLine AB := by euclid_apply (helper_2_7_step3_cab a b c AB (by assumption) (by assumption) (by assumption))
  have hbc : b ≠ c := by euclid_finish
  have hcg : c ≠ g := fun hh => hgnAB (hh ▸ step3_cab)
  euclid_finish

end Elements.Book2
