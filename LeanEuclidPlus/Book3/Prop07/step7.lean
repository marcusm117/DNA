import SystemE
import Book1.Prop24.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step7
    (ABCD : Circle) (a d e f b c : Point) (AD CE BE BF : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hc : c.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (h_tri_ebf : formTriangle e b f BE BF AD)
    (h_eq_bc : |(e─b)| = |(e─c)|)
    (h_ang : ∠ b:e:f > ∠ c:e:f)
    (h_cne_a : c ≠ a) (h_cne_d : c ≠ d)
    : |(b─f)| > |(c─f)| := by
  euclid_apply (line_from_points c f) as CF
  have step7_tri_ecf : formTriangle e c f CE CF AD := by sorry
  have h24 := Elements.Book1.proposition_24 e b f e c f BE BF AD CE CF AD
  euclid_finish

end Elements.Book3
