import SystemE
import Book1.Prop24.Main
import Book3.Prop07.step7_tri_ecf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step8
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
  have step7_tri_ecf : formTriangle e c f CE CF AD := by euclid_apply (helper_3_7_step7_tri_ecf ABCD a d e f c AD CE CF (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)))
  euclid_apply (Elements.Book1.proposition_24 e b f e c f BE BF AD CE CF AD)
  assumption

end Elements.Book3
