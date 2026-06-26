import SystemE
import Book2.Prop07.step9_bfbc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.9: BF is equal to BC. The argument lives in the shared core step9_bfbc (reused by 2.7.8). -/
theorem helper_2_7_step9 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCNAD : ¬(CN.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    |(b─f)| = |(b─c)| := by
  euclid_intros
  have step9_bfbc : |(b─f)| = |(b─c)| := by euclid_apply (helper_2_7_step9_bfbc a b c d e n g h f AB CN AD BE HF BD DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show n.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show n.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show f.onLine HF; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  exact step9_bfbc

end Elements.Book2
