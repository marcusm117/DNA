import SystemE
import Book.Prop03
import Book.Prop04
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_26_h_sym
    (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hf_DF : f.onLine DF) (hd_DF : d.onLine DF)
    (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (hang1 : ∠ a:b:c = ∠ d:e:f) (hang2 : ∠ b:c:a = ∠ e:f:d)
    (hbc : |(b─c)| = |(e─f)|)
    (hstep1 : |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|)
    (hgt : ¬|(a─b)| > |(d─e)|) :
    False := by sorry

end Elements.Book1
