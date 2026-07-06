import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step40
    (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
    (hAB_BC : AB ≠ BC) (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (hstep37 : |(a─b)| = |(d─e)|)
    (hstep36 : |(b─c)| = |(e─f)|)
    (hstep39 : ∠ a:b:c = ∠ d:e:f) :
    |(a─c)| = |(d─f)| := by
  euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
  euclid_finish

end Elements.Book1
