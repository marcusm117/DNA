import SystemE
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step28
    (a b c d e f h : Point) (AB BC AH DE EF DF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
    (hAB_BC : AB ≠ BC) (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hbetween : between b h c)
    (hstep26 : |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|)
    (hstep27 : ∠ a:b:h = ∠ d:e:f) :
    |(a─h)| = |(d─f)| := by
  euclid_apply (proposition_4 b a h e d f AB AH BC DE DF EF)
  euclid_finish

end Elements.Book1
