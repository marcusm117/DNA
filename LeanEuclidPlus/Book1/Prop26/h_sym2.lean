import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop16
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_h_sym2
    (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hf_DF : f.onLine DF) (hd_DF : d.onLine DF)
    (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (hang1 : ∠ a:b:c = ∠ d:e:f)
    (hang2 : ∠ b:c:a = ∠ e:f:d)
    (hstep19 : |(a─b)| = |(d─e)|)
    (hstep24 : |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)|)
    (hgt2 : ¬|(b─c)| > |(e─f)|) : False := by
  have hlt2 : |(e─f)| > |(b─c)| := by
    rcases hstep24 with h | h
    · exact absurd h hgt2
    · exact h
  euclid_apply (proposition_3 e f b c EF BC) as h'
  euclid_apply (line_from_points d h') as DH'
  euclid_apply (proposition_4 b a c e d h' AB AC BC DE DH' EF)
  euclid_apply (proposition_16 d f h' e DF EF DH')
  euclid_finish

end Elements.Book1
