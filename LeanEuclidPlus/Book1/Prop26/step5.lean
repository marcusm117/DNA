import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step5
    (a b c d e f g : Point) (AB BC DE EF DF GC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
    (hAB_BC : AB ≠ BC) (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (hg_GC : g.onLine GC) (hc_GC : c.onLine GC)
    (hbetween : between b g a)
    (hlen1 : |(b─g)| = |(d─e)|) (hlen2 : |(b─c)| = |(e─f)|)
    (hang : ∠ g:b:c = ∠ d:e:f) :
    |(g─c)| = |(d─f)| := by
  euclid_apply (proposition_4 b g c e d f AB GC BC DE DF EF)
  euclid_finish

end Elements.Book1
