import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_25_step3
    (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_aneb : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABneBC : AB ≠ BC) (h_BCneAC : BC ≠ AC) (h_ACneAB : AC ≠ AB)
    (h_dDE : d.onLine DE) (h_eDE : e.onLine DE) (h_dne : d ≠ e)
    (h_eEF : e.onLine EF) (h_fEF : f.onLine EF)
    (h_fDF : f.onLine DF) (h_dDF : d.onLine DF)
    (h_DEneEF : DE ≠ EF) (h_EFneDF : EF ≠ DF) (h_DFneDE : DF ≠ DE)
    (h_ab_de : |(a─b)| = |(d─e)|)
    (h_ac_df : |(a─c)| = |(d─f)|)
    (h_eq : ∠ b:a:c = ∠ e:d:f) :
    |(b─c)| = |(e─f)| := by
  euclid_apply (proposition_4 a b c d e f AB BC AC DE EF DF)
  euclid_finish

end Elements.Book1
