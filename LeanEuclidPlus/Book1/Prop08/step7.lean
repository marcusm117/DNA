import SystemE
import Book1.Prop07.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step7
  (d e f g : Point) (DE EF DF EG GF : Line)
  (hd_DE : d.onLine DE) (hd_DF : d.onLine DF)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hf_DF : f.onLine DF)
  (hne_de : d ≠ e)
  (hne_deef : DE ≠ EF) (hne_efdf : EF ≠ DF) (hne_dfde : DF ≠ DE)
  (step4 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧
           distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|)
  (step5 : g ≠ d ∧ g.sameSide d EF)
  (step6 : (e.onLine EG ∧ e.onLine DE) ∧ f.onLine GF ∧ f.onLine DF)
  : False := by
  euclid_apply (proposition_7 e f d g EF DE DF EG GF)
  euclid_finish

end Elements.Book1
