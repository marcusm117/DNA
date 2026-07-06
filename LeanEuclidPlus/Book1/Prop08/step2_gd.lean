import SystemE
import Book1.Prop07.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
open Classical

namespace Elements.Book1

theorem helper_1_8_step2_gd
  (a b c d e c' g : Point)
  (DE EF DF EG GF : Line)
  (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
  (hg_GF : g.onLine GF) (hc'_GF : c'.onLine GF)
  (hc'_EF : c'.onLine EF)
  (he_EF : e.onLine EF) (hf_EF : c'.onLine EF)
  (hg_ss_d : g.sameSide d EF)
  (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
  (hd_DF : d.onLine DF) (hf_DF : c'.onLine DF)
  (hne_eg : e ≠ g) (hne_de : d ≠ e) (hne_c'g : c' ≠ g)
  (hne_deef : DE ≠ EF) (hne_efdf : EF ≠ DF) (hne_dfde : DF ≠ DE)
  (h_ab_de : |(a─b)| = |(d─e)|) (h_ab_ge : |(a─b)| = |(g─e)|)
  (h_ca_c'g : |(c─a)| = |(c'─g)|) (h_ac_df : |(a─c)| = |(d─c')|)
  : g = d := by
  by_contra hgd
  have hgd' : g ≠ d := hgd
  euclid_apply (proposition_7 e c' d g EF DE DF EG GF)
  euclid_finish

end Elements.Book1
