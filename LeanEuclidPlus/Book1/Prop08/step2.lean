import SystemE
import Book.Prop07
import Book1.Prop08.step2_gd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
open Classical

namespace Elements.Book1

theorem helper_1_8_step2
  (a b c d e f c' g : Point)
  (AB BC AC DE EF DF EG GF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (h_ptImg_c : ptImg c = c')
  (h_lineImg_AB : lineImg AB = EG) (h_lineImg_AC : lineImg AC = GF)
  (hassump1 : lineImg BC = EF)
  (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
  (hg_GF : g.onLine GF) (hc'_GF : c'.onLine GF)
  (hc'_EF : c'.onLine EF)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hg_ss_d : g.sameSide d EF)
  (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
  (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
  (hne_eg : e ≠ g) (hne_de : d ≠ e) (hne_c'g : c' ≠ g)
  (hne_deef : DE ≠ EF) (hne_efdf : EF ≠ DF) (hne_dfde : DF ≠ DE)
  (h_ab_de : |(a─b)| = |(d─e)|) (h_ab_ge : |(a─b)| = |(g─e)|)
  (h_ca_c'g : |(c─a)| = |(c'─g)|) (h_ac_df : |(a─c)| = |(d─f)|)
  (step1 : ptImg c = f)
  : lineImg AB = DE ∧ lineImg AC = DF := by
  rw [h_lineImg_AB, h_lineImg_AC]
  have hcf : c' = f := by rw [← h_ptImg_c]; exact step1
  clear step1 h_ptImg_c hassump1 h_lineImg_AB h_lineImg_AC
  clear ptImg lineImg
  subst hcf
  have step2_gd : g = d := by euclid_apply (helper_1_8_step2_gd a b c d e c' g DE EF DF EG GF (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show c'.onLine GF; assumption)) (by euclid_assumption "" (show c'.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show c'.onLine EF; assumption)) (by euclid_assumption "" (show g.sameSide d EF; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show c'.onLine DF; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show c' ≠ g; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(g─e)|; assumption)) (by euclid_assumption "" (show |(c─a)| = |(c'─g)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(d─c')|; assumption)))
  subst step2_gd
  constructor <;> euclid_finish

end Elements.Book1
