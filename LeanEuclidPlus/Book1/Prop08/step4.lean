import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step4
  (a b c d e f c' g : Point)
  (EF EG GF DE DF : Line)
  (ptImg : Point → Point)
  (h_ptImg_c : ptImg c = c')
  (hc'_GF : c'.onLine GF) (hg_GF : g.onLine GF)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
  (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
  (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
  (hne_eg : e ≠ g) (hne_c'g : c' ≠ g) (hne_de : d ≠ e)
  (hne_efdf : EF ≠ DF) (hne_dfde : DF ≠ DE)
  (h_ab_de : |(a─b)| = |(d─e)|) (h_ab_ge : |(a─b)| = |(g─e)|)
  (h_ca_c'g : |(c─a)| = |(c'─g)|) (h_ac_df : |(a─c)| = |(d─f)|)
  (step1 : ptImg c = f)
  : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧
    distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)| := by
  have hcf : c' = f := by rw [← h_ptImg_c]; exact step1
  clear step1 h_ptImg_c ptImg
  subst hcf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
