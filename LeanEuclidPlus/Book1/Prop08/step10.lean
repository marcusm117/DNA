import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step10
  (a b c c' d e f g : Point) (AB AC BC DE EF DF EG GF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (h_ptImg_c : ptImg c = c')
  (h_lineImg_AB : lineImg AB = EG) (h_lineImg_AC : lineImg AC = GF)
  (h_angle : ∠ b:a:c = ∠ e:g:c')
  (hg_EG : g.onLine EG) (hg_GF : g.onLine GF)
  (hd_DE : d.onLine DE) (hd_DF : d.onLine DF)
  (hc'_EF : c'.onLine EF) (hc'_GF : c'.onLine GF)
  (hf_EF : f.onLine EF) (hf_DF : f.onLine DF)
  (hne_eg : e ≠ g) (hne_de : d ≠ e)
  (hne_dfde : DF ≠ DE) (hne_efdf : EF ≠ DF)
  (step1 : ptImg c = f)
  (step9 : lineImg AB = DE ∧ lineImg AC = DF)
  : ∠ b:a:c = ∠ e:d:f := by
  have hEGDE : EG = DE := by rw [← h_lineImg_AB]; exact step9.1
  have hGFDF : GF = DF := by rw [← h_lineImg_AC]; exact step9.2
  have hcf : c' = f := by rw [← h_ptImg_c]; exact step1
  clear step1 h_ptImg_c ptImg step9 h_lineImg_AB h_lineImg_AC lineImg
  have hgd : g = d := by euclid_finish
  rw [hgd, hcf] at h_angle
  exact h_angle

end Elements.Book1
