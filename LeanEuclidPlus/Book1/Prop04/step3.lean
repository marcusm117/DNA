import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step3
  (a b c d e f : Point) (b' c' : Point) (AC DC' DE DF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (hassump1 : |(a─c)| = |(d─f)|)
  (h_ca_dc' : |(c─a)| = |(c'─d)|)
  (h_ang_bac : ∠ b:a:c = ∠ b':d:c')
  (h_ang_edf : ∠ b:a:c = ∠ e:d:f)
  (h_c'_sameSide : c'.sameSide f DE)
  (h_d_on_DE : d.onLine DE)
  (h_b'_on_DE : b'.onLine DE)
  (h_d_ne_e : d ≠ e)
  (h_d_on_DC' : d.onLine DC')
  (h_c'_on_DC' : c'.onLine DC')
  (h_d_ne_c' : d ≠ c')
  (h_d_on_DF : d.onLine DF)
  (h_f_on_DF : f.onLine DF)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (h_lineImg_AC : lineImg AC = DC')
  (step1 : ptImg b = e)
  (step2 : lineImg AC = DF)
  : ptImg c = f := by
  rw [h_ptImg_c]
  have hDC'DF : DC' = DF := h_lineImg_AC.symm.trans step2
  have hb'e : b' = e := h_ptImg_b.symm.trans step1
  have h_e_on_DE : e.onLine DE := hb'e ▸ h_b'_on_DE
  clear step1 step2 h_ptImg_b h_ptImg_c h_b'_on_DE h_lineImg_AC
  clear ptImg lineImg
  euclid_finish

end Elements.Book1
