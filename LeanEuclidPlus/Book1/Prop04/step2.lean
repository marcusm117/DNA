import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step2
  (a b c d e f : Point) (b' c' : Point) (AB BC AC DE EF DF DC' BC' : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (hassump1 : lineImg AB = DE)
  (h_ang_edf : ∠ b:a:c = ∠ e:d:f)
  (h_ang_bac : ∠ b:a:c = ∠ b':d:c')
  (h_c'_sameSide : c'.sameSide f DE)
  (h_d_on_DC' : d.onLine DC')
  (h_c'_on_DC' : c'.onLine DC')
  (h_d_ne_c' : d ≠ c')
  (h_d_on_DF : d.onLine DF)
  (h_f_on_DF : f.onLine DF)
  (h_d_on_DE : d.onLine DE)
  (h_b'_on_DE : b'.onLine DE)
  (h_d_ne_e : d ≠ e)
  (h_ptImg_b : ptImg b = b')
  (h_lineImg_AC : lineImg AC = DC')
  (step1 : ptImg b = e)
  : lineImg AC = DF := by
  rw [h_lineImg_AC]
  have hb'e : b' = e := by rw [← h_ptImg_b]; exact step1
  have h_e_on_DE : e.onLine DE := hb'e ▸ h_b'_on_DE
  clear step1 h_ptImg_b hassump1 h_lineImg_AC h_b'_on_DE
  clear ptImg lineImg
  have h_ang_edc' : ∠ e:d:c' = ∠ e:d:f := by euclid_finish
  euclid_finish

end Elements.Book1
