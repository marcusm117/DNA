import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step5
  (b c e f : Point) (b' c' : Point) (BC BC' EF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (hassump1 : ptImg b = e)
  (hassump2 : ptImg c = f)
  (hassump3 : lineImg BC ≠ EF)
  (h_b'_on_BC' : b'.onLine BC')
  (h_c'_on_BC' : c'.onLine BC')
  (h_b'_ne_c' : b' ≠ c')
  (h_e_on_EF : e.onLine EF)
  (h_f_on_EF : f.onLine EF)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (h_lineImg_BC : lineImg BC = BC')
  (step1 : ptImg b = e)
  (step3 : ptImg c = f)
  : distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF := by
  rw [h_lineImg_BC]
  have hb'e : b' = e := h_ptImg_b.symm.trans step1
  have hc'f : c' = f := h_ptImg_c.symm.trans step3
  clear step1 step3 h_ptImg_b h_ptImg_c hassump1 hassump2 hassump3 h_lineImg_BC
  clear ptImg lineImg
  constructor <;> euclid_finish

end Elements.Book1
