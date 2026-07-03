import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step7
  (b c e f : Point) (b' c' : Point) (BC EF : Line)
  (ptImg : Point → Point) (lineImg : Line → Line)
  (hassump1 : lineImg BC = EF)
  (h_bc_b'c' : |(b─c)| = |(b'─c')|)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (step1 : ptImg b = e)
  (step3 : ptImg c = f)
  : |(b─c)| = |(e─f)| := by
  have hb'e : b' = e := h_ptImg_b.symm.trans step1
  have hc'f : c' = f := h_ptImg_c.symm.trans step3
  rw [hb'e, hc'f] at h_bc_b'c'
  exact h_bc_b'c'

end Elements.Book1
