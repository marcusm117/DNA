import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step1
  (b c c' e f : Point) (EF : Line)
  (ptImg : Point → Point)
  (h_ptImg_c : ptImg c = c')
  (hc'_EF : c'.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (h_dist : |(b─c)| = |(e─c')|)
  (h_nbetw : ¬between c' e f)
  (hassump1 : |(b─c)| = |(e─f)|)
  : ptImg c = f := by
  rw [h_ptImg_c]
  clear h_ptImg_c ptImg
  euclid_finish

end Elements.Book1
