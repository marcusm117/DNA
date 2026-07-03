import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step8
  (a b c d e f : Point) (b' c' : Point)
  (ptImg : Point → Point)
  (hassump1 : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f)
  (h_ab_de : |(a─b)| = |(d─e)|)
  (h_ac_df : |(a─c)| = |(d─f)|)
  (h_ang : ∠ b:a:c = ∠ b':d:c')
  (h_ang2 : ∠ a:c:b = ∠ d:c':b')
  (h_ang3 : ∠ c:b:a = ∠ c':b':d)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (step1 : ptImg b = e)
  (step3 : ptImg c = f)
  (step7 : |(b─c)| = |(e─f)|)
  : Triangle.area △ a:b:c = Triangle.area △ d:e:f := by
  have hb'e : b' = e := h_ptImg_b.symm.trans step1
  have hc'f : c' = f := h_ptImg_c.symm.trans step3
  rw [hb'e, hc'f] at h_ang h_ang2 h_ang3
  clear step1 step3 h_ptImg_b h_ptImg_c hassump1 hb'e hc'f
  clear ptImg
  euclid_finish

end Elements.Book1
