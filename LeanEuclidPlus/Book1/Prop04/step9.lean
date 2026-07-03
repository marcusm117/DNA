import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_4_step9
  (b c e f : Point) (b' c' : Point)
  (ptImg : Point → Point)
  (hassump1 : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f)
  (h_ang2 : ∠ a:c:b = ∠ d:c':b')
  (h_ang3 : ∠ c:b:a = ∠ c':b':d)
  (h_ptImg_b : ptImg b = b')
  (h_ptImg_c : ptImg c = c')
  (step1 : ptImg b = e)
  (step3 : ptImg c = f)
  (h_bc_b'c' : |(b─c)| = |(b'─c')|)
  (h_b'_ne_c' : b' ≠ c')
  (h_a_ne_b : a ≠ b)
  (h_d_ne_e : d ≠ e)
  : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e := by
  have hb'e : b' = e := h_ptImg_b.symm.trans step1
  have hc'f : c' = f := h_ptImg_c.symm.trans step3
  rw [hb'e, hc'f] at h_ang2 h_ang3 h_b'_ne_c' h_bc_b'c'
  -- h_ang3 : ∠c:b:a = ∠f:e:d, h_ang2 : ∠a:c:b = ∠d:f:e
  -- h_b'_ne_c' : e ≠ f, h_bc_b'c' : |(b─c)| = |(e─f)|
  clear hassump1 step1 step3 h_ptImg_b h_ptImg_c hb'e hc'f
  clear ptImg
  have h_b_ne_c : b ≠ c := by euclid_finish
  have h1 : ∠ a:b:c = ∠ c:b:a := angle_symm a b c ⟨h_a_ne_b, h_b_ne_c⟩
  have h2 : ∠ f:e:d = ∠ d:e:f := angle_symm f e d ⟨h_b'_ne_c'.symm, h_d_ne_e.symm⟩
  exact ⟨h1.trans (h_ang3.trans h2), h_ang2⟩

end Elements.Book1
