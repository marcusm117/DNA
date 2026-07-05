import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD) (_ : f ≠ d)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_off_EF : ¬a.onLine EF) (h_d_off_EF : ¬d.onLine EF)
  (h_b_AE : b.onLine AE) (h_bae : between a e b)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  (hassump1 : AE.intersectsLine FD)
  : g.sameSide b EF ∨ g.opposingSides b EF := by
  have hboff : ¬b.onLine EF := by euclid_finish
  have hgoff : ¬g.onLine EF := by euclid_finish
  by_cases h : g.sameSide b EF
  · exact Or.inl h
  · exact Or.inr ⟨hgoff, hboff, h⟩

end Elements.Book1
