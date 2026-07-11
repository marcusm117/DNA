import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_e_off_mn
    (e l k m0 : Point) (EK MN : Line)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (hl_MN : l.onLine MN) (hm0_MN : m0.onLine MN) (hm0_off : ¬m0.onLine EK)
    (hl_betw : between e l k) :
    ¬e.onLine MN := by
  have h_l_EK : l.onLine EK := between_same_line_in e l k EK ⟨hl_betw, he_EK, hk_EK⟩
  have h_e_ne_l : e ≠ l := (between_symm e l k hl_betw).2.1
  intro h_e_on_MN
  have h_EK_MN : EK = MN := two_points_determine_line e l EK MN
    ⟨⟨he_EK, h_l_EK, h_e_ne_l⟩, h_e_on_MN, hl_MN⟩
  rw [← h_EK_MN] at hm0_MN
  exact hm0_off hm0_MN

end Elements.Book3
