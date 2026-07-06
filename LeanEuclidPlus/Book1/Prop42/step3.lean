import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step3 (b c e f₀ d₁ d₂ d₃ : Point)
    (h_f₀_ne_e : f₀ ≠ e)
    (h_bet : between b e c)
    (h_angle : ∠f₀:e:c = ∠d₁:d₂:d₃) :
    ∠c:e:f₀ = ∠d₁:d₂:d₃ := by
  have h_c_ne_e : c ≠ e := by euclid_finish
  exact (angle_symm c e f₀ ⟨h_c_ne_e, h_f₀_ne_e.symm⟩).trans h_angle

end Elements.Book1
