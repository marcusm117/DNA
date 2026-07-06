import SystemE
import Helpers.SameSide
import Helpers.Pasch
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step11 (a b c e f f₀ d₁ d₂ d₃ : Point)
    (BC EF AG : Line)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_f0_EF : f₀.onLine EF)
    (h_f0_ne_e : f₀ ≠ e)
    (h_f0_side : f₀.onLine BC ∨ f₀.sameSide a BC)
    (h_f_AG : f.onLine AG) (h_a_AG : a.onLine AG)
    (h_par : ¬AG.intersectsLine BC)
    (h_bet : between b e c)
    (h_angle_pos : ∠ d₁:d₂:d₃ > 0)
    (h_angle_lt : ∠ d₁:d₂:d₃ < ∟ + ∟)
    (step3 : ∠ c:e:f₀ = ∠ d₁:d₂:d₃) :
    ∠ c:e:f = ∠ d₁:d₂:d₃ := by
  have h_e_BC : e.onLine BC := by euclid_finish
  have h_c_ne_e : c ≠ e := by euclid_finish
  have h_f0_ss_a : f₀.sameSide a BC := by
    cases h_f0_side with
    | inl h_f0_BC =>
      exfalso
      have h_EF_BC : EF = BC := by
        euclid_apply (two_points_determine_line f₀ e EF BC)
        euclid_finish
      have h_c_EF : c.onLine EF := h_EF_BC ▸ h_c_BC
      by_cases h_bet_cef0 : between c e f₀
      · have h_flat : ∠ c:e:f₀ = ∟ + ∟ := flat_angle_onlyif c e f₀ h_bet_cef0
        linarith [step3.symm.trans h_flat]
      · have h_zero : ∠ c:e:f₀ = 0 := by
          euclid_apply (degenerated_angle_if e c f₀ EF)
          euclid_finish
        linarith [step3.symm.trans h_zero]
    | inr h => exact h
  have h_a_not_BC : ¬a.onLine BC := by euclid_finish
  have h_AG_ne_BC : AG ≠ BC := fun h => h_a_not_BC (h ▸ h_a_AG)
  have h_f_ss_a : f.sameSide a BC :=
    sameSide_of_parallel_both f a AG BC h_f_AG h_a_AG h_AG_ne_BC h_par
  have h_f_ss_f0 : f.sameSide f₀ BC :=
    same_side_trans a f f₀ BC ⟨same_side_symm f a BC h_f_ss_a, same_side_symm f₀ a BC h_f0_ss_a⟩
  have h_f_ne_e : f ≠ e := by euclid_finish
  have h_not_bet : ¬between f e f₀ := fun h_bet_fef0 =>
    (Elements.not_sameSide_of_between f e f₀ BC h_e_BC h_bet_fef0) h_f_ss_f0
  have h_eq : ∠ c:e:f = ∠ c:e:f₀ := by
    euclid_apply (equal_angles e f f₀ c c EF BC)
    euclid_finish
  exact h_eq.trans step3

end Elements.Book1
