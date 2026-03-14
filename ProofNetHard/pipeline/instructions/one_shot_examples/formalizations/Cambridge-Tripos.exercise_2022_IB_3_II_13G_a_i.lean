import Mathlib

open Filter Set


theorem thm_Q
  (U : Set ℂ)
  (hU_1 : Nonempty U)
  (hU_2 : IsConnected U)
  (hU_3 : IsOpen U)
  (f_n : ℕ → ℂ → ℂ)
  (hf_n_1 : ∀ n : ℕ, DifferentiableOn ℂ (f_n n) U)
  (f : ℂ → ℂ)
  (hf_1 : ∀ X : Set ℂ, X ⊆ U ∧ IsCompact X → TendstoUniformlyOn (λ n x => f_n n x) f atTop X) :
  DifferentiableOn ℂ f U := by
sorry
