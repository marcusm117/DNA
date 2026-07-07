import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop01.step12_goff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step12 (a b d g : Point) (AB GD : Line)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_g_on_GD : g.onLine GD) (h_d_on_GD : d.onLine GD)
    (h_bet_adb : between a d b)
    (h_gNa : g ≠ a) (h_gNd : g ≠ d) (h_gNb : g ≠ b)
    (h_step9 : |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|)
    (h_step10 : |(g─a)| = |(g─b)|)
    (hassump1 : ∠ a:d:g = ∠ g:d:b) :
    ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟ := by
  obtain ⟨h_ad_db, _⟩ := h_step9
  have step12_goff : ¬g.onLine AB := by euclid_apply (helper_3_1_step12_goff a b d g AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─d)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─b)|; assumption)))
  have h_d_on_AB : d.onLine AB :=
    between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h1 : ∠ a:d:g = ∟ := by
    euclid_apply (perpendicular_if a b d g AB)
    euclid_finish
  exact ⟨h1, hassump1.symm.trans h1⟩

end Elements.Book3
