import SystemE
import Book1.Prop13.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_1_step3 (ABC : Circle) (a b c c0 d : Point) (AB DC : Line)
    (h_c_on : c.onCircle ABC)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_d_on_DC : d.onLine DC) (h_c0_on_DC : c0.onLine DC) (h_c_on_DC : c.onLine DC)
    (h_perp : ∠ a:d:c0 = ∟)
    (h_c0_off_AB : ¬c0.onLine AB)
    (h_bet_adb : between a d b)
    (h_d_inside : d.insideCircle ABC) :
    c.onCircle ABC ∧ ∠ a:d:c = ∟ := by
  refine ⟨h_c_on, ?_⟩
  have h_cNd : c ≠ d :=
    fun h_eq => inside_not_on_circle d ABC h_d_inside (h_eq ▸ h_c_on)
  have h_d_on_AB : d.onLine AB :=
    between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h_c0Nd : c0 ≠ d := fun h_eq => h_c0_off_AB (h_eq ▸ h_d_on_AB)
  have h_aNd : a ≠ d := (between_symm a d b h_bet_adb).2.1
  have h_AB_ne_DC : AB ≠ DC := fun h_eq => h_c0_off_AB (h_eq ▸ h_c0_on_DC)
  by_cases h_side : between c0 d c
  · -- c on the opposite side of d from c0 on DC: use Book I Prop 13
    have h_c0Nc : c0 ≠ c := (between_symm c0 d c h_side).2.2.1
    have h_prop13 := proposition_13 a d c c0 AB DC
      ⟨h_AB_ne_DC, ⟨h_a_on_AB, h_d_on_AB, h_aNd⟩,
       ⟨h_c_on_DC, h_c0_on_DC, h_c0Nc.symm⟩, h_side⟩
    -- h_prop13 : ∠c:d:a + ∠a:d:c0 = ∟ + ∟
    have h_cda : ∠ c:d:a = ∟ := by linarith
    euclid_finish
  · -- c on the same side of d as c0 on DC: use equal_angles
    have h_no_bet_aa : ¬between a d a :=
      fun h => (between_symm a d a h).2.2.1 rfl
    have h_equal := equal_angles d a a c0 c AB DC
      ⟨h_d_on_AB, h_a_on_AB, h_a_on_AB, h_d_on_DC, h_c0_on_DC, h_c_on_DC,
       h_aNd, h_aNd, h_c0Nd, h_cNd, h_no_bet_aa, h_side⟩
    -- h_equal : ∠a:d:c0 = ∠a:d:c
    exact h_equal ▸ h_perp

end Elements.Book3
