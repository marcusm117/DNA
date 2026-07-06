import SystemE
import Book1.Prop34.variants
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_38_step6
    (a b c g : Point) (AD BF AB AC BG : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hassump1 : formParallelogram g b a c BG AC AD BF)
    : Triangle.area △ a:b:c + Triangle.area △ a:b:c =
      Triangle.area △ g:b:c + Triangle.area △ g:c:a := by
  -- prop34 on the parallelogram: △g:b:a = △c:a:b
  have h34out : |(g─b)| = |(a─c)| ∧ |(g─a)| = |(b─c)| ∧
                ∠ g:b:c = ∠ g:a:c ∧ ∠ b:g:a = ∠ a:c:b ∧
                Triangle.area △ g:b:a = Triangle.area △ c:a:b := by
    euclid_apply (proposition_34 g b a c BG AC AD BF AB ⟨hassump1, ⟨hb_AB, ha_AB, hab.symm⟩⟩)
  obtain ⟨-, -, -, -, h_area⟩ := h34out
  -- parallelogram_area: △g:a:c + △g:c:b = △b:g:a + △b:a:c
  have heq_pa := parallelogram_area g b a c BG AC AD BF hassump1
  linarith [area_symm_2 g a c, area_symm_2 g c b,
            area_symm_2 b g a, area_symm_1 b a g,
            area_symm_2 a b c, area_symm_1 a c b,
            area_symm_1 c a b, area_symm_1 b c a]

end Elements.Book1
