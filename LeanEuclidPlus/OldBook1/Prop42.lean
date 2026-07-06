import SystemE
import OldBook1.Prop10
import OldBook1Variants.Prop23
import OldBook1.Prop31
import OldBook1.Prop38
import OldBook1.Prop41

namespace Elements.Book1

theorem proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_10 b c BC) as e
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_23' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as f'
  euclid_apply (line_from_points e f') as EF
  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  euclid_assert (formParallelogram f g e c AG BC EF CG)
  euclid_apply (proposition_38 a b e a e c AG BC AB AE AE AC)
  euclid_apply (proposition_41 f e c g a AG BC EF CG AE AC)
  use f, g, e, c, AG, BC, EF, CG
  euclid_finish

end Elements.Book1
