import SystemE
import OldBook1.Prop33
import OldBook1Variants.Prop34
import OldBook1Variants.Prop35

namespace Elements.Book1

theorem proposition_36 : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g :=
by
  euclid_intros
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_assert (|(b─c)| = |(e─h)|)
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_finish

end Elements.Book1
