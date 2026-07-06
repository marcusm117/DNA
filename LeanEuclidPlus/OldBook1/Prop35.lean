import SystemE
import OldBook1.Prop04
import OldBook1Variants.Prop29
import OldBook1Variants.Prop34

namespace Elements.Book1

theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f :=
by
  euclid_intros
  euclid_apply (proposition_34' a d b c AF BC AB CD)
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_assert (|(a─d)| = |(e─f)|)
  euclid_assert (|(a─e)| = |(d─f)|)
  euclid_apply (proposition_29'''' c b f d a CD AB AF)
  euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
  euclid_finish

end Elements.Book1
