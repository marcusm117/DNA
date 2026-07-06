import SystemE
import OldBook1.Prop31
import OldBook1Variants.Prop34
import OldBook1Variants.Prop35

namespace Elements.Book1

theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  euclid_apply (proposition_31 b a c AC) as BE
  euclid_apply (intersection_lines AD BE) as e
  euclid_apply (proposition_31 c b d BD) as CF
  euclid_apply (intersection_lines AD CF) as f
  euclid_apply (proposition_35' e b c a d f AD BC BE AC BD CF)
  euclid_apply (proposition_34 e a b c AD BC BE AC AB)
  euclid_apply (proposition_34 f d c b AD BC CF BD CD)
  euclid_finish

end Elements.Book1
