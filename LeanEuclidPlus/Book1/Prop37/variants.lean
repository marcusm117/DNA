import SystemE
import Book1.Prop31.Main
import Book1.Prop34.variants
import Book1.Prop35.variants
import Book1.Prop37.Main

namespace Elements.Book1

theorem proposition_37' : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
by
  euclid_intros
  by_cases (d.sameSide c AB)
  . euclid_apply (proposition_37 a b c d AB BC AC BD CD AD)
    assumption
  . euclid_apply (proposition_37 d b c a BD BC CD AB AC AD)
    euclid_finish

end Elements.Book1
