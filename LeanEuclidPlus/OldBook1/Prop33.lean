import SystemE
import OldBook1.Prop04
import OldBook1.Prop27
import OldBook1Variants.Prop29

namespace Elements.Book1

theorem proposition_33 : ∀ (a b c d : Point) (AB CD AC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ |(a─b)| = |(c─d)| →
  AC ≠ BD ∧ ¬(AC.intersectsLine BD) ∧ |(a─c)|= |(b─d)| :=
by
  euclid_intros
  euclid_apply (line_from_points b c ) as BC
  euclid_apply (proposition_29''' a d b c AB CD BC)
  euclid_apply (proposition_4 c b d b c a BC BD CD BC AC AB)
  euclid_apply (proposition_27 a d c b AC BD BC)
  euclid_finish

end Elements.Book1
