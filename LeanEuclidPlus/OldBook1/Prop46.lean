import SystemE
import OldBook1.Prop03
import OldBook1Variants.Prop11
import OldBook1Variants.Prop29
import OldBook1.Prop31
import OldBook1Variants.Prop34

namespace Elements.Book1

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
by
  euclid_intros
  euclid_apply (proposition_11'' a b AB) as c'
  euclid_apply (line_from_points a c') as AC
  euclid_apply (extend_point_longer AC a c' (a─b)) as c
  euclid_apply (proposition_3 a c a b AC AB) as d
  euclid_apply (proposition_31 d a b AB) as DE
  euclid_apply (proposition_31 b a d AC) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  euclid_apply (proposition_29''''' e b d a DE AB AC)
  euclid_apply (proposition_34' d e a b DE AB AC BE)
  use d, e, DE, AC, BE
  euclid_finish

end Elements.Book1
