import SystemE
import OldBook1.Prop01

namespace Elements.Book1

theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

end Elements.Book1
