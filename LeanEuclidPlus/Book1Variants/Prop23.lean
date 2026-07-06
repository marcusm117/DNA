import SystemE
import Book1.Prop08.Main
import Book1.Prop20.Main
import Book1Variants.Prop22
import Book1.Prop23.Main

namespace Elements.Book1

theorem proposition_23' : ∀ (a b c d e x : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧ ¬(x.onLine AB) →
  ∃ f : Point, f ≠ a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ (∠ f:a:b = ∠ d:c:e) :=
by
  euclid_intros
  by_cases (d.onLine CE)
  . -- Omitted by Euclid.
    by_cases (∠ d:c:e = 0)
    . use b
      euclid_finish
    . euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'
      euclid_finish
  euclid_apply (line_from_points d e) as DE
  -- Euclid didn't explicitly apply proposition_20.
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22'' c d c e e d a b x CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_8 c d e a f g CD DE CE AF FG AB)
  use f
  euclid_finish

end Elements.Book1
