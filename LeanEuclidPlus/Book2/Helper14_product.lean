import SystemE
import Book.Prop03
import Book2.Helper14_geomean

namespace Elements.Book2

open Elements.Book1

/--
Helper for `Book2.Prop14`.  Given two segments `f─g` (length p) and `f─e`
(length q), lay them out *collinearly* and produce a point `h` with
`|g─h|² = p·q = |f─g|·|f─e|`.

Strategy:
  Along line FG, beyond g, mark f₀ with `|g─f₀| = |f─e| = q` (Prop 1.3, after
  extending FG far enough).  Then `f ─ g ─ f₀` is collinear with `|f─g| = p`,
  `|g─f₀| = q`, so `helper_14_geomean f g f₀ FG` gives `h` with
  `|g─h|² = |f─g|·|g─f₀| = p·q`.
-/
theorem helper_14_product : ∀ (f g e : Point) (FG FE : Line),
  distinctPointsOnLine f g FG ∧ distinctPointsOnLine f e FE →
  ∃ (h : Point), |(g─h)| * |(g─h)| = |(f─g)| * |(f─e)| :=
by
  euclid_intros
  -- extend FG beyond g far enough to cut off a length |f─e|
  euclid_apply (extend_point_longer FG f g (f─e)) as x
  -- cut off f₀ on (g,x) with |g─f₀| = |f─e|
  euclid_apply (proposition_3 g x f e FG FE) as f0
  -- f ─ g ─ f₀ collinear, distinct
  have hbet : between f g f0 := by euclid_finish
  euclid_apply (helper_14_geomean f g f0 FG) as hh
  use hh
  -- |g─hh|² = |f─g|·|g─f₀|  and  |g─f₀| = |f─e|
  euclid_finish

end Elements.Book2