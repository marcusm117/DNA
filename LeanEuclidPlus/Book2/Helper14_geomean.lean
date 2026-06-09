import SystemE
import Book.Prop10
import Book.Prop11
import Book.Prop47

namespace Elements.Book2

open Elements.Book1

/--
Helper for `Book2.Prop14` (quadrature).  The geometric-mean / "square root"
construction: given `b ─ e ─ f` collinear (e between b and f), the segment
`e─h` erected perpendicular at `e` up to the semicircle on diameter `bf`
satisfies `|e─h|² = |b─e|·|e─f|`.

Strategy:
  g  = midpoint of bf            (Prop 1.10), so |bg| = |gf| =: r.
  α  = circle centre g, radius gb (so b,f are on α).
  f0 = perpendicular to BF at e   (Prop 1.11), EH = line e f0.
  e is inside α (between two points of α) ⇒ EH meets α at some h.
  |gh| = |gb| = r  (h on α).  Right angle ∠g:e:h (BF ⟂ EH at e).
  Pythagoras (Prop 1.47) on △g:e:h:  |eh|² = |gh|² − |ge|² = r² − |ge|².
  Difference of squares (g midpoint, e between b f):  r² − |ge|² = |be|·|ef|.
-/
theorem helper_14_geomean : ∀ (b e f : Point) (BF : Line),
  distinctPointsOnLine b f BF ∧ between b e f →
  ∃ (h : Point), |(e─h)| * |(e─h)| = |(b─e)| * |(e─f)| :=
by
  euclid_intros
  -- midpoint g of bf
  euclid_apply (proposition_10 b f BF) as g
  -- circle centre g through b ; f is on it too
  euclid_apply (circle_from_points g b) as α
  euclid_apply (point_on_circle_if g b f α)
  -- e is inside the circle (strictly between two points of α)
  euclid_apply (circle_points_between b f e α)
  -- perpendicular to BF at e
  euclid_apply (proposition_11 b f e BF) as f0
  euclid_apply (line_from_points e f0) as EH
  -- the perpendicular through e (interior point) meets the circle
  euclid_apply (intersection_circle_line_2 e α EH)
  euclid_apply (intersections_circle_line α EH) as (h, h')
  -- h on circle ⇒ |gh| = |gb| = r
  euclid_apply (point_on_circle_onlyif g b h α)
  use h
  -- now purely length/angle reasoning
  euclid_apply (line_from_points g h) as GH
  by_cases (e = g)
  · -- e = g : e is the centre, |eh| = r, and |be|·|ef| = r²
    euclid_finish
  · -- e ≠ g.  Decompose: right angle at e ⇒ Pythagoras ⇒ difference of squares.
    -- (1) ∠ g:e:h is right: g lies on BF, the perpendicular EH meets BF at e at ∟.
    have hperp : (∠ g:e:h : ℝ) = ∟ := by euclid_finish
    -- (2) g,e,h form a triangle (h is off BF, e ≠ g).
    euclid_apply (proposition_47 e g h BF GH EH)
    -- now in context: |g─h|² = |g─e|² + |e─h|²   (Pythagoras, right angle at e)
    -- and  |g─h| = |g─b|   (h, b both on α centred at g)
    -- (3) difference of squares: |gb|² − |ge|² = |be|·|ef|  (g midpoint of bf).
    euclid_finish

end Elements.Book2
