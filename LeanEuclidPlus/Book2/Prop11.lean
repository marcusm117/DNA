import SystemE
import Book.Prop03      -- 1.3  cut off a segment equal to a given one
import Book.Prop10      -- 1.10 bisect a straight-line
import Book.Prop11      -- 1.11 erect a perpendicular
import Book.Prop47      -- 1.47 Pythagoras
import Book2.Helper11_golden

namespace Elements.Book2

open Elements.Book1

/-
Convention (cf. Prop 2.1 / Book 1 Prop 47, axiom `rectangle_area`):
  "rectangle contained by X and Y"  = |X| * |Y|   (area of the figure)
  "square on X"                      = |X| * |X|
This is a CONSTRUCTION proposition ("To cut a given straight-line such
that …"), so it is stated existentially, like Book 1's Prop 1/10:
  given AB, produce a cut point H on AB with the required area equality.
Diagram order: A — H — B.

PROOF (non-faithful but valid — exhibits the golden section directly):
  Write s = |ab|.  The cut |ah| = x must satisfy s·(s−x) = x², i.e.
  x = s·(√5−1)/2, an irrational ratio, so a √5 length must be built.
    1. bisect AB at m            (1.10)  ⟹ |am| = s/2
    2. erect ⊥ to AB at a        (1.11)  ⟹ point p off AB, ∠p:a:b = ∟
    3. cut e on AP with |ae|=|am| (1.3)  ⟹ |ae| = s/2, ∠e:a:b = ∟
    4. Pythagoras on right △a-e-b (1.47) ⟹ |eb|² = |ae|² + |ab|²   (= 5s²/4)
    5. produce EA beyond a, cut f with |ef|=|eb| (1.3) ⟹ |af| = |eb|−|ae|
    6. cut h on AB with |ah|=|af| (1.3)  ⟹ between a h b, |ah| = |eb|−|ae|
  The final equality |ab|·|bh| = |ah|·|ah| is then pure length algebra
  (`helper_11_golden`): it collapses to |eb|² = 5|ae|², which is step 4 under
  |ab| = 2|ae|.
-/

-- To cut a given straight-line such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece. Let $AB$ be the given straight-line. So it is required to cut $AB$ such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece. [I say that $AB$ has been cut at $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $AH$.]
theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| :=
by
  euclid_intros
  -- 1. bisect AB at m :  |am| = |mb| = |ab|/2
  euclid_apply (proposition_10 a b AB) as m
  -- 2. erect a perpendicular to AB at a :  p off AB, ∠p:a:b = ∟
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  -- 3. cut e on AP with |ae| = |am|
  euclid_apply (extend_point_longer AP a p (a─m)) as e0
  euclid_apply (proposition_3 a e0 a m AP AB) as e
  have h_angle : ∠ e:a:b = ∟ := by euclid_finish
  -- 4. Pythagoras on the right triangle a-e-b (right angle at a)
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_47 a e b AP EB AB)
  -- Key length facts.  All stated ADDITIVELY (the SMT translator handles only
  -- +,*,/ and Nat literals — no `2*`, no subtraction), so `euclid_finish` can
  -- discharge each from the construction; the subtraction lives in the helper.
  have hA  : |(a─b)| = |(a─m)| + |(a─m)| := by euclid_finish   -- bisection: |ab|=|am|+|mb|, |am|=|mb|
  have hE  : |(a─e)| = |(a─m)| := by euclid_finish              -- cut on perpendicular
  have hpy : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_finish
  -- 5. produce EA beyond a, and cut f with |ef| = |eb|  ⟹  |eb| = |ae| + |af|
  euclid_apply (extend_point_longer AP e a (e─b)) as f0
  euclid_apply (proposition_3 e f0 e b AP EB) as f
  have hQ : |(e─b)| = |(a─e)| + |(a─f)| := by euclid_finish     -- between e a f, |ef|=|eb|
  -- 6. cut h on AB with |ah| = |af|  (the golden point).
  -- The cut needs |af| < |ab| — a √5 magnitude fact, nonlinear, so prove it in Lean.
  have hMpos : |(a─m)| > 0 := by euclid_finish
  have hEBnn : |(e─b)| ≥ 0 := by euclid_finish
  have hlt : |(a─f)| < |(a─b)| :=
    helper_11_af_lt_ab |(a─b)| |(a─m)| |(a─e)| |(e─b)| |(a─f)| hMpos hA hE hpy hQ hEBnn
  euclid_apply (proposition_3 a b a f AB AP) as h
  use h
  have hAH : |(a─h)| = |(a─f)| := by euclid_finish
  have hBH : |(a─b)| = |(a─h)| + |(b─h)| := by euclid_finish    -- between a h b
  refine ⟨by euclid_finish, ?_⟩
  -- final equality : pure length algebra via helper_11_golden
  exact helper_11_golden |(a─b)| |(a─m)| |(a─e)| |(e─b)| |(a─f)| |(a─h)| |(b─h)|
    hA hE hpy hQ hAH hBH

end Elements.Book2