import SystemE

namespace Elements.Book1

/-
Helper for Prop45.lean:39 (final area equality).

The combined parallelogram `f l k m` has `g` between `f,l` and `h` between `k,m`
(f,g,l collinear on FG; k,h,m collinear on KH).  So `sum_parallelograms_area` splits its
two half-triangles into the four sub-triangles, which match the two given sub-sums
(= △abd and △dbc) up to area symmetry.  One axiom apply + linear arithmetic.
-/
theorem helper_45_area_sum :
    ∀ (a b c d f g k h m l : Point) (FG KH FK LM : Line),
    -- the two parallelogram-area sub-sums (from proposition_42 / proposition_44'):
    (Triangle.area △ f:k:h) + (Triangle.area △ f:h:g) = (Triangle.area △ a:b:d) ∧
    (Triangle.area △ g:h:m) + (Triangle.area △ g:l:m) = (Triangle.area △ d:b:c) ∧
    -- the combined parallelogram f-l-k-m (established by proposition_33 in the proof):
    f.onLine FG ∧ l.onLine FG ∧ k.onLine KH ∧ m.onLine KH ∧
    f.onLine FK ∧ k.onLine FK ∧ l.onLine LM ∧ m.onLine LM ∧
    l ≠ m ∧ f.sameSide k LM ∧
    ¬FG.intersectsLine KH ∧ ¬FK.intersectsLine LM ∧
    -- g, h are the interior glue points:
    between f g l ∧ between k h m →
    (Triangle.area △ f:k:m) + (Triangle.area △ f:l:m) =
      (Triangle.area △ a:b:d) + (Triangle.area △ d:b:c) :=
by
  euclid_intros
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
