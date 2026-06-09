import SystemE
import Book.Prop34


namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) :=
by
  euclid_intros
  -- △abc = △acd (big parallelogram, diagonal AC), and the two small parallelograms split by AK / KC.
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_assert (Triangle.area △ a:e:k : ℝ) + (Triangle.area △ k:g:c) = (Triangle.area △ a:h:k) + (Triangle.area △ k:f:c)

  -- Collinear facts: K on diagonal, F on right edge, G on bottom edge, E on left edge.
  euclid_assert between a k c
  euclid_assert between d f c
  euclid_assert between b g c
  euclid_assert between a e b

  -- === d-side: decompose △a:d:c into the upper-right pieces. ===
  -- Split △a:d:c by K (on AC), then △a:k:d by H (on AD) and △d:k:c by F (on DC).
  euclid_apply (sum_areas_if a c k d AC)
  euclid_apply (sum_areas_if a d h k AD)
  euclid_apply (sum_areas_if d c f k CD)
  -- Complement KD = parallelogram HDFK; relate its two diagonal-splits (HF vs KD).
  euclid_assert formParallelogram h d k f AD EF GH CD
  euclid_apply (parallelogram_area h d k f AD EF GH CD)
  euclid_assert (Triangle.area △ a:h:k : ℝ) + (Triangle.area △ k:f:c) + (Triangle.area △ h:k:f) + (Triangle.area △ h:f:d) = (Triangle.area △ a:d:c)

  -- === b-side: decompose △a:b:c into the lower-left pieces. ===
  -- Split △a:b:c by K (on AC), then △a:k:b by E (on AB) and △b:k:c by G (on BC).
  euclid_apply (sum_areas_if a c k b AC)
  euclid_apply (sum_areas_if a b e k AB)
  euclid_apply (sum_areas_if b c g k BC)
  -- Complement BK = parallelogram EBGK; relate its two diagonal-splits (EG vs BK).
  euclid_assert formParallelogram e b k g AB GH EF BC
  euclid_apply (parallelogram_area e b k g AB GH EF BC)
  euclid_assert (Triangle.area △ a:e:k : ℝ) + (Triangle.area △ k:g:c) + (Triangle.area △ e:b:g) + (Triangle.area △ e:g:k) = (Triangle.area △ a:b:c)

  euclid_finish

end Elements.Book1
