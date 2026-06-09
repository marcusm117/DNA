import SystemE
import Book.Prop14
import Book.Prop29
import Book.Prop30
import Book.Prop33
import Book.Prop34
import Book.Prop42
import Book.Prop44


namespace Elements.Book1

/-
Helper for Prop45 (final area equality).

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

theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) :=
by
  euclid_intros
  euclid_apply (proposition_42 a b d e₁ e₂ e₃ AB DB AD E₁₂ E₂₃) as (f, g, k, h , FG, KH, FK, GH)
  euclid_apply (proposition_44' g h d b c e₁ e₂ e₃ k GH DB BC CD E₁₂ E₂₃) as (m, l, HM, G, LM)
  euclid_assert ((∠ h:k:f : ℝ) = ∠ g:h:m)
  euclid_assert ((∠ h:k:f : ℝ) + (∠ k:h:g) = (∠ g:h:m) + (∠ k:h:g))
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_assert ((∠ k:h:g : ℝ) + (∠ g:h:m) = ∟ + ∟)
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_assert ((∠ m:h:g : ℝ) + (∠ h:g:l) = (∠ h:g:f) + (∠ h:g:l))
  euclid_apply (proposition_29''''' l m g h G HM GH)
  euclid_assert ((∠ h:g:f : ℝ) + (∠ h:g:l) = ∟ + ∟)
  euclid_apply (proposition_14 h g f l GH FG G)
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_apply (proposition_34' h m g l HM G GH LM)
  euclid_assert (|(k─f)| = |(m─l)|)
  euclid_apply (proposition_30 FK LM GH)
  euclid_assert (|(f─l)| = |(k─m)|)
  euclid_apply (proposition_33 f l k m FG KH FK LM)
  -- f,l opposite across GH:  l,m on LM ∥ GH ⟹ l.sameSide m GH; f.sameSide k GH and
  --   k,m opposite across GH ⟹ f opposite m ⟹ (with l~m) f opposite l.
  have hlm : l.sameSide m GH := by
    by_contra
    euclid_apply (intersection_lines_opposing l m GH LM)
    euclid_finish
  have hfl : ¬(f.sameSide l GH) := by euclid_finish
  -- glue points: g between f,l (on FG); h between k,m (on KH), via pasch_4 across GH.
  euclid_apply (pasch_4 f g l GH FG)
  euclid_apply (pasch_4 k h m GH KH)
  use f, l, k, m, FG, KH, FK, LM
  euclid_apply (helper_45_area_sum a b c d f g k h m l FG KH FK LM)
  euclid_finish

end Elements.Book1
