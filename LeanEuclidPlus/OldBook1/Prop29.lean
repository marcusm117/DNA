import SystemE
import OldBook1.Prop13
import OldBook1.Prop15

namespace Elements.Book1

theorem proposition_29 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  have : ∠ a:g:h = ∠ g:h:d := by
    by_contra
    by_cases ∠ a:g:h > ∠ g:h:d
    · euclid_assert ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d
      euclid_apply (proposition_13 h g a b EF AB)
      euclid_assert ∠ b:g:h + ∠ g:h:d < ∟ + ∟
      euclid_finish
    · -- Omitted by Euclid.
      euclid_assert ∠ a:g:h < ∠ g:h:d
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∠ g:h:d + ∠ c:h:g
      euclid_apply (proposition_13 g h c d EF CD)
      euclid_assert ∠ a:g:h + ∠ c:h:g < ∟ + ∟
      euclid_finish

  euclid_apply (proposition_15 a b e h g AB EF)
  euclid_apply (proposition_13 b g e h AB EF)
  euclid_finish

end Elements.Book1
