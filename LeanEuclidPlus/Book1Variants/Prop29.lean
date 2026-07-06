import SystemE
import Book1.Prop13.Main
import Book1.Prop15.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem proposition_29' : ∀ (a b c d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine g h EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
    euclid_intros
    euclid_apply (extend_point EF g h) as f
    euclid_apply (proposition_29 a b c d e f g h AB CD EF)
    euclid_finish

theorem proposition_29'' : ∀ (a b d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  (between a g b) ∧ (b.sameSide d GH) ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
    euclid_intros
    euclid_apply (extend_point GH g h) as f
    euclid_apply (extend_point GH h g) as e
    euclid_apply (extend_point CD d h) as c
    euclid_apply (proposition_29 a b c d e f g h AB CD GH)
    euclid_finish

theorem proposition_29''' : ∀ (a d g h : Point) (AB CD GH : Line),
  distinctPointsOnLine a g AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h GH ∧
  a.opposingSides d GH ∧ ¬(AB.intersectsLine CD) →
  ∠ a:g:h = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB a g) as b
  euclid_apply (proposition_29'' a b d g h AB CD GH)
  euclid_finish

theorem proposition_29'''' : ∀ (b d e g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine e h EF ∧
  between e g h ∧ b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ e:g:b = ∠ g:h:d :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

theorem proposition_29''''' : ∀ (b d g h : Point) (AB CD EF : Line),
  distinctPointsOnLine g b AB ∧ distinctPointsOnLine h d CD ∧ distinctPointsOnLine g h EF ∧
  b.sameSide d EF ∧ ¬(AB.intersectsLine CD) →
  ∠ b:g:h + ∠ g:h:d = ∟ + ∟ :=
by
  euclid_intros
  euclid_apply (extend_point AB b g) as a
  euclid_apply (extend_point CD d h) as c
  euclid_apply (extend_point EF g h) as f
  euclid_apply (extend_point EF h g) as e
  euclid_apply (proposition_29 a b c d e f g h AB CD EF)
  euclid_finish

end Elements.Book1
