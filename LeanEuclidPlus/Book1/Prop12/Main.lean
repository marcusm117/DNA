import SystemE
import Book1.Prop10.Main
import Book1.Prop12.step1
import Book1.Prop12.step2
import Book1.Prop12.step3
import Book1.Prop12.step4
import Book1.Prop12.step6
import Book1.Prop12.step7
import Book1.Prop12.step8
import Book1.Prop12.step9
import Book1.Prop12.step10
import Book1.Prop12.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.12.0"
    "To draw a straight-line perpendicular to a given infinite straight-line from a given point which is not on it.   Let $AB$ be the given infinite straight-line  and $C$ the given point, which is not on ($AB$). So it is required to draw a  straight-line  perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on ($AB$). "

  euclid_apply (exists_point_opposite AB c) as d
  euclid_sentence "1.12.1"
    "For let point $D$ have been taken at random on the other side (to $C$) of  the straight-line $AB$,"
    (step1 : d.opposingSides c AB) := by euclid_apply (helper_1_12_step1 d c AB (by euclid_assumption "" (show ¬d.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬d.sameSide c AB; assumption)))

  euclid_apply (circle_from_points c d) as EFG
  euclid_apply (intersections_circle_line EFG AB) as (e, g)
  euclid_sentence "1.12.2"
    "and let the circle $EFG$ have been drawn with center $C$ and radius $CD$ [Post.~3],"
    (step2 : c.isCentre EFG ∧ d.onCircle EFG) := by euclid_apply (helper_1_12_step2 c d EFG (by euclid_assumption "" (show c.isCentre EFG; assumption)) (by euclid_assumption "" (show d.onCircle EFG; assumption)))

  euclid_apply (proposition_10 e g AB) as h
  euclid_sentence "1.12.3"
    "and let the straight-line $EG$ have been cut in half at (point) $H$ [Prop.~1.10],"
    (step3 : between e h g ∧ |(e─h)| = |(h─g)|) := by euclid_apply (helper_1_12_step3 e h g (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show |(e─h)| = |(h─g)|; assumption)))

  euclid_apply (line_from_points c g) as CG
  euclid_apply (line_from_points c h) as CH
  euclid_apply (line_from_points c e) as CE
  euclid_sentence "1.12.4"
    "and let the straight-lines $CG$, $CH$, and $CE$ have been joined."
    (step4 : distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE) := by euclid_apply (helper_1_12_step4 c e g h AB CG CH CE (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show c.onLine CG; assumption)) (by euclid_assumption "" (show g.onLine CG; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)))

  euclid_wts "1.12.5"
    "I say that the  (straight-line) $CH$ has been drawn  perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on ($AB$). "

  -- @assumption_valid
  have step6_assumption1 : |(g─h)| = |(h─e)| := by euclid_finish
  -- @assumption_valid
  have step6_assumption2 : |(h─c)| = |(h─c)| := by rfl
  -- @assumption ("$GH$ is equal to $HE$", |(g─h)| = |(h─e)|)
  -- @assumption ("$HC$ (is) common", |(h─c)| = |(h─c)|)
  euclid_sentence "1.12.6"
    "For since $GH$ is equal to $HE$, and $HC$ (is) common, the two (straight-lines) $GH$,  $HC$ are equal to the two (straight-lines) $EH$, $HC$, respectively,"
    (step6 : |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)|) := by euclid_apply (helper_1_12_step6 g h e c (by euclid_assumption "$GH$ is equal to $HE$" (show |(g─h)| = |(h─e)|; assumption)) (by euclid_assumption "$HC$ (is) common" (show |(h─c)| = |(h─c)|; assumption)))

  euclid_sentence "1.12.7"
    "and the base $CG$ is equal to the base $CE$."
    (step7 : |(c─g)| = |(c─e)|) := by euclid_apply (helper_1_12_step7 c e g EFG (by euclid_assumption "" (show c.isCentre EFG; assumption)) (by euclid_assumption "" (show e.onCircle EFG; assumption)) (by euclid_assumption "" (show g.onCircle EFG; assumption)))

  euclid_sentence "1.12.8"
    "Thus, the angle $CHG$ is equal to the angle $EHC$ [Prop.~1.8],"
    (step8 : ∠ c:h:g = ∠ e:h:c) := by euclid_apply (helper_1_12_step8 c e g h AB CG CH CE EFG (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show c.onLine CG; assumption)) (by euclid_assumption "" (show g.onLine CG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show c.isCentre EFG; assumption)) (by euclid_assumption "" (show e.onCircle EFG; assumption)) (by euclid_assumption "" (show g.onCircle EFG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show |(g─h)| = |(h─e)|; assumption)) (by euclid_assumption "" (show |(c─g)| = |(c─e)|; assumption)))

  euclid_sentence "1.12.9"
    "and they are adjacent."
    (step9 : h.onLine AB) := by euclid_apply (helper_1_12_step9 e h g AB (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)))

  -- @assumption_valid
  have step10_assumption1 : ∠ c:h:g = ∠ e:h:c := by assumption
  -- @assumption ("the adjacent angles equal to one another", ∠ c:h:g = ∠ e:h:c)
  euclid_sentence "1.12.10"
    "But when a straight-line stood on a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle,"
    (step10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) := by euclid_apply (helper_1_12_step10 c e g h AB (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AB; assumption)) (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "the adjacent angles equal to one another" (show ∠ c:h:g = ∠ e:h:c; assumption)))

  euclid_sentence "1.12.11"
    "and the former straight-line is called a perpendicular to that upon which it stands [Def.~1.10]. "
    (step11 : ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) := by euclid_apply (helper_1_12_step11 a b c e g h AB CH (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show between e h g; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟; assumption)))

  exact ⟨h, step9, step11⟩
  euclid_conclude_sentence "1.12.12"
    "Thus, the (straight-line) $CH$ has been drawn perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on  ($AB$). (Which is) the very thing it was required to do."

end Elements.Book1
