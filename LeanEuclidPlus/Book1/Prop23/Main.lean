import SystemE
import Book1.Prop20.Main
import Book1Variants.Prop22
import Book1.Prop23.step1
import Book1.Prop23.step2
import Book1.Prop23.step3
import Book1.Prop23.step4
import Book1.Prop23.step5
import Book1.Prop23.step6
import Book1.Prop23.hfoff
import Book1.Prop23.hfa
import Book1.Prop23.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.23.0"
    "To construct a rectilinear angle equal to a given rectilinear angle at a (given) point on a given straight-line. Let $AB$ be the given straight-line,  $A$ the (given) point on it, and  $DCE$ the given rectilinear angle. So it is required to construct a rectilinear angle equal to the given rectilinear angle $DCE$ at the (given) point $A$ on the given straight-line $AB$. "
  by_cases (d.onLine CE)
  -- Degenerate case omitted by Euclid
  ·
    by_cases (∠ d:c:e = 0)
    · use b; euclid_finish
    · euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'; euclid_finish
  euclid_apply (line_from_points d e) as DE
  euclid_sentence "1.23.1"
    "Let the points $D$ and $E$ have been taken at random on each of the (straight-lines) $CD$ and $CE$ (respectively), and let $DE$ have been joined."
    (step1 : distinctPointsOnLine d e DE) := by euclid_apply (helper_1_23_step1 d e CE DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬d.onLine CE; assumption)))
  -- Euclid didn't explicitly apply proposition_20 (triangle inequality preconditions).
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as FA
  euclid_apply (line_from_points f g) as FG
  have hfoff : ¬f.onLine AB := by euclid_apply (helper_1_23_hfoff c d e a b f g AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show |(a─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(a─g)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─c)| + |(c─e)| > |(d─e)|; assumption)) (by euclid_assumption "" (show |(e─d)| + |(d─c)| > |(e─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))
  euclid_sentence "1.23.2"
    "And let the triangle $AFG$ have been constructed from three straight-lines which are equal to $CD$, $DE$, and $CE$,"
    (step2 : formTriangle a f g FA FG AB) := by euclid_apply (helper_1_23_step2 a b f g AB FA FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show ¬between g a b; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show f.onLine FA; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show |(a─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(a─g)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─c)| + |(c─e)| > |(d─e)|; assumption)) (by euclid_assumption "" (show |(e─d)| + |(d─c)| > |(e─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))
  euclid_sentence "1.23.3"
    "such that $CD$ is equal to $AF$,"
    (step3 : |(c─d)| = |(a─f)|) := by euclid_apply (helper_1_23_step3 c d a f (by euclid_assumption "" (show |(a─f)| = |(c─d)|; assumption)))
  euclid_sentence "1.23.4"
    "$CE$ to $AG$,"
    (step4 : |(c─e)| = |(a─g)|) := by euclid_apply (helper_1_23_step4 c e a g (by euclid_assumption "" (show |(a─g)| = |(c─e)|; assumption)))
  euclid_sentence "1.23.5"
    "and further $DE$ to $FG$ [Prop.~1.22]. "
    (step5 : |(d─e)| = |(f─g)|) := by euclid_apply (helper_1_23_step5 d e f g (by euclid_assumption "" (show |(f─g)| = |(e─d)|; assumption)))
  -- @assumption_valid
  have step6_assumption1 : |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)| := by euclid_finish
  -- @assumption_valid
  have step6_assumption2 : |(d─e)| = |(f─g)| := by assumption
  -- @assumption ("the two (straight-lines) $DC$, $CE$ are equal to the two (straight-lines) $FA$, $AG$, respectively", |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)|)
  -- @assumption ("the base $DE$ is equal to the base $FG$", |(d─e)| = |(f─g)|)
  euclid_sentence "1.23.6"
    "Therefore, since the two (straight-lines) $DC$, $CE$ are equal to the two (straight-lines) $FA$, $AG$, respectively, and the base $DE$ is equal to the base $FG$, the angle $DCE$ is thus equal to the angle $FAG$ [Prop.~1.8]. "
    (step6 : ∠ d:c:e = ∠ f:a:g) := by euclid_apply (helper_1_23_step6 c d e a f g CD CE DE FA FG AB (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬d.onLine CE; assumption)) (by euclid_assumption "" (show formTriangle a f g FA FG AB; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(c─e)| = |(a─g)|; assumption)) (by euclid_assumption "the base $DE$ is equal to the base $FG$" (show |(d─e)| = |(f─g)|; assumption)) (by euclid_assumption "the two (straight-lines) $DC$, $CE$ are equal to the two (straight-lines) $FA$, $AG$, respectively" (show |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)|; assumption)) (by euclid_assumption "the base $DE$ is equal to the base $FG$" (show |(d─e)| = |(f─g)|; assumption)))
  use f
  have hfa : f ≠ a := by euclid_apply (helper_1_23_hfa a f AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show ¬f.onLine AB; assumption)))
  have hangle : ∠ f:a:b = ∠ d:c:e := by euclid_apply (helper_1_23_hangle a b f g AB FA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show f.onLine FA; assumption)) (by euclid_assumption "" (show ¬f.onLine AB; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ¬between g a b; assumption)) (by euclid_assumption "" (show |(a─g)| = |(c─e)|; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∠ f:a:g; assumption)))
  exact ⟨hfa, hangle⟩
  euclid_conclude_sentence "1.23.7"
    "Thus, the rectilinear angle $FAG$,  equal to the  given rectilinear angle $DCE$, has been constructed at the (given) point $A$ on the given straight-line $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
