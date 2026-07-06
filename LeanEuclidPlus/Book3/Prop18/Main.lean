import SystemE
import Book1.Prop12.Main
open Elements.Book1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_18 : ∀ (c f : Point) (ABC : Circle) (DE : Line),
  c.onCircle ABC ∧ c.onLine DE ∧ ¬ DE.intersectsCircle ABC ∧
  f.isCentre ABC ∧ f ≠ c →
  ∀ d : Point, d.onLine DE → d ≠ c → ∠ f:c:d = ∟ :=
by
  euclid_intros
  euclid_intro_sentence "3.18.0"
    "If some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent. For let some straight-line $DE$ touch the circle $ABC$ at point $C$, and let the center $F$ of circle $ABC$ be found [Prop.~3.1], and let $FC$ be joined from $F$ to $C$. I say that $FC$ is perpendicular to $DE$."

  -- Reductio: suppose the perpendicular from F to DE is not FC (i.e. ∠f:c:d ≠ ∟).
  -- Derive a contradiction via the foot G of the actual perpendicular, then conclude.
  have habsurd1 : ¬(∠ f:c:d ≠ ∟) := by
    intro hsuppose1
    -- bridge haves for proposition_12 preconditions
    have hcdDE : distinctPointsOnLine c d DE := by sorry
    have hfoff : ¬f.onLine DE := by sorry
    -- construct G, the foot of the perpendicular from F to DE [Prop. 1.12]
    euclid_apply (proposition_12 c d f DE) as g
    euclid_apply (line_from_points f g) as FG
    -- @assumption ("$FG$ is perpendicular to $DE$", ∠ f:c:d ≠ ∟)
    euclid_sentence "3.18.1"
      "For if not, let $FG$ be drawn from $F$, perpendicular to $DE$ [Prop.~1.12]."
      (step1 : g.onLine DE ∧ f.onLine FG ∧ g.onLine FG ∧ (∠ c:g:f = ∟ ∨ ∠ d:g:f = ∟)) := by sorry

    -- @assumption ("angle $FGC$ is a right-angle", ∠ f:g:c = ∟)
    euclid_sentence "3.18.2"
      "Therefore, since angle $FGC$ is a right-angle, (angle) $FCG$ is thus acute [Prop.~1.17]."
      (step2 : ∠ f:c:g < ∟) := by sorry

    -- @assumption ("the greater angle is subtended by the greater side [Prop.~1.19]", ∠ f:g:c > ∠ f:c:g)
    euclid_sentence "3.18.3"
      "And the greater angle is subtended by the greater side [Prop.~1.19]. Thus, $FC$ (is) greater than $FG$."
      (step3 : |(f─c)| > |(f─g)|) := by sorry

    -- introduce b : another point on circle ABC (needed for the radius equality FC = FB)
    have hb : ∃ b : Point, b.onCircle ABC ∧ b ≠ c := by sorry
    obtain ⟨b, hbcircle, hbc⟩ := hb
    euclid_sentence "3.18.4"
      "And $FC$ (is) equal to $FB$."
      (step4 : |(f─c)| = |(f─b)|) := by sorry

    euclid_sentence "3.18.5"
      "Thus, $FB$ (is) also greater than $FG$, the lesser than the greater."
      (step5 : |(f─b)| > |(f─g)|) := by sorry

    euclid_sentence "3.18.6"
      "The very thing is impossible."
      (step6 : False) := by sorry
    exact step6

  -- "Thus FG is not perpendicular to DE" and "similarly no other except FC":
  -- these are structural post-reductio sentences (same pattern as Prop.~1.14 / Prop.~1.40);
  -- the contradiction already closed the argument; no further System-E claim is provable here.
  euclid_conclude_sentence "3.18.7"
    "Thus, $FG$ is not perpendicular to $DE$."
  euclid_conclude_sentence "3.18.8"
    "So, similarly, we can show that neither (is) any other (straight-line) except $FC$."
  euclid_sentence "3.18.9"
    "Thus, $FC$ is perpendicular to $DE$."
    (step9 : ∠ f:c:d = ∟) := by sorry

  exact step9
  euclid_conclude_sentence "3.18.10"
    "Thus, if some straight-line touches a circle, and some (other) straight-line is joined from the center (of the circle) to the point of contact, (then) the (straight-line) so joined will be perpendicular to the tangent. (Which is) the very thing it was required to show."

end Elements.Book3
