import SystemE
import Book3.Prop12.step1
import Book3.Prop12.step2
import Book3.Prop12.step3
import Book3.Prop12.step4
import Book3.Prop12.step5
import Book3.Prop12.step6
import Book3.Prop12.step7
import Book3.Prop12.step8
import Book3.Prop12.step9
import Book3.Prop12.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_12 : ∀ (a f g : Point) (ABC ADE : Circle),
  f.isCentre ABC ∧
  g.isCentre ADE ∧
  a.onCircle ABC ∧
  a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  f.outsideCircle ADE ∧
  g.outsideCircle ABC →
  between f a g :=
by
  euclid_intros
  euclid_intro_sentence "3.12.0"
    "If two circles touch one another externally, (then) the (straight-line) joining their centers will go through the point of union. For let two circles, $ABC$ and $ADE$, touch one another externally at point $A$, and let the center $F$ of $ABC$ be found [Prop.~3.1], and (the center) $G$ of $ADE$ [Prop.~3.1]. I say that the straight-line joining $F$ to $G$ will go through the point of union at $A$."

  have habsurd1 : ¬(¬ between f a g) := by
    intro hsuppose1
    euclid_sentence "3.12.1"
      "For (if) not (then), if possible, let it go like $FCDG$ (in the figure),"
      (step1 : ∃ (c d : Point), c.onCircle ABC ∧ d.onCircle ADE ∧ between f c d ∧ between c d g) := by euclid_apply (helper_3_12_step1 a f g ABC ADE (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show ¬f.insideCircle ADE; assumption)) (by euclid_assumption "" (show ¬f.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬g.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬between f a g; assumption)))
    obtain ⟨c, d, hcABC, hdADE, hfcd, hcdg⟩ := step1

    euclid_apply (line_from_points a f) as AF
    euclid_apply (line_from_points a g) as AG
    euclid_sentence "3.12.2"
      "and let $AF$ and $AG$ be joined."
      (step2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG) := by euclid_apply (helper_3_12_step2 a f g ABC ADE AF AG (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)))

    -- @assumption_valid
    have step3_assumption1 : f.isCentre ABC := by assumption
    -- @assumption ("point $F$ is the center of circle $ABC$", f.isCentre ABC)
    euclid_sentence "3.12.3"
      "Therefore, since point $F$ is the center of circle $ABC$, $FA$ is equal to $FC$."
      (step3 : |(f─a)| = |(f─c)|) := by euclid_apply (helper_3_12_step3 a f c ABC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "point $F$ is the center of circle $ABC$" (show f.isCentre ABC; assumption)))

    -- @assumption_valid
    have step4_assumption1 : g.isCentre ADE := by assumption
    -- @assumption ("point $G$ is the center of circle $ADE$", g.isCentre ADE)
    euclid_sentence "3.12.4"
      "Again, since point $G$ is the center of circle $ADE$, $GA$ is equal to $GD$."
      (step4 : |(g─a)| = |(g─d)|) := by euclid_apply (helper_3_12_step4 a g d ADE (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show d.onCircle ADE; assumption)) (by euclid_assumption "point $G$ is the center of circle $ADE$" (show g.isCentre ADE; assumption)))

    -- @assumption_valid
    have step5_assumption1 : |(f─a)| = |(f─c)| := by assumption
    -- @assumption ("$FA$ was also shown (to be) equal to $FC$", |(f─a)| = |(f─c)|)
    euclid_sentence "3.12.5"
      "And $FA$ was also shown (to be) equal to $FC$. Thus, the (straight-lines) $FA$ and $AG$ are equal to the (straight-lines) $FC$ and $GD$."
      (step5 : |(f─a)| + |(a─g)| = |(f─c)| + |(g─d)|) := by euclid_apply (helper_3_12_step5 a f g c d (by euclid_assumption "$FA$ was also shown (to be) equal to $FC$" (show |(f─a)| = |(f─c)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─d)|; assumption)) (by euclid_assumption "$FA$ was also shown (to be) equal to $FC$" (show |(f─a)| = |(f─c)|; assumption)))

    euclid_sentence "3.12.6"
      "So the whole of $FG$ is greater than $FA$ and $AG$."
      (step6 : |(f─g)| > |(f─a)| + |(a─g)|) := by euclid_apply (helper_3_12_step6 f g c d a (by euclid_assumption "" (show between f c d; assumption)) (by euclid_assumption "" (show between c d g; assumption)) (by euclid_assumption "" (show |(f─a)| = |(f─c)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─d)|; assumption)))

    euclid_sentence "3.12.7"
      "But, (it is) also less [Prop.~1.20]."
      (step7 : |(f─g)| < |(f─a)| + |(a─g)|) := by euclid_apply (helper_3_12_step7 a f g ABC AF AG (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬g.insideCircle ABC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG; assumption)) (by euclid_assumption "" (show ¬between f a g; assumption)))

    euclid_sentence "3.12.8"
      "The very thing is impossible."
      (step8 : False) := by euclid_apply (helper_3_12_step8 f a g (by euclid_assumption "" (show |(f─g)| > |(f─a)| + |(a─g)|; assumption)) (by euclid_assumption "" (show |(f─g)| < |(f─a)| + |(a─g)|; assumption)))
    exact step8

  euclid_sentence "3.12.9"
    "Thus, the straight-line joining $F$ to $G$ cannot not go through the point of union at $A$."
    (step9 : ¬ ¬ between f a g) := by euclid_apply (helper_3_12_step9 f a g (by euclid_assumption "" (show ¬¬between f a g; assumption)))

  euclid_sentence "3.12.10"
    "Thus, (it will go) through it."
    (step10 : between f a g) := by euclid_apply (helper_3_12_step10 f a g (by euclid_assumption "" (show ¬¬between f a g; assumption)))

  exact step10
  euclid_conclude_sentence "3.12.11"
    "Thus, if two circles touch one another externally, (then) the [straight-line] joining their centers will go through the point of union. (Which is) the very thing it was required to show."

end Elements.Book3
