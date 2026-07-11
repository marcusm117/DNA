import SystemE
import Book3.Prop11.step1
import Book3.Prop11.step2
import Book3.Prop11.step3
import Book3.Prop11.step4
import Book3.Prop11.step5
import Book3.Prop11.step6
import Book3.Prop11.step7
import Book3.Prop11.step8
import Book3.Prop11.step9
import Book3.Prop11.hd_ex
import Book3.Prop11.step_nhout
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_11 : ∀ (a f g : Point) (ABC ADE : Circle),
  a.onCircle ABC ∧ a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  g.insideCircle ABC ∧
  |(g─a)| < |(f─a)| ∧
  f.isCentre ABC ∧ g.isCentre ADE ∧
  f ≠ g →
  between f g a :=
by
  euclid_intros
  euclid_intro_sentence "3.11.0"
    "If two circles touch one another internally, and their centers are found, (then) the straight-line joining their centers, being produced, will fall upon the point of union of the circles. For let two circles, $ABC$ and $ADE$, touch one another internally at point $A$, and let the center $F$ of circle $ABC$ be found [Prop.~3.1], and (the center) $G$ of (circle) $ADE$ [Prop.~3.1]. I say that the straight-line joining $G$ to $F$, being produced, will fall on $A$."

  have habsurd1 : ¬(¬(between f g a)) := by
    intro hsuppose1
    euclid_sentence "3.11.1"
      "For (if) not (then), if possible, let it fall like $FGH$ (in the figure),"
      (step1 : ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h) := by euclid_apply (helper_3_11_step1 a f g ABC (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)))
    obtain ⟨h, h_ne, h_on_ABC, h_bet_fgh⟩ := step1
    -- @euclid_gap: Euclid implicitly assumes H falls outside ADE when extending line FGH; the ¬outsideCircle cases require a separate argument not given in his text
    by_cases h_out : h.outsideCircle ADE
    · have hd_ex : ∃ d : Point, d.onCircle ADE ∧ between g d h := by euclid_apply (helper_3_11_hd_ex f g h ADE (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show h.outsideCircle ADE; assumption)))
      obtain ⟨d, hd_on_ADE, hd_bet_gdh⟩ := hd_ex
      euclid_apply (line_from_points a f) as AF
      euclid_apply (line_from_points a g) as AG
      euclid_sentence "3.11.2"
        "and let $AF$ and $AG$ be joined."
        (step2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG) := by euclid_apply (helper_3_11_step2 a f g ABC ADE AF AG (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)))
      -- @assumption_valid
      have step3_assumption1 : |(f─a)| = |(f─h)| := by euclid_finish
      -- @assumption_valid
      have step3_assumption2 : |(a─g)| + |(g─f)| > |(f─h)| := by euclid_finish
      -- @assumption ("that is to say $FH$", |(f─a)| = |(f─h)|)
      -- @assumption ("since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]", |(a─g)| + |(g─f)| > |(f─h)|)
      euclid_sentence "3.11.3"
        "Therefore, since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20], let $FG$ be taken from both."
        (step3 : |(a─g)| > |(f─h)| - |(g─f)|) := by euclid_apply (helper_3_11_step3 a f g h ABC AF AG (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)) (by euclid_assumption "" (show h ≠ a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "that is to say $FH$" (show |(f─a)| = |(f─h)|; assumption)) (by euclid_assumption "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]" (show |(a─g)| + |(g─f)| > |(f─h)|; assumption)))
      euclid_sentence "3.11.4"
        "Thus, the remainder $AG$ is greater than the remainder $GH$."
        (step4 : |(a─g)| > |(g─h)|) := by euclid_apply (helper_3_11_step4 a f g h (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show |(a─g)| > |(f─h)| - |(g─f)|; assumption)))
      euclid_sentence "3.11.5"
        "And $AG$ (is) equal to $GD$."
        (step5 : |(a─g)| = |(g─d)|) := by euclid_apply (helper_3_11_step5 a g d ADE (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show d.onCircle ADE; assumption)))
      euclid_sentence "3.11.6"
        "Thus, $GD$ is also greater than $GH$, the lesser than the greater."
        (step6 : |(g─d)| > |(g─h)|) := by euclid_apply (helper_3_11_step6 a g d h (by euclid_assumption "" (show |(a─g)| > |(g─h)|; assumption)) (by euclid_assumption "" (show |(a─g)| = |(g─d)|; assumption)))
      euclid_sentence "3.11.7"
        "The very thing is impossible."
        (step7 : False) := by euclid_apply (helper_3_11_step7 g d h (by euclid_assumption "" (show between g d h; assumption)) (by euclid_assumption "" (show |(g─d)| > |(g─h)|; assumption)))
      exact step7
    · have step_nhout : False := by euclid_apply (helper_3_11_step_nhout a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)) (by euclid_assumption "" (show h ≠ a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show ¬h.outsideCircle ADE; assumption)))
      exact step_nhout

  euclid_sentence "3.11.8"
    "Thus, the straight-line joining $F$ to $G$ will not fall outside (one circle but inside the other)."
    (step8 : ¬(¬(between f g a))) := by euclid_apply (helper_3_11_step8 a f g (by euclid_assumption "" (show ¬¬between f g a; assumption)))

  euclid_sentence "3.11.9"
    "Thus, it will fall upon the point of union (of the circles) at point $A$."
    (step9 : between f g a) := by euclid_apply (helper_3_11_step9 a f g (by euclid_assumption "" (show ¬¬between f g a; assumption)))

  exact step9
  euclid_conclude_sentence "3.11.10"
    "Thus, if two circles touch one another internally, [and their centers are found], (then) the straight-line joining their centers, [being produced], will fall upon the point of union of the circles. (Which is) the very thing it was required to show."

end Elements.Book3
