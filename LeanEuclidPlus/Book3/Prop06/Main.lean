import SystemE
import Book3.Prop06.step1
import Book3.Prop06.step2
import Book3.Prop06.step3
import Book3.Prop06.step4
import Book3.Prop06.step5
import Book3.Prop06.step6
import Book3.Prop06.step7
import Book3.Prop06.step8
import Book3.Prop06.hFEB_int
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_6 : ∀ (ABC CDE : Circle),
  -- "touch" = Def III.3 (meet but do not cut), NOT "exactly one point" (that is the later theorem
  -- III.13, which cites III.11 — defining touch as ∃! here would be circular). `ABC ≠ CDE` is the
  -- "two distinct circles" of the enunciation (same-circle satisfies meet+don't-cut, so it's needed).
  ABC ≠ CDE →
  (∃ c : Point, c.onCircle ABC ∧ c.onCircle CDE) ∧ ¬ ABC.intersectsCircle CDE →
  ¬ ∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE :=
by
  euclid_intros

  euclid_intro_sentence "3.6.0"
    "If two circles touch one another, (then) they will not have the same center. For let the two circles $ABC$ and $CDE$ touch one another at point $C$. I say that they will not have the same center."
  obtain ⟨c, hcABC, hcCDE⟩ := left

  have habsurd1 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE) := by
    intro hsuppose1
    obtain ⟨f, hfABC, hfCDE⟩ := hsuppose1
    euclid_sentence "3.6.1"
      "For, if possible, let $F$ be (the common center),"
      (step1 : f.isCentre ABC ∧ f.isCentre CDE) := by euclid_apply (helper_3_6_step1 ABC CDE f (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show f.isCentre CDE; assumption)))

    euclid_apply (line_from_points f c) as FC
    euclid_sentence "3.6.2"
      "and let $FC$ be joined,"
      (step2 : f.onLine FC ∧ c.onLine FC) := by euclid_apply (helper_3_6_step2 f c FC (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)))

    -- Draw a line FEB through f (the supposed centre): b a point on ABC, FEB = line f b,
    -- which meets CDE (f is interior to CDE) at e.
    euclid_apply (exists_point_on_circle ABC) as b
    euclid_apply (line_from_points f b) as FEB
    have hFEB_int : FEB.intersectsCircle CDE := by euclid_apply (helper_3_6_hFEB_int f CDE FEB (by euclid_assumption "" (show f.isCentre CDE; assumption)) (by euclid_assumption "" (show f.onLine FEB; assumption)))
    euclid_apply (intersections_circle_line CDE FEB) as (e, e2)
    euclid_sentence "3.6.3"
      "and let $FEB$ be drawn through (the two circles), at random."
      (step3 : b.onCircle ABC ∧ e.onCircle CDE ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB) := by euclid_apply (helper_3_6_step3 ABC CDE b e f FEB (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle CDE; assumption)) (by euclid_assumption "" (show f.onLine FEB; assumption)) (by euclid_assumption "" (show e.onLine FEB; assumption)) (by euclid_assumption "" (show b.onLine FEB; assumption)))

    -- @assumption_valid
    have step4_assumption1 : f.isCentre ABC := by assumption
    -- @assumption ("point $F$ is the center of the circle $ABC$", f.isCentre ABC)
    euclid_sentence "3.6.4"
      "Therefore, since point $F$ is the center of the circle $ABC$, $FC$ is equal to $FB$."
      (step4 : |(f─c)| = |(f─b)|) := by euclid_apply (helper_3_6_step4 ABC f c b (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "point $F$ is the center of the circle $ABC$" (show f.isCentre ABC; assumption)))

    -- @assumption_valid
    have step5_assumption1 : f.isCentre CDE := by assumption
    -- @assumption ("point $F$ is the center of the circle $CDE$", f.isCentre CDE)
    euclid_sentence "3.6.5"
      "Again, since point $F$ is the center of the circle $CDE$, $FC$ is equal to $FE$."
      (step5 : |(f─c)| = |(f─e)|) := by euclid_apply (helper_3_6_step5 CDE f c e (by euclid_assumption "" (show c.onCircle CDE; assumption)) (by euclid_assumption "" (show e.onCircle CDE; assumption)) (by euclid_assumption "point $F$ is the center of the circle $CDE$" (show f.isCentre CDE; assumption)))

    -- @assumption_valid
    have step6_assumption1 : |(f─c)| = |(f─b)| := by assumption
    -- @assumption ("$FC$ was shown (to be) equal to $FB$", |(f─c)| = |(f─b)|)
    euclid_sentence "3.6.6"
      "But $FC$ was shown (to be) equal to $FB$. Thus, $FE$ is also equal to $FB$, the lesser to the greater."
      (step6 : |(f─e)| = |(f─b)|) := by euclid_apply (helper_3_6_step6 f c e b (by euclid_assumption "" (show |(f─c)| = |(f─e)|; assumption)) (by euclid_assumption "$FC$ was shown (to be) equal to $FB$" (show |(f─c)| = |(f─b)|; assumption)))

    euclid_sentence "3.6.7"
      "The very thing is impossible."
      (step7 : False) := by euclid_apply (helper_3_6_step7 ABC CDE c f b e FC FEB (by euclid_assumption "" (show ¬ABC.intersectsCircle CDE; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle CDE; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show f.isCentre CDE; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle CDE; assumption)) (by euclid_assumption "" (show f.onLine FEB; assumption)) (by euclid_assumption "" (show e.onLine FEB; assumption)) (by euclid_assumption "" (show b.onLine FEB; assumption)) (by euclid_assumption "" (show |(f─c)| = |(f─b)|; assumption)) (by euclid_assumption "" (show |(f─c)| = |(f─e)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(f─b)|; assumption)) (by euclid_assumption "" (show ABC ≠ CDE; assumption)))
    exact step7

  euclid_sentence "3.6.8"
    "Thus, point $F$ is not the (common) center of the circles $ABC$ and $CDE$."
    (step8 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE)) := by euclid_apply (helper_3_6_step8 ABC CDE (by euclid_assumption "" (show ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE); assumption)))
  -- step8 : ¬∃f,... applied to the telescoped reductio hyp (a✝) closes the False goal
  exact step8 ‹∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE›
  euclid_conclude_sentence "3.6.9"
    "Thus, if two circles touch one another, (then) they will not have the same center. (Which is) the very thing it was required to show."

end Elements.Book3
