import SystemE
import Book3.Prop05.step1
import Book3.Prop05.step2
import Book3.Prop05.step3
import Book3.Prop05.step4
import Book3.Prop05.step5
import Book3.Prop05.step6
import Book3.Prop05.step7
import Book3.Prop05.step8
import Book3.Prop05.step9
import Book3.Prop05.hne_ec
import Book3.Prop05.hne_eg
import Book3.Prop05.he_inside_ABC
import Book3.Prop05.hEFG_int_ABC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_5 : ∀ (ABC CDG : Circle),
  -- "two circles" of the enunciation: distinct (System E does NOT forbid a circle intersecting
  -- itself, so without this ABC = CDG satisfies the hypothesis and the statement is false).
  ABC ≠ CDG →
  ABC.intersectsCircle CDG →
  ¬ ∃ e : Point, e.isCentre ABC ∧ e.isCentre CDG :=
by
  euclid_intros
  euclid_intro_sentence "3.5.0"
    "If two circles cut one another, (then) they will not have the same center. For let the two circles $ABC$ and $CDG$ cut one another at points $B$ and $C$. I say that they will not have the same center."

  -- euclid_intros intro'd through ¬; goal is False;
  -- ∃ e, e.isCentre ABC ∧ e.isCentre CDG is in context.
  obtain ⟨e, hecABC, hecdg⟩ := ‹∃ e : Point, e.isCentre ABC ∧ e.isCentre CDG›
  -- Get C, a point lying on both circles.
  euclid_apply (intersection_circles ABC CDG) as c
  -- Construct line EC through e and c (e ≠ c: center is inside, c is on, circle).
  have hne_ec : e ≠ c := by euclid_apply (helper_3_5_hne_ec ABC e c (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)))
  euclid_apply (line_from_points e c) as EC
  -- Construct EFG: a line through e hitting CDG at g and ABC at f.
  euclid_apply (exists_distinct_point_on_circle CDG c) as g
  have hne_eg : e ≠ g := by euclid_apply (helper_3_5_hne_eg CDG e g (by euclid_assumption "" (show e.isCentre CDG; assumption)) (by euclid_assumption "" (show g.onCircle CDG; assumption)))
  euclid_apply (line_from_points e g) as EFG
  have he_inside_ABC : e.insideCircle ABC := by euclid_apply (helper_3_5_he_inside_ABC ABC e (by euclid_assumption "" (show e.isCentre ABC; assumption)))
  have hEFG_int_ABC : EFG.intersectsCircle ABC := by euclid_apply (helper_3_5_hEFG_int_ABC ABC EFG e (by euclid_assumption "" (show e.insideCircle ABC; assumption)) (by euclid_assumption "" (show e.onLine EFG; assumption)))
  euclid_apply (intersections_circle_line ABC EFG) as (f, f')

  euclid_sentence "3.5.1"
    "For, if possible, let $E$ be (the common center),"
    (step1 : e.isCentre ABC ∧ e.isCentre CDG) := by euclid_apply (helper_3_5_step1 ABC CDG e (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show e.isCentre CDG; assumption)))

  euclid_sentence "3.5.2"
    "and let $EC$ be joined,"
    (step2 : e.onLine EC ∧ c.onLine EC) := by euclid_apply (helper_3_5_step2 EC e c (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)))

  euclid_sentence "3.5.3"
    "and let $EFG$ be drawn through (the two circles), at random."
    (step3 : e.onLine EFG ∧ f.onCircle ABC ∧ f.onLine EFG ∧
             g.onCircle CDG ∧ g.onLine EFG) := by euclid_apply (helper_3_5_step3 ABC CDG EFG e f g (by euclid_assumption "" (show e.onLine EFG; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onLine EFG; assumption)) (by euclid_assumption "" (show g.onCircle CDG; assumption)) (by euclid_assumption "" (show g.onLine EFG; assumption)))

  -- @assumption_valid
  have step4_assumption1 : e.isCentre ABC := by assumption
  -- @assumption ("point $E$ is the center of the circle $ABC$", e.isCentre ABC)
  euclid_sentence "3.5.4"
    "And since point $E$ is the center of the circle $ABC$, $EC$ is equal to $EF$."
    (step4 : |(e─c)| = |(e─f)|) := by euclid_apply (helper_3_5_step4 ABC e c f (by euclid_assumption "point $E$ is the center of the circle $ABC$" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)))

  -- @assumption_valid
  have step5_assumption1 : e.isCentre CDG := by assumption
  -- @assumption ("point $E$ is the center of the circle $CDG$", e.isCentre CDG)
  euclid_sentence "3.5.5"
    "Again, since point $E$ is the center of the circle $CDG$, $EC$ is equal to $EG$."
    (step5 : |(e─c)| = |(e─g)|) := by euclid_apply (helper_3_5_step5 CDG e c g (by euclid_assumption "point $E$ is the center of the circle $CDG$" (show e.isCentre CDG; assumption)) (by euclid_assumption "" (show c.onCircle CDG; assumption)) (by euclid_assumption "" (show g.onCircle CDG; assumption)))

  euclid_sentence "3.5.6"
    "But $EC$ was also shown (to be) equal to $EF$."
    (step6 : |(e─c)| = |(e─f)|) := by euclid_apply (helper_3_5_step6 e c f (by euclid_assumption "" (show |(e─c)| = |(e─f)|; assumption)))

  euclid_sentence "3.5.7"
    "Thus, $EF$ is also equal to $EG$, the lesser to the greater."
    (step7 : |(e─f)| = |(e─g)|) := by euclid_apply (helper_3_5_step7 e c f g (by euclid_assumption "" (show |(e─c)| = |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─c)| = |(e─g)|; assumption)))

  euclid_sentence "3.5.8"
    "The very thing is impossible."
    (step8 : False) := by euclid_apply (helper_3_5_step8 ABC CDG e c (by euclid_assumption "" (show ABC ≠ CDG; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show e.isCentre CDG; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle CDG; assumption)))

  euclid_sentence "3.5.9"
    "Thus, point $E$ is not the (common) center of the circles $ABC$ and $CDG$."
    (step9 : ¬(e.isCentre ABC ∧ e.isCentre CDG)) := by euclid_apply (helper_3_5_step9 ABC CDG e c (by euclid_assumption "" (show ABC ≠ CDG; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle CDG; assumption)))

  exact step8
  euclid_conclude_sentence "3.5.10"
    "Thus, if two circles cut one another, (then) they will not have the same center. (Which is) the very thing it was required to show."

end Elements.Book3
