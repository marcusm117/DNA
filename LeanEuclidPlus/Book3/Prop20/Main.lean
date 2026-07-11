import SystemE
import Book3.Prop20.step1
import Book3.Prop20.step2
import Book3.Prop20.step3
import Book3.Prop20.step4
import Book3.Prop20.step5
import Book3.Prop20.step6
import Book3.Prop20.step7
import Book3.Prop20.step8
import Book3.Prop20.step9
import Book3.Prop20.step10
import Book3.Prop20.step11
import Book3.Prop20.step12
import Book3.Prop20.hd_ex
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_20 : ∀ (a b c e : Point) (BC : Line) (ABC : Circle),
  e.isCentre ABC ∧
  a.onCircle ABC ∧
  b.onCircle ABC ∧
  c.onCircle ABC ∧
  distinctPointsOnLine b c BC ∧
  b ≠ a ∧
  c ≠ a ∧
  a.sameSide e BC →
  ∠ b:e:c = ∠ b:a:c + ∠ b:a:c :=
by
  euclid_intros
  euclid_intro_sentence "3.20.0"
    "In a circle, the angle at the center is double that at the circumference, when the angles have the same circumference base. Let $ABC$ be a circle, and let $BEC$ be an angle at its center, and $BAC$ (one) at (its) circumference. And let them have the same circumference base $BC$. I say that angle $BEC$ is double (angle) $BAC$."

  euclid_apply (line_from_points a e) as AEF
  euclid_apply (intersection_circle_line_extending_points ABC AEF e a) as f
  euclid_sentence "3.20.1"
    "For being joined, let $AE$ be drawn through to $F$."
    (step1 : distinctPointsOnLine a e AEF ∧ f.onCircle ABC ∧ between a e f) := by euclid_apply (helper_3_20_step1 a e f AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show between f e a; assumption)))

  -- @assumption_valid
  have step2_assumption1 : |(e─a)| = |(e─b)| := by euclid_finish
  -- @assumption ("$EA$ is equal to $EB$", |(e─a)| = |(e─b)|)
  euclid_sentence "3.20.2"
    "Therefore, since $EA$ is equal to $EB$, angle $EAB$ (is) also equal to $EBA$ [Prop.~1.5]."
    (step2 : ∠ e:a:b = ∠ e:b:a) := by euclid_apply (helper_3_20_step2 a b e AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "$EA$ is equal to $EB$" (show |(e─a)| = |(e─b)|; assumption)))

  euclid_sentence "3.20.3"
    "Thus, angle $EAB$ and $EBA$ is double (angle) $EAB$."
    (step3 : ∠ e:a:b + ∠ e:b:a = ∠ e:a:b + ∠ e:a:b) := by euclid_apply (helper_3_20_step3 a b e (by euclid_assumption "" (show ∠ e:a:b = ∠ e:b:a; assumption)))

  euclid_sentence "3.20.4"
    "And $BEF$ (is) equal to $EAB$ and $EBA$ [Prop.~1.32]."
    (step4 : ∠ b:e:f = ∠ e:a:b + ∠ e:b:a) := by euclid_apply (helper_3_20_step4 a b e f AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show between f e a; assumption)))

  euclid_sentence "3.20.5"
    "Thus, $BEF$ is also double $EAB$."
    (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) := by euclid_apply (helper_3_20_step5 a b e f (by euclid_assumption "" (show ∠ e:a:b = ∠ e:b:a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:b:a; assumption)))

  euclid_sentence "3.20.6"
    "So, for the same (reasons), $FEC$ is also double $EAC$."
    (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c) := by euclid_apply (helper_3_20_step6 a c e f AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show between f e a; assumption)))

  euclid_sentence "3.20.7"
    "Thus, the whole (angle) $BEC$ is double the whole (angle) $BAC$."
    (step7 : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c) := by euclid_apply (helper_3_20_step7 a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:a:b; assumption)) (by euclid_assumption "" (show ∠ f:e:c = ∠ e:a:c + ∠ e:a:c; assumption)))

  have hd_ex : ∃ d : Point, d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d ∧ d.sameSide e BC := by euclid_apply (helper_3_20_hd_ex a b c e BC ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)))
  obtain ⟨d, hd_on, hdb, hdc, hda, hd_side⟩ := hd_ex
  euclid_sentence "3.20.8"
    "So let another (straight-line) be inflected, and let there be another angle, $BDC$."
    (step8 : d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d) := by euclid_apply (helper_3_20_step8 a b c d ABC (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)))

  euclid_apply (line_from_points d e) as DEG
  euclid_apply (intersection_circle_line_extending_points ABC DEG e d) as g
  euclid_sentence "3.20.9"
    "And $DE$ being joined, let it be produced to $G$."
    (step9 : distinctPointsOnLine d e DEG ∧ g.onCircle ABC ∧ between d e g) := by euclid_apply (helper_3_20_step9 d e g DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show between g e d; assumption)))

  euclid_sentence "3.20.10"
    "So, similarly, we can show that angle $GEC$ is double $EDC$,"
    (step10 : ∠ g:e:c = ∠ e:d:c + ∠ e:d:c) := by euclid_apply (helper_3_20_step10 c d e g DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show between g e d; assumption)))

  euclid_sentence "3.20.11"
    "of which $GEB$ is double $EDB$."
    (step11 : ∠ g:e:b = ∠ e:d:b + ∠ e:d:b) := by euclid_apply (helper_3_20_step11 b d e g DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show between g e d; assumption)))

  euclid_sentence "3.20.12"
    "Thus, the remaining (angle) $BEC$ is double the (remaining angle) $BDC$."
    (step12 : ∠ b:e:c = ∠ b:d:c + ∠ b:d:c) := by euclid_apply (helper_3_20_step12 b c d e g BC DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show d.sameSide e BC; assumption)) (by euclid_assumption "" (show between g e d; assumption)) (by euclid_assumption "" (show ∠ g:e:c = ∠ e:d:c + ∠ e:d:c; assumption)) (by euclid_assumption "" (show ∠ g:e:b = ∠ e:d:b + ∠ e:d:b; assumption)))

  exact step7
  euclid_conclude_sentence "3.20.13"
    "Thus, in a circle, the angle at the center is double that at the circumference, when [the angles] have the same circumference base. (Which is) the very thing it was required to show."

end Elements.Book3
