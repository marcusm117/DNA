import SystemE
import Book1.Prop04.Main
import Book1.Prop20.Main
import Book1.Prop23.Main
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
import Book3.Prop07.step1
import Book3.Prop07.step2
import Book3.Prop07.step3
import Book3.Prop07.step4
import Book3.Prop07.step5
import Book3.Prop07.step6
import Book3.Prop07.step7
import Book3.Prop07.step8
import Book3.Prop07.step9
import Book3.Prop07.step10
import Book3.Prop07.step11
import Book3.Prop07.step12
import Book3.Prop07.step13
import Book3.Prop07.step14
import Book3.Prop07.step15
import Book3.Prop07.step16
import Book3.Prop07.step18
import Book3.Prop07.step19
import Book3.Prop07.step20
import Book3.Prop07.step21
import Book3.Prop07.step23
import Book3.Prop07.step24
import Book3.Prop07.step25
import Book3.Prop07.step26
import Book3.Prop07.step27
import Book3.Prop07.step28
import Book3.Prop07.step2_assumption1
import Book3.Prop07.hh_exist
import Book3.Prop07.step10_assumption1
import Book3.Prop07.step19_assumption1
import Book3.Prop07.hh_opp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Faithful to Euclid's DEMONSTRATION (not the enunciation's "always"): he names the three other lines
-- FB, FC, FG and proves the specific chain FA>FB>FC>FG>FD (greatest/least = the ends of the chain), under
-- the figure ordering ∠BEF>∠CEF>∠GEF; plus the two-equal (a mirror H on the far side of AD, and uniqueness).
-- Modeled on the faithful sibling Book3/Prop08. (The earlier ∀-over-all-points version over-generalized
-- beyond what the proof actually demonstrates — corrected 2026-07-06.)
theorem proposition_7 : ∀ (ABCD : Circle) (a d e f b c g : Point) (AD : Line),
  e.isCentre ABCD →
  a.onCircle ABCD →
  d.onCircle ABCD →
  distinctPointsOnLine a d AD →
  between a e d →
  between e f d →
  b.onCircle ABCD →
  c.onCircle ABCD →
  g.onCircle ABCD →
  -- Non-degeneracy: b, c, g are not the endpoints of the diameter
  b ≠ a → b ≠ d →
  c ≠ a → c ≠ d →
  g ≠ a → g ≠ d →
  ∠ b:e:f > ∠ c:e:f →
  ∠ c:e:f > ∠ g:e:f →
  |(f─a)| > |(f─b)| ∧
  |(f─b)| > |(f─c)| ∧
  |(f─c)| > |(f─g)| ∧
  |(f─g)| > |(f─d)| ∧
  (∃ h : Point, h.onCircle ABCD ∧ h.opposingSides g AD ∧ |(f─h)| = |(f─g)| ∧
    ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h) :=
by
  euclid_intros
  euclid_intro_sentence "3.7.0"
    "If some point, which is not the center of the circle, is taken on the diameter of a circle, and some straight-lines radiate from the point towards the (circumference of the) circle, (then) the greatest (straight-line) will be that on which the center (lies), and the least the remainder (of the same diameter). And for the others, a (straight-line) nearer$^\\dag$ to the (straight-line) through the center is always greater than a (straight-line) further away. And only two equal (straight-lines) will radiate from the point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). Let $ABCD$ be a circle, and let $AD$ be its diameter, and let some point $F$, which is not the center of the circle, be taken on $AD$. Let $E$ be the center of the circle. And let some straight-lines, $FB$, $FC$, and $FG$, radiate from $F$ towards (the circumference of) circle $ABCD$. I say that $FA$ is the greatest (straight-line), $FD$ the least, and of the others, $FB$ (is) greater than $FC$, and $FC$ than $FG$."

  -- B, C, G (and their circle-membership + the angle ordering ∠BEF>∠CEF>∠GEF) are now theorem
  -- binders/hypotheses, in context from euclid_intros.
  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points g e) as GE
  euclid_sentence "3.7.1"
    "For let $BE$, $CE$, and $GE$ be joined."
    (step1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c e CE ∧ distinctPointsOnLine g e GE) := by euclid_apply (helper_3_7_step1 ABCD e b c g BE CE GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)))

  euclid_apply (line_from_points b f) as BF
  -- @assumption_gap
  have step2_assumption1 : formTriangle e b f BE BF AD := by euclid_apply (helper_3_7_step2_assumption1 ABCD a d e f b AD BE BF (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)))
  -- @assumption ("for every triangle (any) two sides are greater than the remaining (side)", formTriangle e b f BE BF AD)
  euclid_sentence "3.7.2"
    "And since for every triangle (any) two sides are greater than the remaining (side) [Prop.~1.20], $EB$ and $EF$ is thus greater than $BF$."
    (step2 : |(e─b)| + |(e─f)| > |(b─f)|) := by euclid_apply (helper_3_7_step2 e b f BE BF AD (by euclid_assumption "for every triangle (any) two sides are greater than the remaining (side)" (show formTriangle e b f BE BF AD; assumption)))

  -- @assumption_valid
  have step3_assumption1 : |(a─e)| = |(e─b)| := by euclid_finish
  -- @assumption ("$AE$ (is) equal to $BE$", |(a─e)| = |(e─b)|)
  euclid_sentence "3.7.3"
    "And $AE$ (is) equal to $BE$ [thus, $BE$ and $EF$ is equal to $AF$]."
    (step3 : |(e─b)| + |(e─f)| = |(f─a)|) := by euclid_apply (helper_3_7_step3 a e f d AD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "$AE$ (is) equal to $BE$" (show |(a─e)| = |(e─b)|; assumption)))

  euclid_sentence "3.7.4"
    "Thus, $AF$ (is) greater than $BF$."
    (step4 : |(f─a)| > |(f─b)|) := by euclid_apply (helper_3_7_step4 (by euclid_assumption "" (show |(e─b)| + |(e─f)| > |(b─f)|; assumption)) (by euclid_assumption "" (show |(e─b)| + |(e─f)| = |(f─a)|; assumption)))

  -- @assumption_valid
  have step5_assumption1 : |(e─b)| = |(e─c)| := by euclid_finish
  -- @assumption_valid
  have step5_assumption2 : |(f─e)| = |(f─e)| := by rfl
  -- @assumption ("$BE$ is equal to $CE$", |(e─b)| = |(e─c)|)
  -- @assumption ("$FE$ (is) common", |(f─e)| = |(f─e)|)
  euclid_sentence "3.7.5"
    "Again, since $BE$ is equal to $CE$, and $FE$ (is) common, the two (straight-lines) $BE$, $EF$ are equal to the two (straight-lines) $CE$, $EF$ (respectively)."
    (step5 : |(e─b)| = |(e─c)| ∧ |(e─f)| = |(e─f)|) := by euclid_apply (helper_3_7_step5 (by euclid_assumption "$BE$ is equal to $CE$" (show |(e─b)| = |(e─c)|; assumption)) (by euclid_assumption "$FE$ (is) common" (show |(f─e)| = |(f─e)|; assumption)))

  euclid_sentence "3.7.6"
    "But, angle $BEF$ (is) also greater than angle $CEF$.$^\\ddag$"
    (step6 : ∠ b:e:f > ∠ c:e:f) := by euclid_apply (helper_3_7_step6 (by euclid_assumption "" (show ∠ b:e:f > ∠ c:e:f; assumption)))

  euclid_sentence "3.7.7"
    "Thus, the base $BF$ is greater than the base $CF$."
    (step7 : |(b─f)| > |(c─f)|) := by euclid_apply (helper_3_7_step7 ABCD a d e f b c AD CE BE BF (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show formTriangle e b f BE BF AD; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─c)|; assumption)) (by euclid_assumption "" (show ∠ b:e:f > ∠ c:e:f; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)))

  euclid_sentence "3.7.8"
    "Thus, the base $BF$ is greater than the base $CF$ [Prop.~1.24]."
    (step8 : |(b─f)| > |(c─f)|) := by euclid_apply (helper_3_7_step8 ABCD a d e f b c AD CE BE BF (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show formTriangle e b f BE BF AD; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─c)|; assumption)) (by euclid_assumption "" (show ∠ b:e:f > ∠ c:e:f; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)))

  euclid_sentence "3.7.9"
    "So, for the same (reasons), $CF$ is also greater than $FG$."
    (step9 : |(f─c)| > |(f─g)|) := by euclid_apply (helper_3_7_step9 ABCD a d e f c g AD CE GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show ∠ c:e:f > ∠ g:e:f; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)))

  -- H is constructed (by I.23) such that ∠FEH = ∠GEF; FH is joined.
  -- Placed here (before step11 introduces subtraction) so euclid_apply for FH/EH
  -- doesn't encounter the HSub term in context.
  -- hh_exist omits opposingSides to avoid poisoning euclid_finish via SMT translation;
  -- hh_opp is proved separately as a standalone sorry node just before exact.
  have hh_exist : ∃ h : Point, h.onCircle ABCD ∧ ∠ f:e:h = ∠ g:e:f ∧ h ≠ g := by euclid_apply (helper_3_7_hh_exist ABCD a b c d e f g AD GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show |(f─a)| > |(f─b)|; assumption)) (by euclid_assumption "" (show |(b─f)| > |(c─f)|; assumption)) (by euclid_assumption "" (show |(f─c)| > |(f─g)|; assumption)))
  obtain ⟨h, hh_on, hh_ang_pre, hh_ne_g⟩ := hh_exist
  euclid_apply (line_from_points f h) as FH
  euclid_apply (line_from_points e h) as EH

  -- @assumption_gap
  have step10_assumption1 : |(g─f)| + |(f─e)| > |(g─e)| := by euclid_apply (helper_3_7_step10_assumption1 ABCD a d e f g AD GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)))
  -- @assumption_valid
  have step10_assumption2 : |(e─g)| = |(e─d)| := by euclid_finish
  -- @assumption ("$GF$ and $FE$ are greater than $EG$", |(g─f)| + |(f─e)| > |(g─e)|)
  -- @assumption ("$EG$ (is) equal to $ED$", |(e─g)| = |(e─d)|)
  euclid_sentence "3.7.10"
    "Again, since $GF$ and $FE$ are greater than $EG$ [Prop.~1.20], and $EG$ (is) equal to $ED$, $GF$ and $FE$ are thus greater than $ED$."
    (step10 : |(g─f)| + |(f─e)| > |(e─d)|) := by euclid_apply (helper_3_7_step10 ABCD a d e f g AD GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "$GF$ and $FE$ are greater than $EG$" (show |(g─f)| + |(f─e)| > |(g─e)|; assumption)) (by euclid_assumption "$EG$ (is) equal to $ED$" (show |(e─g)| = |(e─d)|; assumption)))

  euclid_sentence "3.7.11"
    "Let $EF$ be taken from both."
    (step11 : |(g─f)| > |(e─d)| - |(e─f)|) := by euclid_apply (helper_3_7_step11 (by euclid_assumption "" (show |(g─f)| + |(f─e)| > |(e─d)|; assumption)))

  euclid_sentence "3.7.12"
    "Thus, the remainder $GF$ is greater than the remainder $FD$."
    (step12 : |(g─f)| > |(f─d)|) := by euclid_apply (helper_3_7_step12 (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show |(g─f)| + |(f─e)| > |(e─d)|; assumption)))

  euclid_sentence "3.7.13"
    "Thus, $FA$ (is) the greatest (straight-line),"
    (step13 : |(f─a)| > |(f─b)|) := by euclid_apply (helper_3_7_step13 (by euclid_assumption "" (show |(f─a)| > |(f─b)|; assumption)))

  euclid_sentence "3.7.14"
    "$FD$ the least,"
    (step14 : |(f─g)| > |(f─d)|) := by euclid_apply (helper_3_7_step14 (by euclid_assumption "" (show |(g─f)| > |(f─d)|; assumption)))

  euclid_sentence "3.7.15"
    "and $FB$ (is) greater than $FC$,"
    (step15 : |(f─b)| > |(f─c)|) := by euclid_apply (helper_3_7_step15 (by euclid_assumption "" (show |(b─f)| > |(c─f)|; assumption)))

  euclid_sentence "3.7.16"
    "and $FC$ than $FG$."
    (step16 : |(f─c)| > |(f─g)|) := by euclid_apply (helper_3_7_step16 (by euclid_assumption "" (show |(f─c)| > |(f─g)|; assumption)))

  euclid_wts "3.7.17"
    "I also say that from point $F$ only two equal (straight-lines) will radiate towards (the circumference of) circle $ABCD$, (one) on each (side) of the least (straight-line) $FD$."

  euclid_sentence "3.7.18"
    "For let the (angle) $FEH$, equal to angle $GEF$, be constructed on the straight-line $EF$, at the point $E$ on it [Prop.~1.23], and let $FH$ be joined."
    (step18 : ∠ f:e:h = ∠ g:e:f ∧ distinctPointsOnLine f h FH) := by euclid_apply (helper_3_7_step18 ABCD a d e f g h AD GE FH (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show ∠ f:e:h = ∠ g:e:f; assumption)))

  -- @assumption_gap
  have step19_assumption1 : |(e─g)| = |(e─h)| := by euclid_apply (helper_3_7_step19_assumption1 ABCD e g h (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onCircle ABCD; assumption)))
  -- @assumption_valid
  have step19_assumption2 : |(e─f)| = |(e─f)| := by rfl
  -- @assumption ("$GE$ is equal to $EH$", |(e─g)| = |(e─h)|)
  -- @assumption ("$EF$ (is) common", |(e─f)| = |(e─f)|)
  euclid_sentence "3.7.19"
    "Therefore, since $GE$ is equal to $EH$, and $EF$ (is) common, the two (straight-lines) $GE$, $EF$ are equal to the two (straight-lines) $HE$, $EF$ (respectively)."
    (step19 : |(e─g)| = |(e─h)| ∧ |(e─f)| = |(e─f)|) := by euclid_apply (helper_3_7_step19 (by euclid_assumption "$GE$ is equal to $EH$" (show |(e─g)| = |(e─h)|; assumption)) (by euclid_assumption "$EF$ (is) common" (show |(e─f)| = |(e─f)|; assumption)))

  euclid_sentence "3.7.20"
    "And angle $GEF$ (is) equal to angle $HEF$."
    (step20 : ∠ g:e:f = ∠ h:e:f) := by euclid_apply (helper_3_7_step20 ABCD e f g h (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show h.onCircle ABCD; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show ∠ f:e:h = ∠ g:e:f; assumption)))

  euclid_sentence "3.7.21"
    "Thus, the base $FG$ is equal to the base $FH$ [Prop.~1.4]."
    (step21 : |(f─g)| = |(f─h)|) := by euclid_apply (helper_3_7_step21 ABCD a d e f g h AD GE EH FH (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine EH; assumption)) (by euclid_assumption "" (show h.onLine EH; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show |(e─g)| = |(e─h)|; assumption)) (by euclid_assumption "" (show ∠ g:e:f = ∠ h:e:f; assumption)))

  euclid_wts "3.7.22"
    "So I say that another (straight-line) equal to $FG$ will not radiate towards (the circumference of) the circle from point $F$."

  have habsurd1 : ¬(∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h) := by
    intro hsuppose1
    obtain ⟨k, hk_on, hk_eq, hk_ne_g, hk_ne_h⟩ := hsuppose1
    euclid_sentence "3.7.23"
      "For, if possible, let $FK$ (so) radiate."
      (step23 : k.onCircle ABCD ∧ |(f─k)| = |(f─g)|) := by euclid_apply (helper_3_7_step23 ABCD f g k (by euclid_assumption "" (show k.onCircle ABCD; assumption)) (by euclid_assumption "" (show |(f─k)| = |(f─g)|; assumption)))

    -- @assumption_valid
    have step24_assumption1 : |(f─k)| = |(f─g)| := by assumption
    -- @assumption_valid
    have step24_assumption2 : |(f─h)| = |(f─g)| := by linarith
    -- @assumption ("$FK$ is equal to $FG$", |(f─k)| = |(f─g)|)
    -- @assumption ("$FH$ [is equal] to $FG$", |(f─h)| = |(f─g)|)
    euclid_sentence "3.7.24"
      "And since $FK$ is equal to $FG$, but $FH$ [is equal] to $FG$, $FK$ is thus also equal to $FH$,"
      (step24 : |(f─k)| = |(f─h)|) := by euclid_apply (helper_3_7_step24 (by euclid_assumption "$FK$ is equal to $FG$" (show |(f─k)| = |(f─g)|; assumption)) (by euclid_assumption "$FH$ [is equal] to $FG$" (show |(f─h)| = |(f─g)|; assumption)))

    euclid_sentence "3.7.25"
      "the nearer to the (straight-line) through the center equal to the further away."
      (step25 : |(f─k)| = |(f─h)|) := by euclid_apply (helper_3_7_step25 (by euclid_assumption "" (show |(f─k)| = |(f─h)|; assumption)))

    euclid_sentence "3.7.26"
      "The very thing (is) impossible."
      (step26 : False) := by euclid_apply (helper_3_7_step26 ABCD a b c d e f g h k AD (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onCircle ABCD; assumption)) (by euclid_assumption "" (show k.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show k ≠ g; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show |(f─a)| > |(f─b)|; assumption)) (by euclid_assumption "" (show |(b─f)| > |(c─f)|; assumption)) (by euclid_assumption "" (show |(f─c)| > |(f─g)|; assumption)) (by euclid_assumption "" (show |(f─g)| > |(f─d)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(f─h)|; assumption)) (by euclid_assumption "" (show |(f─k)| = |(f─g)|; assumption)))
    exact step26

  -- Reductio close: the supposition is refuted.
  euclid_sentence "3.7.27"
    "Thus, another (straight-line) equal to $GF$ will not radiate from the point $F$ towards (the circumference of) the circle."
    (step27 : ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h)) := by euclid_apply (helper_3_7_step27 (by euclid_assumption "" (show ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h); assumption)))

  euclid_sentence "3.7.28"
    "Thus, (there is) only one (such straight-line)."
    (step28 : ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h) := by euclid_apply (helper_3_7_step28 ABCD f g h (by euclid_assumption "" (show ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h); assumption)))

  have hh_opp : h.opposingSides g AD := by euclid_apply (helper_3_7_hh_opp ABCD a b c d e f g h AD (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show |(f─a)| > |(f─b)|; assumption)) (by euclid_assumption "" (show |(b─f)| > |(c─f)|; assumption)) (by euclid_assumption "" (show |(f─c)| > |(f─g)|; assumption)) (by euclid_assumption "" (show ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h; assumption)))
  exact ⟨step13, step15, step16, step14, h, hh_on, hh_opp, step21.symm, step28⟩
  euclid_conclude_sentence "3.7.29"
    "Thus, if some point, which is not the center of the circle, is taken on the diameter of a circle, and some straight-lines radiate from the point towards the (circumference of the) circle, (then) the greatest (straight-line) will be that on which the center (lies), and the least the remainder (of the same diameter). And for the others, a (straight-line) nearer to the (straight-line) through the center is always greater than a (straight-line) further away. And only two equal (straight-lines) will radiate from the same point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). (Which is) the very thing it was required to show."

end Elements.Book3
