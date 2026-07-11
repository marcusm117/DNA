import SystemE
import Book3.Prop16.step1
import Book3.Prop16.step2
import Book3.Prop16.step3
import Book3.Prop16.step4
import Book3.Prop16.step5
import Book3.Prop16.step6
import Book3.Prop16.step7
import Book3.Prop16.step8
import Book3.Prop16.step9
import Book3.Prop16.step10
import Book3.Prop16.step11
import Book3.Prop16.step13
import Book3.Prop16.step14
import Book3.Prop16.step15
import Book3.Prop16.step16
import Book3.Prop16.step17
import Book3.Prop16.step18
import Book3.Prop16.step19
import Book3.Prop16.hDC
import Book3.Prop16.hgDG
import Book3.Prop16.hh
import Book3.Prop16.step15_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_16 : ∀ (a b d e : Point) (ABC : Circle) (AE : Line),
    d.isCentre ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ between a d b ∧
    distinctPointsOnLine a e AE ∧
    ∠ e:a:b = ∟ →
    ((∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) ∧
    (∀ (FA : Line), a.onLine FA → FA ≠ AE → FA.intersectsCircle ABC) :=
by
  euclid_intros
  euclid_intro_sentence "3.16.0"
    "A (straight-line) drawn at right-angles to the diameter of a circle, from its end, will fall outside the circle. And another straight-line cannot be inserted into the space between the (aforementioned) straight-line and the circumference. And the angle of the semi-circle is greater than any acute rectilinear angle whatsoever, and the remaining (angle is) less (than any acute rectilinear angle). Let $ABC$ be a circle around the center $D$ and the diameter $AB$. I say that the (straight-line) drawn from $A$, at right-angles to $AB$ [Prop~1.11], from its end, will fall outside the circle."

  have habsurd1 : ¬(AE.intersectsCircle ABC) := by
    intro hsuppose1
    euclid_sentence "3.16.1"
      "For (if) not (then), if possible, let it fall inside, like $CA$ (in the figure),"
      (step1 : ∃ c : Point, c.onLine AE ∧ c.onCircle ABC ∧ c ≠ a) := by euclid_apply (helper_3_16_step1 a ABC AE (by euclid_assumption "" (show AE.intersectsCircle ABC; assumption)))
    obtain ⟨c, hcAE, hcABC, hcne⟩ := step1
    have hDC : ∃ DC : Line, d.onLine DC ∧ c.onLine DC := by euclid_apply (helper_3_16_hDC d c ABC (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)))
    obtain ⟨DC, hDCd, hDCc⟩ := hDC
    euclid_sentence "3.16.2"
      "and let $DC$ be joined."
      (step2 : distinctPointsOnLine d c DC) := by euclid_apply (helper_3_16_step2 d c ABC DC (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)))
    -- @assumption_valid
    have step3_assumption1 : |(d─a)| = |(d─c)| := by euclid_finish
    -- @assumption ("$DA$ is equal to $DC$", |(d─a)| = |(d─c)|)
    euclid_sentence "3.16.3"
      "Since $DA$ is equal to $DC$, angle $DAC$ is also equal to angle $ACD$ [Prop.~1.5]."
      (step3 : ∠ d:a:c = ∠ a:c:d) := by euclid_apply (helper_3_16_step3 d a c b e ABC AE DC (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show c.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine d c DC; assumption)) (by euclid_assumption "$DA$ is equal to $DC$" (show |(d─a)| = |(d─c)|; assumption)))
    euclid_sentence "3.16.4"
      "And $DAC$ (is) a right-angle."
      (step4 : ∠ d:a:c = ∟) := by euclid_apply (helper_3_16_step4 d a c b e AE (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show c.onLine AE; assumption)))
    euclid_sentence "3.16.5"
      "Thus, $ACD$ (is) also a right-angle."
      (step5 : ∠ a:c:d = ∟) := by euclid_apply (helper_3_16_step5 d a c (by euclid_assumption "" (show ∠ d:a:c = ∠ a:c:d; assumption)) (by euclid_assumption "" (show ∠ d:a:c = ∟; assumption)))
    euclid_sentence "3.16.6"
      "So, in triangle $ACD$, the two angles $DAC$ and $ACD$ are equal to two right-angles."
      (step6 : ∠ d:a:c + ∠ a:c:d = ∟ + ∟) := by euclid_apply (helper_3_16_step6 d a c (by euclid_assumption "" (show ∠ d:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)))
    euclid_sentence "3.16.7"
      "The very thing is impossible [Prop.~1.17]."
      (step7 : False) := by euclid_apply (helper_3_16_step7 d a c ABC DC (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show ∠ d:a:c + ∠ a:c:d = ∟ + ∟; assumption)))
    exact step7

  euclid_sentence "3.16.8"
    "Thus, the (straight-line) drawn from point $A$, at right-angles to $BA$, will not fall inside the circle."
    (step8 : ¬(AE.intersectsCircle ABC)) := by euclid_apply (helper_3_16_step8 ABC AE (by euclid_assumption "" (show ¬AE.intersectsCircle ABC; assumption)))

  euclid_sentence "3.16.9"
    "So, similarly, we can show that neither (will it fall) on the circumference."
    (step9 : ¬(∃ c : Point, c.onLine AE ∧ c.onCircle ABC ∧ c ≠ a)) := by euclid_apply (helper_3_16_step9 a ABC AE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show ¬AE.intersectsCircle ABC; assumption)))

  euclid_sentence "3.16.10"
    "Thus, (it will fall) outside (the circle)."
    (step10 : (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) := by euclid_apply (helper_3_16_step10 a ABC AE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show ¬AE.intersectsCircle ABC; assumption)))

  euclid_sentence "3.16.11"
    "Let it fall like $AE$ (in the figure)."
    (step11 : (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) := by euclid_apply (helper_3_16_step11 (by euclid_assumption "" (show (∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC; assumption)))

  euclid_wts "3.16.12"
    "So, I say that another straight-line cannot be inserted into the space between the straight-line $AE$ and the circumference $CHA$."

  have habsurd2 : ¬(∃ (FA : Line), a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC) := by
    intro hsuppose2
    obtain ⟨FA, hFAon, hFAne, hFAnot⟩ := hsuppose2
    euclid_sentence "3.16.13"
      "For, if possible, let it be inserted like $FA$ (in the figure),"
      (step13 : a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC) := by euclid_apply (helper_3_16_step13 a ABC AE FA (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show FA ≠ AE; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)))
    have hgDG : ∃ (g : Point) (DG_line : Line),
        g.onLine FA ∧ ∠ a:g:d = ∟ ∧ d.onLine DG_line ∧ g.onLine DG_line ∧ a ≠ g := by euclid_apply (helper_3_16_hgDG a d ABC FA AE e b (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show FA ≠ AE; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)))
    obtain ⟨g, DG_line, hgFA, hgperp, hDGd, hDGg, hagne⟩ := hgDG
    have hh : ∃ h : Point, h.onCircle ABC ∧ h.onLine DG_line := by euclid_apply (helper_3_16_hh d ABC DG_line (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onLine DG_line; assumption)))
    obtain ⟨h, hhcircle, hhline⟩ := hh
    euclid_sentence "3.16.14"
      "and let $DG$ be drawn from point $D$, perpendicular to $FA$ [Prop.~1.12]."
      (step14 : g.onLine FA ∧ ∠ a:g:d = ∟) := by euclid_apply (helper_3_16_step14 a g d ABC FA (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show g.onLine FA; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ g; assumption)) (by euclid_assumption "" (show ∠ a:g:d = ∟; assumption)))
    -- @assumption_valid
    have step15_assumption1 : ∠ a:g:d = ∟ := by assumption
    -- @assumption_gap
    have step15_assumption2 : ∠ d:a:g < ∟ := by euclid_apply (helper_3_16_step15_assumption2 a g d ABC FA (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show g.onLine FA; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ g; assumption)) (by euclid_assumption "" (show ∠ a:g:d = ∟; assumption)))
    -- @assumption ("$AGD$ is a right-angle", ∠ a:g:d = ∟)
    -- @assumption ("$DAG$ (is) less than a right-angle", ∠ d:a:g < ∟)
    euclid_sentence "3.16.15"
      "And since $AGD$ is a right-angle, and $DAG$ (is) less than a right-angle, $AD$ (is) thus greater than $DG$ [Prop.~1.19]."
      (step15 : |(a─d)| > |(d─g)|) := by euclid_apply (helper_3_16_step15 a g d ABC FA (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show g.onLine FA; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ g; assumption)) (by euclid_assumption "$AGD$ is a right-angle" (show ∠ a:g:d = ∟; assumption)) (by euclid_assumption "$DAG$ (is) less than a right-angle" (show ∠ d:a:g < ∟; assumption)))
    euclid_sentence "3.16.16"
      "And $DA$ (is) equal to $DH$."
      (step16 : |(d─a)| = |(d─h)|) := by euclid_apply (helper_3_16_step16 a h d ABC (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)))
    euclid_sentence "3.16.17"
      "Thus, $DH$ (is) greater than $DG$, the lesser than the greater."
      (step17 : |(d─h)| > |(d─g)|) := by euclid_apply (helper_3_16_step17 a d g h (by euclid_assumption "" (show |(a─d)| > |(d─g)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─h)|; assumption)))
    euclid_sentence "3.16.18"
      "The very thing is impossible."
      (step18 : False) := by euclid_apply (helper_3_16_step18 d g h ABC FA (by euclid_assumption "" (show d.isCentre ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine FA; assumption)) (by euclid_assumption "" (show ¬FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show |(d─h)| > |(d─g)|; assumption)))
    exact step18

  euclid_sentence "3.16.19"
    "Thus, another straight-line cannot be inserted into the space between the straight-line ($AE$) and the circumference."
    (step19 : ¬(∃ (FA : Line), a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC)) := by euclid_apply (helper_3_16_step19 a ABC AE (by euclid_assumption "" (show ¬∃ FA, a.onLine FA ∧ FA ≠ AE ∧ ¬FA.intersectsCircle ABC; assumption)))

  euclid_wts "3.16.20"
    "And I also say that the semi-circular angle contained by the straight-line $BA$ and the circumference $CHA$ is greater than any acute rectilinear angle whatsoever, and the remaining (angle) contained by the circumference $CHA$ and the straight-line $AE$ is less than any acute rectilinear angle whatsoever."

  -- @euclid_gap: horn angles (semi-circular ∧ arc, curvilinear ∧ tangent) have no sort in
  -- System E; sentences 21–25 are textually preserved but carry no expressible claim.
  euclid_conclude_sentence "3.16.21"
    "For if any rectilinear angle is greater than the (angle) contained by the straight-line $BA$ and the circumference $CHA$, or less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$, (then) a straight-line can be inserted into the space between the circumference $CHA$ and the straight-line $AE$---anything which will make (an angle) contained by straight-lines greater than the angle contained by the straight-line $BA$ and the circumference $CHA$, or less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$."

  euclid_conclude_sentence "3.16.22"
    "But (such a straight-line) cannot be inserted."

  euclid_conclude_sentence "3.16.23"
    "Thus, an acute (angle) contained by straight-lines cannot be greater than the angle contained by the straight-line $BA$ and the circumference $CHA$,"

  euclid_conclude_sentence "3.16.24"
    "neither (can it be) less than the (angle) contained by the circumference $CHA$ and the straight-line $AE$."

  euclid_conclude_sentence "3.16.25"
    "So, from this, (it is) manifest that a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle [and that the straight-line touches the circle at a single point, inasmuch as it was also shown that a (straight-line) meeting (the circle) at two (points) falls inside it [Prop.~3.2]\\,]."

  exact ⟨step11, fun FA hFA hne => by_contra fun h => step19 ⟨FA, hFA, hne, h⟩⟩
  euclid_conclude_sentence "3.16.26"
    "(Which is) the very thing it was required to show."

end Elements.Book3
