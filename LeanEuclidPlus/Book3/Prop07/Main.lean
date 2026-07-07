import SystemE
import Book1.Prop04.Main
import Book1.Prop20.Main
import Book1.Prop23.Main
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Faithful to Euclid's DEMONSTRATION (not the enunciation's "always"): he names the three other lines
-- FB, FC, FG and proves the specific chain FA>FB>FC>FG>FD (greatest/least = the ends of the chain), under
-- the figure ordering ∠BEF>∠CEF>∠GEF; plus the two-equal (a mirror H on the far side of AD, and uniqueness).
-- Modeled on the faithful sibling Book3/Prop08. (The earlier ∀-over-all-points version over-generalized
-- beyond what the proof actually demonstrates — corrected 2026-07-06.)
set_option systemE.solverTime 30 in
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
  have BE : Line := by sorry
  have CE : Line := by sorry
  have GE : Line := by sorry
  euclid_sentence "3.7.1"
    "For let $BE$, $CE$, and $GE$ be joined."
    (step1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c e CE ∧ distinctPointsOnLine g e GE) := by sorry

  have BF : Line := by sorry
  -- @assumption_gap
  have step2_assumption1 : formTriangle e b f BE BF AD := by sorry
  -- @assumption ("for every triangle (any) two sides are greater than the remaining (side)", formTriangle e b f BE BF AD)
  euclid_sentence "3.7.2"
    "And since for every triangle (any) two sides are greater than the remaining (side) [Prop.~1.20], $EB$ and $EF$ is thus greater than $BF$."
    (step2 : |(e─b)| + |(e─f)| > |(b─f)|) := by sorry

  -- @assumption_valid
  have step3_assumption1 : |(a─e)| = |(e─b)| := by euclid_finish
  -- @assumption ("$AE$ (is) equal to $BE$", |(a─e)| = |(e─b)|)
  euclid_sentence "3.7.3"
    "And $AE$ (is) equal to $BE$ [thus, $BE$ and $EF$ is equal to $AF$]."
    (step3 : |(e─b)| + |(e─f)| = |(f─a)|) := by sorry

  euclid_sentence "3.7.4"
    "Thus, $AF$ (is) greater than $BF$."
    (step4 : |(f─a)| > |(f─b)|) := by sorry

  -- @assumption_valid
  have step5_assumption1 : |(e─b)| = |(e─c)| := by euclid_finish
  -- @assumption_valid
  have step5_assumption2 : |(f─e)| = |(f─e)| := by rfl
  -- @assumption ("$BE$ is equal to $CE$", |(e─b)| = |(e─c)|)
  -- @assumption ("$FE$ (is) common", |(f─e)| = |(f─e)|)
  euclid_sentence "3.7.5"
    "Again, since $BE$ is equal to $CE$, and $FE$ (is) common, the two (straight-lines) $BE$, $EF$ are equal to the two (straight-lines) $CE$, $EF$ (respectively)."
    (step5 : |(e─b)| = |(e─c)| ∧ |(e─f)| = |(e─f)|) := by sorry

  euclid_sentence "3.7.6"
    "But, angle $BEF$ (is) also greater than angle $CEF$.$^\\ddag$"
    (step6 : ∠ b:e:f > ∠ c:e:f) := by sorry

  euclid_sentence "3.7.7"
    "Thus, the base $BF$ is greater than the base $CF$."
    (step7 : |(b─f)| > |(c─f)|) := by sorry

  euclid_sentence "3.7.8"
    "Thus, the base $BF$ is greater than the base $CF$ [Prop.~1.24]."
    (step8 : |(b─f)| > |(c─f)|) := by sorry

  euclid_sentence "3.7.9"
    "So, for the same (reasons), $CF$ is also greater than $FG$."
    (step9 : |(f─c)| > |(f─g)|) := by sorry

  -- @assumption_gap
  have step10_assumption1 : |(g─f)| + |(f─e)| > |(g─e)| := by sorry
  -- @assumption_valid
  have step10_assumption2 : |(e─g)| = |(e─d)| := by euclid_finish
  -- @assumption ("$GF$ and $FE$ are greater than $EG$", |(g─f)| + |(f─e)| > |(g─e)|)
  -- @assumption ("$EG$ (is) equal to $ED$", |(e─g)| = |(e─d)|)
  euclid_sentence "3.7.10"
    "Again, since $GF$ and $FE$ are greater than $EG$ [Prop.~1.20], and $EG$ (is) equal to $ED$, $GF$ and $FE$ are thus greater than $ED$."
    (step10 : |(g─f)| + |(f─e)| > |(e─d)|) := by sorry

  euclid_sentence "3.7.11"
    "Let $EF$ be taken from both."
    (step11 : |(g─f)| > |(e─d)| - |(e─f)|) := by sorry

  euclid_sentence "3.7.12"
    "Thus, the remainder $GF$ is greater than the remainder $FD$."
    (step12 : |(g─f)| > |(f─d)|) := by sorry

  euclid_sentence "3.7.13"
    "Thus, $FA$ (is) the greatest (straight-line),"
    (step13 : |(f─a)| > |(f─b)|) := by sorry

  euclid_sentence "3.7.14"
    "$FD$ the least,"
    (step14 : |(f─g)| > |(f─d)|) := by sorry

  euclid_sentence "3.7.15"
    "and $FB$ (is) greater than $FC$,"
    (step15 : |(f─b)| > |(f─c)|) := by sorry

  euclid_sentence "3.7.16"
    "and $FC$ than $FG$."
    (step16 : |(f─c)| > |(f─g)|) := by sorry

  euclid_wts "3.7.17"
    "I also say that from point $F$ only two equal (straight-lines) will radiate towards (the circumference of) circle $ABCD$, (one) on each (side) of the least (straight-line) $FD$."

  -- H is constructed (by I.23) such that ∠FEH = ∠GEF; FH is joined.
  have h : Point := by sorry
  have FH : Line := by sorry
  have EH : Line := by sorry
  euclid_sentence "3.7.18"
    "For let the (angle) $FEH$, equal to angle $GEF$, be constructed on the straight-line $EF$, at the point $E$ on it [Prop.~1.23], and let $FH$ be joined."
    (step18 : ∠ f:e:h = ∠ g:e:f ∧ distinctPointsOnLine f h FH) := by sorry

  -- @assumption_gap
  have step19_assumption1 : |(e─g)| = |(e─h)| := by sorry
  -- @assumption_valid
  have step19_assumption2 : |(e─f)| = |(e─f)| := by rfl
  -- @assumption ("$GE$ is equal to $EH$", |(e─g)| = |(e─h)|)
  -- @assumption ("$EF$ (is) common", |(e─f)| = |(e─f)|)
  euclid_sentence "3.7.19"
    "Therefore, since $GE$ is equal to $EH$, and $EF$ (is) common, the two (straight-lines) $GE$, $EF$ are equal to the two (straight-lines) $HE$, $EF$ (respectively)."
    (step19 : |(e─g)| = |(e─h)| ∧ |(e─f)| = |(e─f)|) := by sorry

  euclid_sentence "3.7.20"
    "And angle $GEF$ (is) equal to angle $HEF$."
    (step20 : ∠ g:e:f = ∠ h:e:f) := by sorry

  euclid_sentence "3.7.21"
    "Thus, the base $FG$ is equal to the base $FH$ [Prop.~1.4]."
    (step21 : |(f─g)| = |(f─h)|) := by sorry

  euclid_wts "3.7.22"
    "So I say that another (straight-line) equal to $FG$ will not radiate towards (the circumference of) the circle from point $F$."

  have habsurd1 : ¬(∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h) := by
    intro hsuppose1
    have k : Point := by sorry
    have hk_on : k.onCircle ABCD := by sorry
    have hk_eq : |(f─k)| = |(f─g)| := by sorry
    have hk_ne_g : k ≠ g := by sorry
    have hk_ne_h : k ≠ h := by sorry
    euclid_sentence "3.7.23"
      "For, if possible, let $FK$ (so) radiate."
      (step23 : k.onCircle ABCD ∧ |(f─k)| = |(f─g)|) := by sorry

    -- @assumption_valid
    have step24_assumption1 : |(f─k)| = |(f─g)| := by assumption
    -- @assumption_valid
    have step24_assumption2 : |(f─h)| = |(f─g)| := by linarith
    -- @assumption ("$FK$ is equal to $FG$", |(f─k)| = |(f─g)|)
    -- @assumption ("$FH$ [is equal] to $FG$", |(f─h)| = |(f─g)|)
    euclid_sentence "3.7.24"
      "And since $FK$ is equal to $FG$, but $FH$ [is equal] to $FG$, $FK$ is thus also equal to $FH$,"
      (step24 : |(f─k)| = |(f─h)|) := by sorry

    euclid_sentence "3.7.25"
      "the nearer to the (straight-line) through the center equal to the further away."
      (step25 : |(f─k)| = |(f─h)|) := by sorry

    euclid_sentence "3.7.26"
      "The very thing (is) impossible."
      (step26 : False) := by sorry
    exact step26

  -- Reductio close: the supposition is refuted.
  euclid_sentence "3.7.27"
    "Thus, another (straight-line) equal to $GF$ will not radiate from the point $F$ towards (the circumference of) the circle."
    (step27 : ¬ (∃ k : Point, k.onCircle ABCD ∧ |(f─k)| = |(f─g)| ∧ k ≠ g ∧ k ≠ h)) := by sorry

  euclid_sentence "3.7.28"
    "Thus, (there is) only one (such straight-line)."
    (step28 : ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h) := by sorry

  have hh_on : h.onCircle ABCD := by sorry
  have hh_opp : h.opposingSides g AD := by sorry
  exact ⟨step13, step15, step16, step14, h, hh_on, hh_opp, step21.symm, step28⟩
  euclid_conclude_sentence "3.7.29"
    "Thus, if some point, which is not the center of the circle, is taken on the diameter of a circle, and some straight-lines radiate from the point towards the (circumference of the) circle, (then) the greatest (straight-line) will be that on which the center (lies), and the least the remainder (of the same diameter). And for the others, a (straight-line) nearer to the (straight-line) through the center is always greater than a (straight-line) further away. And only two equal (straight-lines) will radiate from the same point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). (Which is) the very thing it was required to show."

end Elements.Book3
