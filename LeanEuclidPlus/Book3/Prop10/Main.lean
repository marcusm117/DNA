import SystemE
import Book.Prop10
import Book.Prop11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open Elements.Book1

namespace Elements.Book3

-- orchestrator-agreed: matches enunciation — two distinct circles cannot share 3 distinct points ("cut at more than two points").
set_option systemE.solverTime 30 in
theorem proposition_10 : ∀ (ABC DEF : Circle),
  ABC ≠ DEF →
  ¬ ∃ (p q r : Point),
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    p.onCircle ABC ∧ q.onCircle ABC ∧ r.onCircle ABC ∧
    p.onCircle DEF ∧ q.onCircle DEF ∧ r.onCircle DEF :=
by
  euclid_intros
  euclid_intro_sentence "3.10.0"
    "A circle does not cut a(nother) circle at more than two points."

  -- Flat reductio: euclid_intros has introduced the existential as a hypothesis and set the goal to
  -- False. Obtain witness points B, G, H (3 of Euclid's 4; F is named in step1 text but unused after).
  -- h_sup is a copy so the original existential hypothesis remains in context.
  have h_sup : ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      p.onCircle ABC ∧ q.onCircle ABC ∧ r.onCircle ABC ∧
      p.onCircle DEF ∧ q.onCircle DEF ∧ r.onCircle DEF := by assumption
  obtain ⟨b, g, h, hbg, hbh, hgh, hbABC, hgABC, hhABC, hbDEF, hgDEF, hhDEF⟩ := h_sup

  euclid_sentence "3.10.1"
    "For, if possible, let the circle $ABC$ cut the circle $DEF$ at more than two points, $B$, $G$, $F$, and $H$."
    (step1 : b ≠ g ∧ b ≠ h ∧ g ≠ h ∧ b.onCircle ABC ∧ g.onCircle ABC ∧ h.onCircle ABC ∧ b.onCircle DEF ∧ g.onCircle DEF ∧ h.onCircle DEF) := by sorry

  euclid_apply (line_from_points b h) as BH
  euclid_apply (line_from_points b g) as BG
  euclid_apply (Elements.Book1.proposition_10 b h BH) as k
  euclid_apply (Elements.Book1.proposition_10 b g BG) as l
  euclid_sentence "3.10.2"
    "And $BH$ and $BG$ being joined, let them (then) be cut in half at points $K$ and $L$ (respectively)."
    (step2 : between b k h ∧ |(b─k)| = |(k─h)| ∧ between b l g ∧ |(b─l)| = |(l─g)|) := by sorry

  euclid_apply (proposition_11 b h k BH) as c₀
  euclid_apply (line_from_points k c₀) as AC
  euclid_apply (extend_point AC c₀ k) as a
  euclid_apply (proposition_11 b g l BG) as m₀
  euclid_apply (line_from_points l m₀) as NO
  euclid_apply (extend_point NO m₀ l) as e
  euclid_sentence "3.10.3"
    "And $KC$ and $LM$ being drawn at right-angles to $BH$ and $BG$ from $K$ and $L$ (respectively) [Prop.~1.11], let them (then) be drawn through to points $A$ and $E$ (respectively)."
    (step3 : ∠ b:k:c₀ = ∟ ∧ a.onLine AC ∧ ∠ b:l:m₀ = ∟ ∧ e.onLine NO) := by sorry

  -- @assumption ("in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles", k.onLine AC ∧ between b k h ∧ |(b─k)| = |(k─h)| ∧ ∠ b:k:c₀ = ∟)
  euclid_sentence "3.10.4"
    "Therefore, since in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles, the center of circle $ABC$ is thus on $AC$ [Prop.~3.1~corr.]."
    (step4 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC) := by sorry

  -- @assumption ("in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles", l.onLine NO ∧ between b l g ∧ |(b─l)| = |(l─g)| ∧ ∠ b:l:m₀ = ∟)
  euclid_sentence "3.10.5"
    "Again, since in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles, the center of circle $ABC$ is thus on $NO$ [Prop.~3.1~corr.]."
    (step5 : ∃ o : Point, o.isCentre ABC ∧ o.onLine NO) := by sorry

  euclid_sentence "3.10.6"
    "And it was also shown (to be) on $AC$."
    (step6 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC) := by sorry

  have hp_exists : ∃ q : Point, q.onLine AC ∧ q.onLine NO := by sorry
  obtain ⟨p, hpAC, hpNO⟩ := hp_exists
  euclid_sentence "3.10.7"
    "And the straight-lines $AC$ and $NO$ meet at no other (point) than $P$."
    (step7 : p.onLine AC ∧ p.onLine NO) := by sorry

  euclid_sentence "3.10.8"
    "Thus, point $P$ is the center of circle $ABC$."
    (step8 : p.isCentre ABC) := by sorry

  euclid_sentence "3.10.9"
    "So, similarly, we can show that $P$ is also the center of circle $DEF$."
    (step9 : p.isCentre DEF) := by sorry

  euclid_sentence "3.10.10"
    "Thus, two circles cutting one another, $ABC$ and $DEF$, have the same center $P$."
    (step10 : p.isCentre ABC ∧ p.isCentre DEF) := by sorry

  euclid_sentence "3.10.11"
    "The very thing is impossible [Prop.~3.5]."
    (step11 : False) := by sorry

  euclid_sentence "3.10.12"
    "Thus, a circle does not cut a(nother) circle at more than two points."
    (step12 : ¬ ∃ (b₀ g₀ h₀ : Point), b₀ ≠ g₀ ∧ b₀ ≠ h₀ ∧ g₀ ≠ h₀ ∧
        b₀.onCircle ABC ∧ g₀.onCircle ABC ∧ h₀.onCircle ABC ∧
        b₀.onCircle DEF ∧ g₀.onCircle DEF ∧ h₀.onCircle DEF) := by sorry

  exact step11
  euclid_conclude_sentence "3.10.13"
    "(Which is) the very thing it was required to show."

end Elements.Book3
