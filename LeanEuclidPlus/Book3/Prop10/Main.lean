import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book3.Prop10.step1
import Book3.Prop10.step2
import Book3.Prop10.step3
import Book3.Prop10.step4
import Book3.Prop10.step5
import Book3.Prop10.step6
import Book3.Prop10.step7
import Book3.Prop10.step8
import Book3.Prop10.step9
import Book3.Prop10.step10
import Book3.Prop10.step11
import Book3.Prop10.step12
import Book3.Prop10.hp_exists
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open Elements.Book1

namespace Elements.Book3

-- orchestrator-agreed: matches enunciation — two distinct circles cannot share 3 distinct points ("cut at more than two points").
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

  have h_sup : ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      p.onCircle ABC ∧ q.onCircle ABC ∧ r.onCircle ABC ∧
      p.onCircle DEF ∧ q.onCircle DEF ∧ r.onCircle DEF := by assumption
  obtain ⟨b, g, h, hbg, hbh, hgh, hbABC, hgABC, hhABC, hbDEF, hgDEF, hhDEF⟩ := h_sup

  -- Note: Euclid names four intersection points B, G, F, H in this sentence but F is not every used in the proof and creates issues so we are unfaithful here by ommiting F.
  euclid_sentence "3.10.1"
    "For, if possible, let the circle $ABC$ cut the circle $DEF$ at more than two points, $B$, $G$, $F$, and $H$."
    (step1 : b ≠ g ∧ b ≠ h ∧ g ≠ h ∧ b.onCircle ABC ∧ g.onCircle ABC ∧ h.onCircle ABC ∧ b.onCircle DEF ∧ g.onCircle DEF ∧ h.onCircle DEF) := by euclid_apply (helper_3_10_step1 ABC DEF b g h (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show b ≠ h; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show g.onCircle DEF; assumption)) (by euclid_assumption "" (show h.onCircle DEF; assumption)))

  euclid_apply (line_from_points b h) as BH
  euclid_apply (line_from_points b g) as BG
  euclid_apply (Elements.Book1.proposition_10 b h BH) as k
  euclid_apply (Elements.Book1.proposition_10 b g BG) as l
  euclid_sentence "3.10.2"
    "And $BH$ and $BG$ being joined, let them (then) be cut in half at points $K$ and $L$ (respectively)."
    (step2 : between b k h ∧ |(b─k)| = |(k─h)| ∧ between b l g ∧ |(b─l)| = |(l─g)|) := by euclid_apply (helper_3_10_step2 b h k g l (by euclid_assumption "" (show between b k h; assumption)) (by euclid_assumption "" (show |(b─k)| = |(k─h)|; assumption)) (by euclid_assumption "" (show between b l g; assumption)) (by euclid_assumption "" (show |(b─l)| = |(l─g)|; assumption)))

  euclid_apply (proposition_11 b h k BH) as c₀
  euclid_apply (line_from_points k c₀) as AC
  euclid_apply (extend_point AC c₀ k) as a
  euclid_apply (proposition_11 b g l BG) as m₀
  euclid_apply (line_from_points l m₀) as NO
  euclid_apply (extend_point NO m₀ l) as e
  euclid_sentence "3.10.3"
    "And $KC$ and $LM$ being drawn at right-angles to $BH$ and $BG$ from $K$ and $L$ (respectively) [Prop.~1.11], let them (then) be drawn through to points $A$ and $E$ (respectively)."
    (step3 : ∠ b:k:c₀ = ∟ ∧ a.onLine AC ∧ ∠ b:l:m₀ = ∟ ∧ e.onLine NO) := by euclid_apply (helper_3_10_step3 b k c₀ l m₀ a e AC NO (by euclid_assumption "" (show ∠ b:k:c₀ = ∟; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show ∠ b:l:m₀ = ∟; assumption)) (by euclid_assumption "" (show e.onLine NO; assumption)))

  -- @assumption_valid
  have step4_assumption1 : k.onLine AC ∧ between b k h ∧ |(b─k)| = |(k─h)| ∧ ∠ b:k:c₀ = ∟ := by euclid_finish
  -- @assumption ("in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles", k.onLine AC ∧ between b k h ∧ |(b─k)| = |(k─h)| ∧ ∠ b:k:c₀ = ∟)
  euclid_sentence "3.10.4"
    "Therefore, since in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles, the center of circle $ABC$ is thus on $AC$ [Prop.~3.1~corr.]."
    (step4 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC) := by euclid_apply (helper_3_10_step4 ABC b h k c₀ BH AC (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BH; assumption)) (by euclid_assumption "" (show h.onLine BH; assumption)) (by euclid_assumption "" (show ¬c₀.onLine BH; assumption)) (by euclid_assumption "" (show c₀.onLine AC; assumption)) (by euclid_assumption "in circle $ABC$ some straight-line $AC$ cuts some (other) straight-line $BH$ in half, and at right-angles" (show k.onLine AC ∧ between b k h ∧ |(b─k)| = |(k─h)| ∧ ∠ b:k:c₀ = ∟; assumption)))

  -- @assumption_valid
  have step5_assumption1 : l.onLine NO ∧ between b l g ∧ |(b─l)| = |(l─g)| ∧ ∠ b:l:m₀ = ∟ := by euclid_finish
  -- @assumption ("in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles", l.onLine NO ∧ between b l g ∧ |(b─l)| = |(l─g)| ∧ ∠ b:l:m₀ = ∟)
  euclid_sentence "3.10.5"
    "Again, since in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles, the center of circle $ABC$ is thus on $NO$ [Prop.~3.1~corr.]."
    (step5 : ∃ o : Point, o.isCentre ABC ∧ o.onLine NO) := by euclid_apply (helper_3_10_step5 ABC b g l m₀ BG NO (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show ¬m₀.onLine BG; assumption)) (by euclid_assumption "" (show m₀.onLine NO; assumption)) (by euclid_assumption "in the same circle $ABC$ some straight-line $NO$ cuts some (other straight-line) $BG$ in half, and at right-angles" (show l.onLine NO ∧ between b l g ∧ |(b─l)| = |(l─g)| ∧ ∠ b:l:m₀ = ∟; assumption)))

  euclid_sentence "3.10.6"
    "And it was also shown (to be) on $AC$."
    (step6 : ∃ o : Point, o.isCentre ABC ∧ o.onLine AC) := by euclid_apply (helper_3_10_step6 (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABC ∧ o.onLine AC; assumption)))

  have hp_exists : ∃ q : Point, q.onLine AC ∧ q.onLine NO := by euclid_apply (helper_3_10_hp_exists ABC AC NO (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABC ∧ o.onLine AC; assumption)) (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABC ∧ o.onLine NO; assumption)))
  obtain ⟨p, hpAC, hpNO⟩ := hp_exists
  euclid_sentence "3.10.7"
    "And the straight-lines $AC$ and $NO$ meet at no other (point) than $P$."
    (step7 : p.onLine AC ∧ p.onLine NO) := by euclid_apply (helper_3_10_step7 p AC NO (by euclid_assumption "" (show p.onLine AC; assumption)) (by euclid_assumption "" (show p.onLine NO; assumption)))

  euclid_sentence "3.10.8"
    "Thus, point $P$ is the center of circle $ABC$."
    (step8 : p.isCentre ABC) := by euclid_apply (helper_3_10_step8 ABC b g h k l c₀ m₀ p BH BG AC NO (by euclid_assumption "" (show b.onLine BH; assumption)) (by euclid_assumption "" (show h.onLine BH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show k.onLine AC; assumption)) (by euclid_assumption "" (show c₀.onLine AC; assumption)) (by euclid_assumption "" (show l.onLine NO; assumption)) (by euclid_assumption "" (show m₀.onLine NO; assumption)) (by euclid_assumption "" (show ¬c₀.onLine BH; assumption)) (by euclid_assumption "" (show ¬m₀.onLine BG; assumption)) (by euclid_assumption "" (show ∠ b:k:c₀ = ∟; assumption)) (by euclid_assumption "" (show ∠ b:l:m₀ = ∟; assumption)) (by euclid_assumption "" (show between b k h; assumption)) (by euclid_assumption "" (show |(b─k)| = |(k─h)|; assumption)) (by euclid_assumption "" (show between b l g; assumption)) (by euclid_assumption "" (show |(b─l)| = |(l─g)|; assumption)) (by euclid_assumption "" (show b ≠ h; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABC ∧ o.onLine AC; assumption)) (by euclid_assumption "" (show ∃ o : Point, o.isCentre ABC ∧ o.onLine NO; assumption)) (by euclid_assumption "" (show p.onLine AC; assumption)) (by euclid_assumption "" (show p.onLine NO; assumption)))

  euclid_sentence "3.10.9"
    "So, similarly, we can show that $P$ is also the center of circle $DEF$."
    (step9 : p.isCentre DEF) := by euclid_apply (helper_3_10_step9 DEF b g h k l c₀ m₀ p BH BG AC NO (by euclid_assumption "" (show b.onLine BH; assumption)) (by euclid_assumption "" (show h.onLine BH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show k.onLine AC; assumption)) (by euclid_assumption "" (show c₀.onLine AC; assumption)) (by euclid_assumption "" (show l.onLine NO; assumption)) (by euclid_assumption "" (show m₀.onLine NO; assumption)) (by euclid_assumption "" (show ¬c₀.onLine BH; assumption)) (by euclid_assumption "" (show ¬m₀.onLine BG; assumption)) (by euclid_assumption "" (show ∠ b:k:c₀ = ∟; assumption)) (by euclid_assumption "" (show ∠ b:l:m₀ = ∟; assumption)) (by euclid_assumption "" (show between b k h; assumption)) (by euclid_assumption "" (show |(b─k)| = |(k─h)|; assumption)) (by euclid_assumption "" (show between b l g; assumption)) (by euclid_assumption "" (show |(b─l)| = |(l─g)|; assumption)) (by euclid_assumption "" (show b ≠ h; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show g.onCircle DEF; assumption)) (by euclid_assumption "" (show h.onCircle DEF; assumption)) (by euclid_assumption "" (show p.onLine AC; assumption)) (by euclid_assumption "" (show p.onLine NO; assumption)))

  euclid_sentence "3.10.10"
    "Thus, two circles cutting one another, $ABC$ and $DEF$, have the same center $P$."
    (step10 : p.isCentre ABC ∧ p.isCentre DEF) := by euclid_apply (helper_3_10_step10 ABC DEF p (by euclid_assumption "" (show p.isCentre ABC; assumption)) (by euclid_assumption "" (show p.isCentre DEF; assumption)))

  euclid_sentence "3.10.11"
    "The very thing is impossible [Prop.~3.5]."
    (step11 : False) := by euclid_apply (helper_3_10_step11 ABC DEF p b (by euclid_assumption "" (show ABC ≠ DEF; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show p.isCentre ABC ∧ p.isCentre DEF; assumption)))

  euclid_sentence "3.10.12"
    "Thus, a circle does not cut a(nother) circle at more than two points."
    (step12 : ¬ ∃ (b₀ g₀ h₀ : Point), b₀ ≠ g₀ ∧ b₀ ≠ h₀ ∧ g₀ ≠ h₀ ∧
        b₀.onCircle ABC ∧ g₀.onCircle ABC ∧ h₀.onCircle ABC ∧
        b₀.onCircle DEF ∧ g₀.onCircle DEF ∧ h₀.onCircle DEF) := by euclid_apply (helper_3_10_step12 ABC DEF p b (by euclid_assumption "" (show ABC ≠ DEF; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle DEF; assumption)) (by euclid_assumption "" (show p.isCentre ABC ∧ p.isCentre DEF; assumption)))

  exact step11
  euclid_conclude_sentence "3.10.13"
    "(Which is) the very thing it was required to show."

end Elements.Book3
