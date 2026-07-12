import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop11
import Book1.Prop31.Main
import Book2.Prop01.step1
import Book2.Prop01.step2
import Book2.Prop01.step3
import Book2.Prop01.step4
import Book2.Prop01.step5
import Book2.Prop01.step6
import Book2.Prop01.step7
import Book2.Prop01.step8
import Book2.Prop01.step9
import Book2.Prop01.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point) (A BC : Line),
  distinctPointsOnLine a₁ a₂ A ∧ distinctPointsOnLine b c BC ∧
  d.onLine BC ∧ e.onLine BC ∧ between b d e ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| =
    |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| :=
by
  euclid_intros
  euclid_intro_sentence "2.1.0"
    "If there are two straight-lines, and one of them is cut into any number of pieces whatsoever, (then) the rectangle contained by the two straight-lines is equal to the (sum of the) rectangles contained by the uncut (straight-line), and every one of the pieces (of the cut straight-line). Let $A$ and $BC$ be the two straight-lines, and let $BC$ be cut, at random, at points $D$ and $E$. I say that the rectangle contained by $A$ and $BC$ is equal to the rectangle(s) contained by $A$ and $BD$, by $A$ and $DE$, and, finally, by $A$ and $EC$."

  euclid_apply (proposition_11'' b c BC) as f
  euclid_apply (line_from_points b f) as BF
  euclid_apply (extend_point_longer BF b f (a₁─a₂)) as f'
  euclid_sentence "2.1.1"
    "For let $BF$ be drawn from point $B$, at right-angles to $BC$ [Prop.~1.11],"
    (step1 : ∠ f:b:c = ∟) := by euclid_apply (helper_2_1_step1 b c f (by euclid_assumption "" (show ∠ f:b:c = ∟; assumption)))

  euclid_apply (proposition_3 b f' a₁ a₂ BF A) as g
  euclid_sentence "2.1.2"
    "and let $BG$ be made equal to $A$ [Prop.~1.3],"
    (step2 : |(b─g)| = |(a₁─a₂)|) := by euclid_apply (helper_2_1_step2 a₁ a₂ b g (by euclid_assumption "" (show |(b─g)| = |(a₁─a₂)|; assumption)))

  euclid_apply (proposition_31 g b c BC) as GH
  euclid_sentence "2.1.3"
    "and let $GH$ be drawn through (point) $G$, parallel to $BC$ [Prop.~1.31],"
    (step3 : g.onLine GH ∧ ¬(GH.intersectsLine BC)) := by euclid_apply (helper_2_1_step3 g GH BC (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)))

  euclid_apply (proposition_31 d b f BF) as DK
  euclid_apply (proposition_31 e b f BF) as EL
  euclid_apply (proposition_31 c b f BF) as CH
  euclid_apply (intersection_lines DK GH) as k
  euclid_apply (intersection_lines EL GH) as l
  euclid_apply (intersection_lines CH GH) as h
  euclid_sentence "2.1.4"
    "and let $DK$, $EL$, and $CH$ be drawn through (points) $D$, $E$, and $C$ (respectively), parallel to $BG$ [Prop.~1.31]."
    (step4 : d.onLine DK ∧ ¬(DK.intersectsLine BF) ∧
      e.onLine EL ∧ ¬(EL.intersectsLine BF) ∧
      c.onLine CH ∧ ¬(CH.intersectsLine BF)) := by euclid_apply (helper_2_1_step4 d e c DK EL CH BF (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)))

  euclid_sentence "2.1.5"
    "So the (rectangle) $BH$ is equal to the (rectangles) $BK$, $DL$, and $EH$."
    (step5 : Triangle.area △ b:c:h + Triangle.area △ b:g:h =
      (Triangle.area △ b:d:k + Triangle.area △ b:g:k)
    + (Triangle.area △ d:e:l + Triangle.area △ d:k:l)
    + (Triangle.area △ e:c:h + Triangle.area △ e:l:h)) := by euclid_apply (helper_2_1_step5 b c d e f f' g h k l BC GH BF DK EL CH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b g f'; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)) (by euclid_assumption "" (show k.onLine DK; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)))
  -- ideally "it is contained by $GB$ and $BC$" is said here. but this violates euclid's order.
  -- @assumption_valid
  have step6_assumption1 : |(b─g)| = |(a₁─a₂)| := by assumption
  -- @assumption ("$BG$ (is) equal to $A$", |(b─g)| = |(a₁─a₂)|)
  euclid_sentence "2.1.6"
    "And $BH$ is the (rectangle contained) by $A$ and $BC$. For it is contained by $GB$ and $BC$, and $BG$ (is) equal to $A$."
    (step6 : Triangle.area △ b:c:h + Triangle.area △ b:g:h = |(a₁─a₂)| * |(b─c)|) := by euclid_apply (helper_2_1_step6 a₁ a₂ b c f f' g h BC BF CH GH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b f f'; assumption)) (by euclid_assumption "" (show between b g f'; assumption)) (by euclid_assumption "" (show ∠ f:b:c = ∟; assumption)) (by euclid_assumption "$BG$ (is) equal to $A$" (show |(b─g)| = |(a₁─a₂)|; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)))

  -- @assumption_valid
  have step7_assumption1 : |(b─g)| = |(a₁─a₂)| := by assumption
  -- @assumption ("$BG$ (is) equal to $A$", |(b─g)| = |(a₁─a₂)|)
  euclid_sentence "2.1.7"
    "And $BK$ (is) the (rectangle contained) by $A$ and $BD$. For it is contained by $GB$ and $BD$, and $BG$ (is) equal to $A$."
    (step7 : Triangle.area △ b:d:k + Triangle.area △ b:g:k = |(a₁─a₂)| * |(b─d)|) := by euclid_apply (helper_2_1_step7 a₁ a₂ b c d e f f' g k BC BF DK GH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b f f'; assumption)) (by euclid_assumption "" (show between b g f'; assumption)) (by euclid_assumption "" (show ∠ f:b:c = ∟; assumption)) (by euclid_assumption "$BG$ (is) equal to $A$" (show |(b─g)| = |(a₁─a₂)|; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show k.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)))

  -- @assumption_valid
  have step8_assumption1 : |(b─g)| = |(a₁─a₂)| := by assumption
  -- @assumption ("$BG$ [Prop.~1.34], (is) equal to $A$", |(b─g)| = |(a₁─a₂)|)
  euclid_sentence "2.1.8"
    "And $DL$ (is) the (rectangle contained) by $A$ and $DE$. For $DK$, that is to say $BG$ [Prop.~1.34], (is) equal to $A$."
    (step8 : Triangle.area △ d:e:l + Triangle.area △ d:k:l = |(a₁─a₂)| * |(d─e)|) := by euclid_apply (helper_2_1_step8 a₁ a₂ b c d e f f' g k l BC BF DK EL GH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b f f'; assumption)) (by euclid_assumption "" (show between b g f'; assumption)) (by euclid_assumption "" (show ∠ f:b:c = ∟; assumption)) (by euclid_assumption "$BG$ [Prop.~1.34], (is) equal to $A$" (show |(b─g)| = |(a₁─a₂)|; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show k.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)))

  euclid_sentence "2.1.9"
    "Similarly, $EH$ (is) also the (rectangle contained) by $A$ and $EC$."
    (step9 : Triangle.area △ e:c:h + Triangle.area △ e:l:h = |(a₁─a₂)| * |(e─c)|) := by euclid_apply (helper_2_1_step9 a₁ a₂ b c d e f f' g h l BC BF EL CH GH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b f f'; assumption)) (by euclid_assumption "" (show between b g f'; assumption)) (by euclid_assumption "" (show ∠ f:b:c = ∟; assumption)) (by euclid_assumption "" (show |(b─g)| = |(a₁─a₂)|; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)))

  euclid_sentence "2.1.10"
    "Thus, the (rectangle contained) by $A$ and $BC$ is equal to the (rectangles contained) by $A$ and $BD$, by $A$ and $DE$, and, finally, by $A$ and $EC$."
    (step10 : |(a₁─a₂)| * |(b─c)| =
      |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)|) := by euclid_apply (helper_2_1_step10 a₁ a₂ b c d e g h k l (by euclid_assumption "" (show Triangle.area △ b:c:h + Triangle.area △ b:g:h = (Triangle.area △ b:d:k + Triangle.area △ b:g:k) + (Triangle.area △ d:e:l + Triangle.area △ d:k:l) + (Triangle.area △ e:c:h + Triangle.area △ e:l:h); assumption)) (by euclid_assumption "" (show Triangle.area △ b:c:h + Triangle.area △ b:g:h = |(a₁─a₂)| * |(b─c)|; assumption)) (by euclid_assumption "" (show Triangle.area △ b:d:k + Triangle.area △ b:g:k = |(a₁─a₂)| * |(b─d)|; assumption)) (by euclid_assumption "" (show Triangle.area △ d:e:l + Triangle.area △ d:k:l = |(a₁─a₂)| * |(d─e)|; assumption)) (by euclid_assumption "" (show Triangle.area △ e:c:h + Triangle.area △ e:l:h = |(a₁─a₂)| * |(e─c)|; assumption)))

  exact step10
  euclid_conclude_sentence "2.1.11"
    "Thus, if there are two straight-lines, and one of them is cut into any number of pieces whatsoever, (then) the rectangle contained by the two straight-lines is equal to the (sum of the) rectangles contained by the uncut (straight-line), and every one of the pieces (of the cut straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
