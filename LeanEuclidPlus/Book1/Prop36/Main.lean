import SystemE
import Book1.Prop36.step1
import Book1.Prop36.step2
import Book1.Prop36.step3
import Book1.Prop36.step4
import Book1.Prop36.step5
import Book1.Prop36.step6
import Book1.Prop36.step7
import Book1.Prop36.step8
import Book1.Prop36.step9
import Book1.Prop36.step2_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_36 : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  euclid_intros
  euclid_intro_sentence "1.36.0"
    "Parallelograms which are on equal bases and between the same parallels are equal to one another. Let $ABCD$ and $EFGH$ be parallelograms which are on the equal bases $BC$ and $FG$, and (are) between the same parallels $AH$ and $BG$. I say that the parallelogram $ABCD$ is equal to $EFGH$. "

  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  euclid_sentence "1.36.1"
    "For let $BE$ and $CH$ have been joined."
    (step1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH) := by euclid_apply (helper_1_36_step1 b c e f g h AH BG HG BE CH (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine HG; assumption)) (by euclid_assumption "" (show g.onLine HG; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show e.sameSide f HG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)))

  -- @assumption_valid
  have step2_assumption1 : |(b─c)| = |(f─g)| := by assumption
  -- @assumption_gap
  have step2_assumption2 : |(f─g)| = |(e─h)| := by euclid_apply (helper_1_36_step2_assumption2 e f g h AH BG EF HG (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine HG; assumption)) (by euclid_assumption "" (show g.onLine HG; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show e.sameSide f HG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine HG; assumption)))
  -- @assumption ("$BC$ is equal to $FG$", |(b─c)| = |(f─g)|)
  -- @assumption ("$FG$ is equal to $EH$ [Prop.~1.34]", |(f─g)| = |(e─h)|)
  euclid_sentence "1.36.2"
    "And since $BC$ is equal to $FG$, but $FG$ is equal to $EH$ [Prop.~1.34], $BC$ is thus equal to $EH$."
    (step2 : |(b─c)| = |(e─h)|) := by euclid_apply (helper_1_36_step2 e f g h AH BG EF HG (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine HG; assumption)) (by euclid_assumption "" (show g.onLine HG; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show e.sameSide f HG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine HG; assumption)) (by euclid_assumption "$BC$ is equal to $FG$" (show |(b─c)| = |(f─g)|; assumption)) (by euclid_assumption "$FG$ is equal to $EH$ [Prop.~1.34]" (show |(f─g)| = |(e─h)|; assumption)))

  euclid_sentence "1.36.3"
    "And they are also parallel,"
    (step3 : ¬(BG.intersectsLine AH)) := by euclid_apply (helper_1_36_step3 AH BG (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)))

  euclid_sentence "1.36.4"
    "and $EB$ and $HC$ join them."
    (step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH) := by euclid_apply (helper_1_36_step4 b c e h BE CH (by euclid_assumption "" (show distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH; assumption)))

  euclid_sentence "1.36.5"
    "But (straight-lines) joining equal and parallel (straight-lines) on the same sides are (themselves) equal and parallel [Prop.~1.33] [thus, $EB$ and $HC$ are also equal and parallel]."
    (step5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH)) := by euclid_apply (helper_1_36_step5 a b c d e h AH BG AB CD BE CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show |(b─c)| = |(e─h)|; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by euclid_assumption "" (show between a e h; assumption)) (by euclid_assumption "" (show between a d h; assumption)))

  euclid_sentence "1.36.6"
    "Thus, $EBCH$ is a parallelogram [Prop.~1.34],"
    (step6 : formParallelogram e h b c AH BG BE CH) := by euclid_apply (helper_1_36_step6 a b c d e h AH BG AB CD BE CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by euclid_assumption "" (show |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH; assumption)) (by euclid_assumption "" (show between a e h; assumption)) (by euclid_assumption "" (show between a d h; assumption)))

  -- @assumption_valid
  have step7_assumption1 : distinctPointsOnLine b c BG := by euclid_finish
  -- @assumption_valid
  have step7_assumption2 : ¬(BG.intersectsLine AH) := by assumption
  -- @assumption ("$BC$, as ($ABCD$)", distinctPointsOnLine b c BG)
  -- @assumption ("$BC$ and $AH$, as ($ABCD$) [Prop.~1.35]", ¬(BG.intersectsLine AH))
  euclid_sentence "1.36.7"
    "and is equal to $ABCD$. For it has  the same base, $BC$, as ($ABCD$), and is between the same parallels, $BC$ and $AH$, as ($ABCD$) [Prop.~1.35]."
    (step7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by euclid_apply (helper_1_36_step7 a b c d e h AH BG AB CD BE CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show formParallelogram e h b c AH BG BE CH; assumption)) (by euclid_assumption "$BC$, as ($ABCD$)" (show distinctPointsOnLine b c BG; assumption)) (by euclid_assumption "$BC$ and $AH$, as ($ABCD$) [Prop.~1.35]" (show ¬(BG.intersectsLine AH); assumption)))

  euclid_sentence "1.36.8"
    "So, for the same (reasons), $EFGH$ is also equal to the same (parallelogram) $EBCH$ [Prop.~1.34]. "
    (step8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h) := by euclid_apply (helper_1_36_step8 b c e f g h AH BG EF HG BE CH (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show f.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine HG; assumption)) (by euclid_assumption "" (show g.onLine HG; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show e.sameSide f HG; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine HG; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by euclid_assumption "" (show |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH; assumption)) (by euclid_assumption "" (show formParallelogram e h b c AH BG BE CH; assumption)))

  euclid_sentence "1.36.9"
    "So that the parallelogram $ABCD$ is  also equal to $EFGH$. "
    (step9 : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g) := by euclid_apply (helper_1_36_step9 a b c d e f g h (by euclid_assumption "" (show Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c; assumption)) (by euclid_assumption "" (show Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h; assumption)))

  exact step9
  euclid_conclude_sentence "1.36.10"
    "Thus, parallelograms which are on equal bases and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
