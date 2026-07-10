import SystemE
import Book1.Prop31.Main
import Book1Variants.Prop46
import Book2.Prop06.step1
import Book2.Prop06.step2
import Book2.Prop06.step3
import Book2.Prop06.step4
import Book2.Prop06.step5
import Book2.Prop06.step6
import Book2.Prop06.step7
import Book2.Prop06.step8
import Book2.Prop06.step9
import Book2.Prop06.step10
import Book2.Prop06.step11
import Book2.Prop06.step12
import Book2.Prop06.step13
import Book2.Prop06.step14
import Book2.Prop06.step15
import Book2.Prop06.step16
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem proposition_6 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between a b d →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  euclid_intro_sentence "2.6.0"
    "If a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having being added, and the (straight-line) having being added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added. For let any straight-line $AB$ be cut in half at point $C$, and let any straight-line $BD$ be added to it straight-on. I say that the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the square on $CD$."

  euclid_apply (Elements.Book1.proposition_46 c d AB) as (e, f, EF, CE, DF)
  euclid_sentence "2.6.1"
    "For let the square $CEFD$ be described on $CD$ [Prop.~1.46],"
    (step1 : |(c─e)| = |(c─d)| ∧ |(d─f)| = |(c─d)| ∧ |(e─f)| = |(c─d)| ∧
      (∠ d:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:d:f = ∟) ∧ (∠ d:f:e = ∟)) := by euclid_apply (helper_2_6_step1 c d e f (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(e─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)))

  euclid_apply (line_from_points d e) as DE
  euclid_sentence "2.6.2"
    "and let $DE$ be joined,"
    (step2 : distinctPointsOnLine d e DE) := by euclid_apply (helper_2_6_step2 a b c d e AB DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))

  euclid_apply (Elements.Book1.proposition_31 b c e CE) as BG
  euclid_apply (intersection_lines BG EF) as g
  euclid_apply (intersection_lines BG DE) as h
  euclid_sentence "2.6.3"
    "and let $BG$ be drawn through point $B$, parallel to either of $EC$ or $DF$ [Prop.~1.31],"
    (step3 : b.onLine BG ∧ ¬(BG.intersectsLine CE)) := by euclid_apply (helper_2_6_step3 b BG CE (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))

  euclid_apply (Elements.Book1.proposition_31 h a b AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM DF) as m
  euclid_sentence "2.6.4"
    "and let $KM$ be drawn through point $H$, parallel to either of $AB$ or $EF$ [Prop.~1.31],"
    (step4 : h.onLine KM ∧ ¬(KM.intersectsLine AB)) := by euclid_apply (helper_2_6_step4 h KM AB (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))

  euclid_apply (Elements.Book1.proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines KM AK) as k
  euclid_sentence "2.6.5"
    "and finally let $AK$ be drawn through $A$, parallel to either of $CL$ or $DM$ [Prop.~1.31]."
    (step5 : a.onLine AK ∧ ¬(AK.intersectsLine CE)) := by euclid_apply (helper_2_6_step5 a AK CE (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))

  -- @assumption ("$AC$ is equal to $CB$", |(a─c)| = |(c─b)|)
  euclid_sentence "2.6.6"
    "Therefore, since $AC$ is equal to $CB$, (rectangle) $AL$ is also equal to (rectangle) $CH$ [Prop.~1.36]."
    (step6 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ c:b:h + Triangle.area △ c:h:l) := by euclid_apply (helper_2_6_step6 a b c d e k l h AB KM AK CE BG DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "$AC$ is equal to $CB$" (show |(a─c)| = |(c─b)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))

  euclid_sentence "2.6.7"
    "But, (rectangle) $CH$ is equal to (rectangle) $HF$ [Prop.~1.43]."
    (step7 : Triangle.area △ c:b:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by euclid_apply (helper_2_6_step7 a b c d e f g h l m AB DE CE DF EF BG KM (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)) (by euclid_assumption "" (show e.sameSide c DF; assumption)))

  euclid_sentence "2.6.8"
    "Thus, (rectangle) $AL$ is also equal to (rectangle) $HF$."
    (step8 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by euclid_apply (helper_2_6_step8 a c l k b h m f g (by euclid_assumption "" (show Triangle.area △ a:c:l + Triangle.area △ a:l:k = Triangle.area △ c:b:h + Triangle.area △ c:h:l; assumption)) (by euclid_assumption "" (show Triangle.area △ c:b:h + Triangle.area △ c:h:l = Triangle.area △ h:m:f + Triangle.area △ h:f:g; assumption)))

  euclid_sentence "2.6.9"
    "Let (rectangle) $CM$ be added to both."
    (step9 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l)) := by euclid_apply (helper_2_6_step9 a b c d e f k l m h AB KM AK DF CE BG DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))

  euclid_sentence "2.6.10"
    "Thus, the whole (rectangle) $AM$ is equal to the gnomon $NOP$."
    (step10 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) := by euclid_apply (helper_2_6_step10 a c d h m f g l k (by euclid_assumption "" (show Triangle.area △ a:c:l + Triangle.area △ a:l:k = Triangle.area △ h:m:f + Triangle.area △ h:f:g; assumption)) (by euclid_assumption "" (show Triangle.area △ a:d:m + Triangle.area △ a:m:k = (Triangle.area △ a:c:l + Triangle.area △ a:l:k) + (Triangle.area △ c:d:m + Triangle.area △ c:m:l); assumption)))

  euclid_sentence "2.6.11"
    "But, $AM$ is the (rectangle contained) by $AD$ and $DB$. For $DM$ is equal to $DB$."
    (step11 : Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─b)|) := by euclid_apply (helper_2_6_step11 a b c d e f g h l m k AB CE DF EF BG KM DE AK (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)) (by euclid_assumption "" (show e.sameSide c DF; assumption)))

  euclid_sentence "2.6.12"
    "Thus, gnomon $NOP$ is also equal to the [rectangle contained] by $AD$ and $DB$."
    (step12 : (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) = |(a─d)| * |(d─b)|) := by euclid_apply (helper_2_6_step12 a b d m k c l h f g (by euclid_assumption "" (show Triangle.area △ a:d:m + Triangle.area △ a:m:k = (Triangle.area △ c:d:m + Triangle.area △ c:m:l) + (Triangle.area △ h:m:f + Triangle.area △ h:f:g); assumption)) (by euclid_assumption "" (show Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─b)|; assumption)))

  euclid_sentence "2.6.13"
    "Let $LG$, which is equal to the square on $BC$, be added to both."
    (step13 : Triangle.area △ l:h:g + Triangle.area △ l:g:e = |(c─b)| * |(c─b)|) := by euclid_apply (helper_2_6_step13 a b c d e f g h l AB CE DF EF BG KM DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)) (by euclid_assumption "" (show e.sameSide c DF; assumption)))

  euclid_sentence "2.6.14"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the gnomon $NOP$ and the (square) $LG$."
    (step14 : |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| =
      ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e)) := by euclid_apply (helper_2_6_step14 a b c d m l h f g e (by euclid_assumption "" (show (Triangle.area △ c:d:m + Triangle.area △ c:m:l) + (Triangle.area △ h:m:f + Triangle.area △ h:f:g) = |(a─d)| * |(d─b)|; assumption)) (by euclid_assumption "" (show Triangle.area △ l:h:g + Triangle.area △ l:g:e = |(c─b)| * |(c─b)|; assumption)))

  euclid_sentence "2.6.15"
    "But the gnomon $NOP$ and the (square) $LG$ is (equivalent to) the whole square $CEFD$, which is on $CD$."
    (step15 : (((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
        Triangle.area △ c:e:f + Triangle.area △ c:f:d) ∧
      (Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_6_step15 a b c d e f g h l m AB CE DF EF BG KM DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)) (by euclid_assumption "" (show e.sameSide c DF; assumption)))

  euclid_sentence "2.6.16"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the square on $CD$."
    (step16 : |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)|) := by euclid_apply (helper_2_6_step16 a b c d m l h f g e (by euclid_assumption "" (show |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) + (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) + (Triangle.area △ l:h:g + Triangle.area △ l:g:e); assumption)) (by euclid_assumption "" (show (((Triangle.area △ c:d:m + Triangle.area △ c:m:l) + (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) + (Triangle.area △ l:h:g + Triangle.area △ l:g:e) = Triangle.area △ c:e:f + Triangle.area △ c:f:d) ∧ (Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)|); assumption)))

  exact step16
  euclid_conclude_sentence "2.6.17"
    "Thus, if a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having being added, and the (straight-line) having being added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added. (Which is) the very thing it was required to show."

end Elements.Book2
