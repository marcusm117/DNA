import SystemE
import Book1.Prop31.Main
import Book1.Prop38.step1
import Book1.Prop38.step2
import Book1.Prop38.step3
import Book1.Prop38.step4
import Book1.Prop38.step5
import Book1.Prop38.step6
import Book1.Prop38.step7
import Book1.Prop38.step8
import Book1.Prop38.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_38 : ∀ (a b c d e f: Point) (AD BF AB AC DE DF : Line),
  a.onLine AD ∧ d.onLine AD ∧ formTriangle a b c AB BF AC ∧ formTriangle d e f DE BF DF ∧
  ¬(AD.intersectsLine BF) ∧ (between b c f) ∧ (between b e f) ∧ |(b─c)| = |(e─f)| →
  Triangle.area △ a:b:c = Triangle.area △ d:e:f := by
  euclid_intros
  euclid_intro_sentence "1.38.0"
    "Triangles which are on equal bases and between the same parallels are equal to one another. Let $ABC$ and $DEF$ be triangles on the equal bases $BC$ and $EF$, and between the same parallels $BF$ and $AD$. I say that triangle $ABC$ is equal to triangle $DEF$. "

  euclid_apply (proposition_31 b a c AC) as BG
  euclid_apply (intersection_lines AD BG) as g
  euclid_apply (proposition_31 f d e DE) as FH
  euclid_apply (intersection_lines AD FH) as h
  euclid_sentence "1.38.1"
    "For let $AD$ have been produced in both directions to $G$ and $H$,"
    (step1 : g.onLine AD ∧ h.onLine AD) := by euclid_apply (helper_1_38_step1 g h AD (by euclid_assumption "" (show g.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)))

  euclid_sentence "1.38.2"
    "and let the (straight-line) $BG$ have been drawn through $B$ parallel to $CA$ [Prop.~1.31],"
    (step2 : distinctPointsOnLine b g BG ∧ ¬(BG.intersectsLine AC)) := by euclid_apply (helper_1_38_step2 a b g AD BF BG AC AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show AB ≠ BF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BF; assumption)) (by euclid_assumption "" (show ¬BG.intersectsLine AC; assumption)))

  euclid_sentence "1.38.3"
    "and let the (straight-line) $FH$ have been drawn through $F$ parallel to $DE$ [Prop.~1.31]."
    (step3 : distinctPointsOnLine f h FH ∧ ¬(FH.intersectsLine DE)) := by euclid_apply (helper_1_38_step3 d e f h AD BF FH DE (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine BF; assumption)) (by euclid_assumption "" (show DE ≠ BF; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BF; assumption)) (by euclid_assumption "" (show ¬FH.intersectsLine DE; assumption)))

  euclid_sentence "1.38.4"
    "Thus,  $GBCA$ and $DEFH$ are each parallelograms."
    (step4 : formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF) := by euclid_apply (helper_1_38_step4 a b c d e f g h AD BF AB AC DE BG FH (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BF; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show DE ≠ BF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine AD; assumption)) (by euclid_assumption "" (show ¬BG.intersectsLine AC; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show ¬FH.intersectsLine DE; assumption)) (by euclid_assumption "" (show between b c f; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BF; assumption)))

  -- @assumption_valid
  have step5_assumption1 : |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF) := by euclid_finish
  -- @assumption ("they are on the equal bases $BC$ and $EF$, and between  the same parallels $BF$ and $GH$", |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF))
  euclid_sentence "1.38.5"
    "And $GBCA$ is equal to $DEFH$. For they are on the equal bases $BC$ and $EF$, and between  the same parallels $BF$ and $GH$ [Prop.~1.36]."
    (step5 : Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) := by euclid_apply (helper_1_38_step5 a b c d e f g h AD BF AB AC DE BG FH (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BF; assumption)) (by euclid_assumption "" (show BF ≠ AC; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show DE ≠ BF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine BG; assumption)) (by euclid_assumption "" (show g.onLine AD; assumption)) (by euclid_assumption "" (show ¬BG.intersectsLine AC; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show ¬FH.intersectsLine DE; assumption)) (by euclid_assumption "" (show between b c f; assumption)) (by euclid_assumption "" (show between b e f; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BF; assumption)) (by euclid_assumption "" (show formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF; assumption)) (by euclid_assumption "they are on the equal bases $BC$ and $EF$, and between  the same parallels $BF$ and $GH$" (show |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF); assumption)))

  -- @assumption_valid
  have step6_assumption1 : formParallelogram g b a c BG AC AD BF := by euclid_finish
  -- @assumption ("the diagonal $AB$ cuts the latter in half", formParallelogram g b a c BG AC AD BF)
  euclid_sentence "1.38.6"
    "And triangle $ABC$ is half of the parallelogram $GBCA$. For the diagonal $AB$ cuts the latter in half [Prop.~1.34]."
    (step6 : Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a) := by euclid_apply (helper_1_38_step6 a b c g AD BF AB AC BG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "the diagonal $AB$ cuts the latter in half" (show formParallelogram g b a c BG AC AD BF; assumption)))

  -- @assumption_valid
  have step7_assumption1 : formParallelogram d e h f DE FH AD BF := by euclid_finish
  -- @assumption ("the diagonal $DF$ cuts the latter in half", formParallelogram d e h f DE FH AD BF)
  euclid_sentence "1.38.7"
    "And triangle $FED$ (is) half of parallelogram $DEFH$. For the diagonal $DF$ cuts the latter in half."
    (step7 : Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h) := by euclid_apply (helper_1_38_step7 d e f h AD BF DE FH DF (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine FH; assumption)) (by euclid_assumption "" (show f.onLine FH; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show ¬FH.intersectsLine DE; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BF; assumption)) (by euclid_assumption "" (show DE ≠ BF; assumption)) (by euclid_assumption "the diagonal $DF$ cuts the latter in half" (show formParallelogram d e h f DE FH AD BF; assumption)))

  euclid_sentence "1.38.8"
    "[And the halves of equal things are equal to one another.]"
    (step8 : (Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧ Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧ Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) → Triangle.area △ a:b:c = Triangle.area △ f:e:d) := by euclid_apply (helper_1_38_step8 a b c d e f g h)

  euclid_sentence "1.38.9"
    "Thus, triangle $ABC$ is equal to triangle $DEF$. "
    (step9 : Triangle.area △ a:b:c = Triangle.area △ d:e:f) := by euclid_apply (helper_1_38_step9 a b c d e f g h (by euclid_assumption "" (show Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a; assumption)) (by euclid_assumption "" (show Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h; assumption)) (by euclid_assumption "" (show (Triangle.area △ a:b:c + Triangle.area △ a:b:c = Triangle.area △ g:b:c + Triangle.area △ g:c:a ∧ Triangle.area △ f:e:d + Triangle.area △ f:e:d = Triangle.area △ d:e:f + Triangle.area △ d:f:h ∧ Triangle.area △ g:b:c + Triangle.area △ g:c:a = Triangle.area △ d:e:f + Triangle.area △ d:f:h) → Triangle.area △ a:b:c = Triangle.area △ f:e:d; assumption)))

  exact step9
  euclid_conclude_sentence "1.38.10"
    "Thus, triangles which are on equal bases and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
