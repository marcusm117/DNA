import SystemE
import Book1.Prop31.Main
import Book1.Prop37.step1
import Book1.Prop37.step2
import Book1.Prop37.step3
import Book1.Prop37.step4
import Book1.Prop37.step5
import Book1.Prop37.step6
import Book1.Prop37.step7
import Book1.Prop37.step8
import Book1.Prop37.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  euclid_intros
  euclid_intro_sentence "1.37.0"
    "Triangles which are on the same base and between the same parallels are equal to one another.    Let $ABC$ and $DBC$ be triangles on the same base $BC$, and between the same parallels $AD$ and $BC$. I say that triangle $ABC$ is equal to triangle $DBC$. "

  euclid_apply (proposition_31 b a c AC) as BE
  euclid_apply (intersection_lines AD BE) as e
  euclid_apply (proposition_31 c b d BD) as CF
  euclid_apply (intersection_lines AD CF) as f
  euclid_sentence "1.37.1"
    "Let $AD$ have been produced in both directions to $E$ and $F$,"
    (step1 : between d a e ∧ between a d f) := by euclid_apply (helper_1_37_step1 a b c d e f AB BC AC BD CD AD BE CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show BD ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CD; assumption)) (by euclid_assumption "" (show CD ≠ BD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show d.sameSide c AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine AC; assumption)) (by euclid_assumption "" (show e.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show ¬CF.intersectsLine BD; assumption)) (by euclid_assumption "" (show f.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)))

  euclid_sentence "1.37.2"
    "and let the (straight-line) $BE$ have been drawn through $B$ parallel to $CA$ [Prop.~1.31],"
    (step2 : b.onLine BE ∧ e.onLine BE ∧ ¬(BE.intersectsLine AC)) := by euclid_apply (helper_1_37_step2 b e AC BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine AC; assumption)))

  euclid_sentence "1.37.3"
    "and let the (straight-line) $CF$ have been drawn through $C$ parallel to $BD$ [Prop.~1.31]."
    (step3 : c.onLine CF ∧ f.onLine CF ∧ ¬(CF.intersectsLine BD)) := by euclid_apply (helper_1_37_step3 c f BD CF (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show ¬CF.intersectsLine BD; assumption)))

  euclid_sentence "1.37.4"
    "Thus, $EBCA$ and $DBCF$ are both parallelograms,"
    (step4 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF) := by euclid_apply (helper_1_37_step4 a b c d e f AB BC AC BD CD AD BE CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show BD ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CD; assumption)) (by euclid_assumption "" (show CD ≠ BD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show d.sameSide c AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine AC; assumption)) (by euclid_assumption "" (show e.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show ¬CF.intersectsLine BD; assumption)) (by euclid_assumption "" (show f.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show between d a e ∧ between a d f; assumption)) (by euclid_assumption "" (show b.onLine BE ∧ e.onLine BE ∧ ¬BE.intersectsLine AC; assumption)) (by euclid_assumption "" (show c.onLine CF ∧ f.onLine CF ∧ ¬CF.intersectsLine BD; assumption)))

  -- @assumption_valid
  have step5_assumption1 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF := by assumption
  -- @assumption ("they are on the same base $BC$, and between the same parallels $BC$ and $EF$", formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF)
  euclid_sentence "1.37.5"
    "and are equal. For they are on the same base $BC$, and between the same parallels $BC$ and $EF$ [Prop.~1.35]."
    (step5 : Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f) := by euclid_apply (helper_1_37_step5 a b c d e f AB BC AC BD CD AD BE CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine AC; assumption)) (by euclid_assumption "" (show e.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show ¬CF.intersectsLine BD; assumption)) (by euclid_assumption "" (show f.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "they are on the same base $BC$, and between the same parallels $BC$ and $EF$" (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  euclid_sentence "1.37.6"
    "And the triangle $ABC$ is half of  the parallelogram $EBCA$. For the diagonal $AB$ cuts the latter in half [Prop.~1.34]."
    (step6 : Triangle.area △ a:b:c = Triangle.area △ e:a:b) := by euclid_apply (helper_1_37_step6 a b c d e f AB BC AC BD CD AD BE CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  euclid_sentence "1.37.7"
    "And the  triangle $DBC$ (is) half of the parallelogram $DBCF$. For the diagonal $DC$ cuts the latter in half [Prop.~1.34]."
    (step7 : Triangle.area △ d:b:c = Triangle.area △ f:d:c) := by euclid_apply (helper_1_37_step7 a b c d e f AB BC AC BD CD AD BE CF (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show BD ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ CD; assumption)) (by euclid_assumption "" (show CD ≠ BD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show d.sameSide c AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show ¬CF.intersectsLine BD; assumption)) (by euclid_assumption "" (show f.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  euclid_sentence "1.37.8"
    "[And the halves of equal things are equal to one another.]"
    (step8 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) := by euclid_apply (helper_1_37_step8 a b c d e f (by euclid_assumption "" (show Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ e:a:b; assumption)) (by euclid_assumption "" (show Triangle.area △ d:b:c = Triangle.area △ f:d:c; assumption)))

  euclid_sentence "1.37.9"
    "Thus, triangle $ABC$ is equal to triangle $DBC$. "
    (step9 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) := by euclid_apply (helper_1_37_step9 a b c d (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ d:b:c; assumption)))

  exact step9
  euclid_conclude_sentence "1.37.10"
    "Thus, triangles which are on the same base and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
