import SystemE
import Book1.Prop04.Main
import Book1.Prop14.Main
import Book1.Prop31.Main
import Book1.Prop41.Main
import Book1.Prop46.variants
import Book1.Prop47.step1
import Book1.Prop47.step2
import Book1.Prop47.step3
import Book1.Prop47.step4
import Book1.Prop47.step5
import Book1.Prop47.step6
import Book1.Prop47.step7
import Book1.Prop47.step8
import Book1.Prop47.step9
import Book1.Prop47.step10
import Book1.Prop47.step11
import Book1.Prop47.step12
import Book1.Prop47.step13
import Book1.Prop47.step14
import Book1.Prop47.step15
import Book1.Prop47.step16
import Book1.Prop47.step17
import Book1.Prop47.step18
import Book1.Prop47.step19
import Book1.Prop47.step20
import Book1.Prop47.step21
import Book1.Prop47.hoffBD
import Book1.Prop47.hALDE
import Book1.Prop47.hALBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_intro_sentence "1.47.0"
    "In right-angled triangles,  the square on the side subtending the right-angle is equal to the (sum of the) squares on the sides containing the right-angle.  Let $ABC$ be a right-angled triangle having the angle $BAC$a right-angle. I say that the square on $BC$ is equal to the (sum of the) squares on $BA$ and $AC$. "

  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_sentence "1.47.1"
    "For let the square $BDEC$ have been described on $BC$, and (the squares) $GB$ and $HC$ on $AB$ and $AC$ (respectively) [Prop.~1.46]."
    (step1 :
      (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
        (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
      (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
        (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
      (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
        (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟))) := by euclid_apply (helper_1_47_step1 b c d e BC DE BD CE a g f AB GF AG BF h k AC HK AH CK (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:d:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ c:e:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(a─g)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─f)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(g─f)| = |(a─b)|; assumption)) (by euclid_assumption "" (show (∠ b:a:g : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:g:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:f:g : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─c)|; assumption)) (by euclid_assumption "" (show |(c─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show |(h─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show (∠ c:a:h : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:h:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ c:k:h : ℝ) = ∟; assumption)))

  have hoffBD : ¬(a.onLine BD) := by euclid_apply (helper_1_47_hoffBD a b c AB BC AC d BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)))
  euclid_apply (proposition_31 a b d BD) as AL
  have hALDE : AL.intersectsLine DE := by euclid_apply (helper_1_47_hALDE a b c d e AB BC AC AL BD DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show (∠ b:d:e : ℝ) = ∟; assumption)))
  euclid_apply (intersection_lines AL DE) as l
  euclid_sentence "1.47.2"
    "And let $AL$ have been drawn through point $A$ parallel to either of $BD$ or $CE$ [Prop.~1.31]."
    (step2 : a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE))) := by euclid_apply (helper_1_47_step2 a AL BD CE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)))

  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_sentence "1.47.3"
    "And let $AD$ and $FC$ have been joined."
    (step3 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC) := by euclid_apply (helper_1_47_step3 a b c d f AB BC AC BD BF AD FC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)))

  -- @assumption_valid
  have step4_assumption1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟) := by euclid_finish
  -- @assumption ("angles $BAC$ and $BAG$ are each right-angles", (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟))
  euclid_sentence "1.47.4"
    "And since angles $BAC$ and $BAG$ are each right-angles, then two straight-lines $AC$ and $AG$, not lying on the same side, make the adjacent angles with some straight-line $BA$, at the point $A$ on it, (whose sum is) equal to two right-angles."
    (step4 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟)) := by euclid_apply (helper_1_47_step4 a b c g AB (by euclid_assumption "" (show ¬g.sameSide c AB; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "angles $BAC$ and $BAG$ are each right-angles" (show (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟); assumption)))

  euclid_sentence "1.47.5"
    "Thus, $CA$ is straight-on to $AG$ [Prop.~1.14]."
    (step5 : between c a g) := by euclid_apply (helper_1_47_step5 a b c g AB AC AG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show ¬g.sameSide c AB; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:g : ℝ) = ∟; assumption)))

  euclid_sentence "1.47.6"
    "So, for the same (reasons), $BA$ is also straight-on to $AH$."
    (step6 : between b a h) := by euclid_apply (helper_1_47_step6 a b c h AB AC AH (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ c:a:h : ℝ) = ∟; assumption)))

  -- @assumption_valid
  have step7_assumption1 : ∠ d:b:c = ∠ f:b:a := by euclid_finish
  -- @assumption_valid
  have step7_assumption2 : (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟) := by euclid_finish
  -- @assumption ("angle $DBC$ is equal to $FBA$", ∠ d:b:c = ∠ f:b:a)
  -- @assumption ("for (they are) both right-angles", (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟))
  euclid_sentence "1.47.7"
    "And since angle $DBC$ is equal to $FBA$, for (they are) both right-angles, let $ABC$ have been added to both. "
    (step7 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) := by euclid_apply (helper_1_47_step7 a b c d f (by euclid_assumption "angle $DBC$ is equal to $FBA$" (show ∠ d:b:c = ∠ f:b:a; assumption)) (by euclid_assumption "for (they are) both right-angles" (show (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟); assumption)))

  euclid_sentence "1.47.8"
    "Thus, the whole (angle) $DBA$ is equal to the whole (angle) $FBC$."
    (step8 : ∠ d:b:a = ∠ f:b:c) := by euclid_apply (helper_1_47_step8 a b c d f g AB BC AC BD BF GF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬g.sameSide c AB; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ∠ d:b:c = ∠ f:b:a; assumption)))

  -- @assumption_valid
  have step9_assumption1 : |(d─b)| = |(b─c)| := by euclid_finish
  -- @assumption_valid
  have step9_assumption2 : |(f─b)| = |(b─a)| := by euclid_finish
  -- @assumption ("$DB$ is equal to $BC$", |(d─b)| = |(b─c)|)
  -- @assumption ("$FB$ to $BA$", |(f─b)| = |(b─a)|)
  euclid_sentence "1.47.9"
    "And since $DB$ is equal to $BC$, and $FB$ to $BA$, the two (straight-lines) $DB$, $BA$ are equal to the two (straight-lines) $CB$, $BF$, respectively."
    (step9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|) := by euclid_apply (helper_1_47_step9 a b c d f (by euclid_assumption "$DB$ is equal to $BC$" (show |(d─b)| = |(b─c)|; assumption)) (by euclid_assumption "$FB$ to $BA$" (show |(f─b)| = |(b─a)|; assumption)))

  euclid_sentence "1.47.10"
    "And angle $DBA$ (is) equal to angle $FBC$."
    (step10 : ∠ d:b:a = ∠ f:b:c) := by euclid_apply (helper_1_47_step10 a b c d f (by euclid_assumption "" (show ∠ d:b:a = ∠ f:b:c; assumption)))

  euclid_sentence "1.47.11"
    "Thus, the base $AD$ [is] equal to the base $FC$,"
    (step11 : |(a─d)| = |(f─c)|) := by euclid_apply (helper_1_47_step11 a b c d f AB BC AC BD AD FC BF (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(d─b)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(f─b)| = |(b─a)|; assumption)) (by euclid_assumption "" (show ∠ d:b:a = ∠ f:b:c; assumption)))

  euclid_sentence "1.47.12"
    "and the triangle $ABD$ is equal to the triangle $FBC$ [Prop.~1.4]."
    (step12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) := by euclid_apply (helper_1_47_step12 a b c d f AB BC AC BD AD FC BF (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show (∠ a:b:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(d─b)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(f─b)| = |(b─a)|; assumption)) (by euclid_assumption "" (show ∠ d:b:a = ∠ f:b:c; assumption)))

  have hALBC : AL.intersectsLine BC := by euclid_apply (helper_1_47_hALBC a b d AL BD BC (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)))
  euclid_apply (intersection_lines AL BC) as m
  -- @assumption_valid
  have step13_assumption1 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL) := by euclid_finish
  -- @assumption ("they have the same base, $BD$, and are between the same parallels, $BD$ and $AL$", b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL))
  euclid_sentence "1.47.13"
    "And  parallelogram $BL$ [is] double (the area) of triangle $ABD$. For they have the same base, $BD$, and are between the same parallels, $BD$ and $AL$  [Prop.~1.41]."
    (step13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d) := by euclid_apply (helper_1_47_step13 a b d l m AB BC BD DE AL AD (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "they have the same base, $BD$, and are between the same parallels, $BD$ and $AL$" (show b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL); assumption)))

  -- @assumption_valid
  have step14_assumption1 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC) := by euclid_finish
  -- @assumption ("they have the same base, $FB$, and are between the same parallels, $FB$ and $GC$", f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC))
  euclid_sentence "1.47.14"
    "And  square $GB$ is double (the area) of triangle $FBC$. For again they have the same base, $FB$, and are between the same parallels, $FB$ and $GC$ [Prop.~1.41]."
    (step14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by euclid_apply (helper_1_47_step14 a b c f g AB AC AG BF GF FC BC (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show between c a g; assumption)) (by euclid_assumption "they have the same base, $FB$, and are between the same parallels, $FB$ and $GC$" (show f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC); assumption)))

  euclid_sentence "1.47.15"
    "[And the doubles of equal things are equal to one another.]"
    (step15 : Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c) := by euclid_apply (helper_1_47_step15 a b c d f)

  euclid_sentence "1.47.16"
    "Thus, the parallelogram $BL$ is also equal to the square $GB$."
    (step16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b) := by euclid_apply (helper_1_47_step16 a b c d f g m l (by euclid_assumption "" (show Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:b:d + Triangle.area △ a:b:d; assumption)) (by euclid_assumption "" (show Triangle.area △ a:g:f + Triangle.area △ a:f:b = Triangle.area △ f:b:c + Triangle.area △ f:b:c; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:d = Triangle.area △ f:b:c → Triangle.area △ a:b:d + Triangle.area △ a:b:d = Triangle.area △ f:b:c + Triangle.area △ f:b:c; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:d = Triangle.area △ f:b:c; assumption)))

  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  euclid_sentence "1.47.17"
    "So, similarly, $AE$ and $BK$ being joined,  the parallelogram $CL$ can be shown (to be)  equal to the square $HC$."
    (step17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by euclid_apply (helper_1_47_step17 a b c d e h k l m AB AC AL AE BK CE DE BC BD AH CK HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show between b a h; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show |(c─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:c:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)))

  euclid_sentence "1.47.18"
    "Thus, the whole square $BDEC$ is equal to the (sum of the) two squares $GB$ and $HC$."
    (step18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c)) := by euclid_apply (helper_1_47_step18 a b c d e f g h k l m AB BC AC DE BD CE AL (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:c:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:a:c : ℝ) = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:g:f + Triangle.area △ a:f:b; assumption)) (by euclid_assumption "" (show Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:h:k + Triangle.area △ a:k:c; assumption)))

  euclid_sentence "1.47.19"
    "And the square $BDEC$ is described on $BC$,"
    (step19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|) := by euclid_apply (helper_1_47_step19 b c d e BC DE BD CE (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show (∠ c:b:d : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ b:d:e : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))

  euclid_sentence "1.47.20"
    "and the (squares) $GB$ and $HC$ on $BA$ and $AC$ (respectively)."
    (step20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|)) := by euclid_apply (helper_1_47_step20 a b c f g h k AB AC GF AG BF HK AH CK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show g.sameSide a BF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BF; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show h.sameSide a CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)) (by euclid_assumption "" (show (∠ a:g:f : ℝ) = ∟; assumption)) (by euclid_assumption "" (show (∠ a:h:k : ℝ) = ∟; assumption)) (by euclid_assumption "" (show |(a─g)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─c)|; assumption)))

  euclid_sentence "1.47.21"
    "Thus, the square on the side $BC$ is equal to the (sum of the) squares on the sides $BA$ and $AC$. "
    (step21 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)|) := by euclid_apply (helper_1_47_step21 a b c d e f g h k (by euclid_assumption "" (show Triangle.area △ b:d:e + Triangle.area △ b:e:c = (Triangle.area △ a:g:f + Triangle.area △ a:f:b) + (Triangle.area △ a:h:k + Triangle.area △ a:k:c); assumption)) (by euclid_assumption "" (show Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|; assumption)) (by euclid_assumption "" (show (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧ (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|); assumption)))

  exact step21
  euclid_conclude_sentence "1.47.22"
    "Thus, in right-angled triangles,  the square on the side subtending the right-angle is equal to the (sum of the) squares on the sides surrounding the right-[angle]. (Which is) the very thing it was required to show."

end Elements.Book1
