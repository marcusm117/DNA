import SystemE
import Book1Variants.Prop11
import Book1.Prop03.Main
import Book1.Prop31.Main
import Book1.Prop46.step1
import Book1.Prop46.step2
import Book1.Prop46.step3
import Book1.Prop46.step4
import Book1.Prop46.step5
import Book1.Prop46.step6
import Book1.Prop46.step7
import Book1.Prop46.step8
import Book1.Prop46.step9
import Book1.Prop46.step10
import Book1.Prop46.step12
import Book1.Prop46.step13
import Book1.Prop46.step14
import Book1.Prop46.step15
import Book1.Prop46.step16
import Book1.Prop46.step17
import Book1.Prop46.step18
import Book1.Prop46.step19
import Book1.Prop46.hbe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_46 : ∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB →
  ∃ (d e : Point) (DE AD BE : Line), formParallelogram d e a b DE AB AD BE ∧
  |(d─e)| = |(a─b)| ∧ |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
  (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.46.0"
    "To describe a square on a given straight-line. Let $AB$ be the given straight-line. So it is required to describe a square on the straight-line $AB$. "

  euclid_apply (extend_point AB b a) as g
  euclid_apply (proposition_11 b g a AB) as c
  euclid_apply (line_from_points a c) as AC
  euclid_sentence "1.46.1"
    "Let $AC$ have been drawn at right-angles to the straight-line $AB$ from the point $A$ on it [Prop.~1.11],"
    (step1 : ∠ c:a:b = ∟) := by euclid_apply (helper_1_46_step1 a b c AB (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  euclid_apply (extend_point_longer AC a c (a─b)) as c1
  euclid_apply (proposition_3 a c1 a b AC AB) as d
  euclid_apply (line_from_points a d) as AD
  euclid_sentence "1.46.2"
    "and let $AD$ have been made equal to $AB$ [Prop.~1.3]."
    (step2 : |(a─d)| = |(a─b)|) := by euclid_apply (helper_1_46_step2 a b d (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)))

  euclid_apply (proposition_31 d a b AB) as DE
  euclid_sentence "1.46.3"
    "And let $DE$ have been drawn through point $D$ parallel to $AB$ [Prop.~1.31],"
    (step3 : d.onLine DE ∧ ¬(DE.intersectsLine AB)) := by euclid_apply (helper_1_46_step3 a b d AB DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))

  euclid_apply (proposition_31 b a d AD) as BE
  euclid_apply (intersection_lines DE BE) as e
  euclid_sentence "1.46.4"
    "and let $BE$ have been drawn through point $B$ parallel to $AD$ [Prop.~1.31]."
    (step4 : b.onLine BE ∧ ¬(BE.intersectsLine AD)) := by euclid_apply (helper_1_46_step4 a b d AD BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬(BE.intersectsLine AD); assumption)))

  euclid_sentence "1.46.5"
    "Thus, $ADEB$ is a parallelogram."
    (step5 : formParallelogram d e a b DE AB AD BE) := by euclid_apply (helper_1_46_step5 a b c d e c1 AB AC AD BE DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show c1.onLine AC; assumption)) (by euclid_assumption "" (show between a d c1; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine AD; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)))

  euclid_sentence "1.46.6"
    "Therefore, $AB$ is equal to $DE$,"
    (step6 : |(a─b)| = |(d─e)|) := by euclid_apply (helper_1_46_step6 a b d e AB AD BE DE (by euclid_assumption "" (show formParallelogram d e a b DE AB AD BE; assumption)))

  euclid_sentence "1.46.7"
    "and $AD$ to $BE$ [Prop.~1.34]."
    (step7 : |(a─d)| = |(b─e)|) := by euclid_apply (helper_1_46_step7 a b d e AB AD BE DE (by euclid_assumption "" (show formParallelogram d e a b DE AB AD BE; assumption)))

  euclid_sentence "1.46.8"
    "But, $AB$ is equal to $AD$."
    (step8 : |(a─b)| = |(a─d)|) := by euclid_apply (helper_1_46_step8 a b d (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)))

  euclid_sentence "1.46.9"
    "Thus, the four (sides) $BA$, $AD$, $DE$, and $EB$ are equal to one another."
    (step9 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by euclid_apply (helper_1_46_step9 a b d e (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─e)|; assumption)))

  euclid_sentence "1.46.10"
    "Thus, the parallelogram $ADEB$ is equilateral."
    (step10 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by euclid_apply (helper_1_46_step10 a b d e (by euclid_assumption "" (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  euclid_wts "1.46.11"
    "So I say that (it is) also right-angled."

  -- @assumption_valid
  have step12_assumption1 : ¬(DE.intersectsLine AB) := by assumption
  -- @assumption ("the straight-line $AD$ falls across the parallels $AB$ and $DE$", ¬(DE.intersectsLine AB))
  euclid_sentence "1.46.12"
    "For since the straight-line $AD$ falls across the parallels $AB$ and $DE$, the (sum of the) angles $BAD$ and $ADE$ is equal to two right-angles [Prop.~1.29]."
    (step12 : ∠ b:a:d + ∠ a:d:e = ∟ + ∟) := by euclid_apply (helper_1_46_step12 a b c d e c1 AB AC AD BE DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c1.onLine AC; assumption)) (by euclid_assumption "" (show between a d c1; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "the straight-line $AD$ falls across the parallels $AB$ and $DE$" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(BE.intersectsLine AD); assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)))

  euclid_sentence "1.46.13"
    "But $BAD$ (is a) right-angle."
    (step13 : ∠ b:a:d = ∟) := by euclid_apply (helper_1_46_step13 a b c d c1 AB AC AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c1.onLine AC; assumption)) (by euclid_assumption "" (show between a c c1; assumption)) (by euclid_assumption "" (show between a d c1; assumption)) (by euclid_assumption "" (show ¬c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ c:a:b = ∟; assumption)))

  euclid_sentence "1.46.14"
    "Thus, $ADE$ (is) also a right-angle."
    (step14 : ∠ a:d:e = ∟) := by euclid_apply (helper_1_46_step14 a b d e (by euclid_assumption "" (show ∠ b:a:d + ∠ a:d:e = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))

  euclid_sentence "1.46.15"
    "And for parallelogrammic figures, the opposite sides and angles are equal to one another [Prop.~1.34]."
    (step15 : formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e)) := by euclid_apply (helper_1_46_step15 a b d e AB AD BE DE)

  euclid_sentence "1.46.16"
    "Thus, each of the opposite angles $ABE$ and $BED$ (are) also right-angles."
    (step16 : ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) := by euclid_apply (helper_1_46_step16 a b d e AB AD BE DE (by euclid_assumption "" (show formParallelogram d e a b DE AB AD BE; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show formParallelogram d e a b DE AB AD BE → (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e); assumption)))

  euclid_sentence "1.46.17"
    "Thus, $ADEB$ is right-angled."
    (step17 : ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) := by euclid_apply (helper_1_46_step17 a b d e (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟; assumption)))

  euclid_sentence "1.46.18"
    "And it was also shown (to be) equilateral.  "
    (step18 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) := by euclid_apply (helper_1_46_step18 a b d e (by euclid_assumption "" (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  euclid_sentence "1.46.19"
    "Thus, ($ADEB$) is a square [Def.~1.22]."
    (step19 : (|(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) ∧
      (∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟)) := by euclid_apply (helper_1_46_step19 a b d e (by euclid_assumption "" (show ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|; assumption)))

  have hbe : |(b─e)| = |(a─b)| := by euclid_apply (helper_1_46_hbe a b d e (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─e)|; assumption)))
  exact ⟨d, e, DE, AD, BE, step5, step6.symm, step2, hbe, step13, step14, step16.1, step16.2⟩
  euclid_conclude_sentence "1.46.20"
    "And it is described on the straight-line $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
