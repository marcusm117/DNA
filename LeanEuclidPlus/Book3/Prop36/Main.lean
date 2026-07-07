import SystemE
import Book1.Prop12.Main
import Book3.Prop01.Main
set_option linter.unusedVariables false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_36 : ∀ (a b c d : Point) (ABC : Circle) (DB : Line),
    a.onCircle ABC ∧ c.onCircle ABC ∧ d.outsideCircle ABC ∧
    between d c a ∧
    d.onLine DB ∧ b.onLine DB ∧ b.onCircle ABC ∧ ¬ DB.intersectsCircle ABC →
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| :=
by
  euclid_intros
  euclid_intro_sentence "3.36.0"
    "If some point is taken outside a circle, and two straight-lines radiate from it towards the circle, and (one) of them cuts the circle, and the (other) touches (it), (then) the (rectangle contained) by the whole (straight-line) cutting (the circle), and the (part of it) cut off outside (the circle), between the point and the convex circumference, will be equal to the square on the tangent (line). For let some point $D$ be taken outside circle $ABC$, and let two straight-lines, $DC[A]$ and $DB$, radiate from $D$ towards circle $ABC$. And let $DCA$ cut circle $ABC$, and let $BD$ touch (it). I say that the rectangle contained by $AD$ and $DC$ is equal to the square on $DB$."

  -- secant line: d, c, a are collinear (between d c a), so line through d and a contains c
  euclid_apply (line_from_points d a) as DA

  euclid_sentence "3.36.1"
    "$[D]CA$ is surely either through the center, or not."
    (step1 : (∃ f : Point, f.isCentre ABC ∧ f.onLine DA) ∨
             ¬(∃ f : Point, f.isCentre ABC ∧ f.onLine DA)) := by sorry

  -- orchestrator-2case: classical case split on whether center of ABC lies on secant DA
  rcases step1 with ⟨f, hfcenter, hfDA⟩ | hnotthrough

  · -- Case 1: DCA is through the center (center = f, f.onLine DA)
    euclid_apply (line_from_points f b) as FB

    -- @assumption ("$F$ be the center of circle $ABC$", f.isCentre ABC)
    euclid_sentence "3.36.2"
      "Let it first of all be through the center, and let $F$ be the center of circle $ABC$, and let $FB$ be joined."
      (step2 : distinctPointsOnLine f b FB) := by sorry

    euclid_sentence "3.36.3"
      "Thus, (angle) $FBD$ is a right-angle [Prop.~3.18]."
      (step3 : ∠ f:b:d = ∟) := by sorry

    -- @assumption ("straight-line $AC$ is cut in half at $F$", |(a─f)| = |(f─c)|)
    euclid_sentence "3.36.4"
      "And since straight-line $AC$ is cut in half at $F$, let $CD$ be added to it."
      (step4 : |(a─f)| = |(f─c)|) := by sorry

    euclid_sentence "3.36.5"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $FC$ is equal to the (square) on $FD$ [Prop.~2.6]."
      (step5 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|) := by sorry

    euclid_sentence "3.36.6"
      "And $FC$ (is) equal to $FB$."
      (step6 : |(f─c)| = |(f─b)|) := by sorry

    euclid_sentence "3.36.7"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $FB$ is equal to the (square) on $FD$."
      (step7 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)|) := by sorry

    euclid_sentence "3.36.8"
      "And the (square) on $FD$ is equal to the (sum of the squares) on $FB$ and $BD$ [Prop.~1.47]."
      (step8 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) := by sorry

    euclid_sentence "3.36.9"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $FB$ is equal to the (sum of the squares) on $FB$ and $BD$."
      (step9 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) := by sorry

    euclid_sentence "3.36.10"
      "Let the (square) on $FB$ be subtracted from both."
      (step10 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|) := by sorry

    euclid_sentence "3.36.11"
      "Thus, the remaining (rectangle contained) by $AD$ and $DC$ is equal to the (square) on the tangent $DB$."
      (step11 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|) := by sorry

    exact step11

  · -- Case 2: DCA is NOT through the center
    euclid_wts "3.36.12"
      "And so let $DCA$ not be through the center of circle $ABC$,"

    -- find center E via Prop. 3.1
    euclid_apply (proposition_1 ABC) as e

    euclid_sentence "3.36.13"
      "and let the center $E$ be found,"
      (step13 : e.isCentre ABC) := by sorry

    -- drop perpendicular from e to DA (= line AC), foot = f, line = EF [Prop. 1.12]
    euclid_apply (proposition_12 a c e DA) as f
    euclid_apply (line_from_points e f) as EF

    euclid_sentence "3.36.14"
      "and let $EF$ be drawn from $E$, perpendicular to $AC$ [Prop.~1.12]."
      (step14 : f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)) := by sorry

    -- join EB, EC, ED
    euclid_apply (line_from_points e b) as EB
    euclid_apply (line_from_points e c) as EC
    euclid_apply (line_from_points e d) as ED

    euclid_sentence "3.36.15"
      "And let $EB$, $EC$, and $ED$ be joined."
      (step15 : distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED) := by sorry

    euclid_sentence "3.36.16"
      "(Angle) $EBD$ (is) thus a right-angle [Prop.~3.18]."
      (step16 : ∠ e:b:d = ∟) := by sorry

    -- @assumption ("some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles", e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    euclid_sentence "3.36.17"
      "And since some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles, it also cuts it in half [Prop.~3.3]."
      (step17 : |(a─f)| = |(f─c)|) := by sorry

    euclid_sentence "3.36.18"
      "Thus, $AF$ is equal to $FC$."
      (step18 : |(a─f)| = |(f─c)|) := by sorry

    -- @assumption ("the straight-line $AC$ is cut in half at point $F$", |(a─f)| = |(f─c)|)
    euclid_sentence "3.36.19"
      "And since the straight-line $AC$ is cut in half at point $F$, let $CD$ be added to it."
      (step19 : |(a─f)| = |(f─c)|) := by sorry

    euclid_sentence "3.36.20"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $FC$ is equal to the (square) on $FD$ [Prop.~2.6]."
      (step20 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|) := by sorry

    euclid_sentence "3.36.21"
      "Let the (square) on $FE$ be added to both."
      (step21 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| = |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|) := by sorry

    euclid_sentence "3.36.22"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (sum of the squares) on $CF$ and $FE$ is equal to the (sum of the squares) on $FD$ and $FE$."
      (step22 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| = |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|) := by sorry

    -- @assumption ("$EFC$ [is] a right-angle", ∠ e:f:c = ∟)
    euclid_sentence "3.36.23"
      "But the (square) on $EC$ is equal to the (sum of the squares) on $CF$ and $FE$. For [angle] $EFC$ [is] a right-angle [Prop.~1.47]."
      (step23 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)|) := by sorry

    euclid_sentence "3.36.24"
      "And the (square) on $ED$ is equal to the (sum of the squares) on $DF$ and $FE$ [Prop.~1.47]."
      (step24 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)|) := by sorry

    euclid_sentence "3.36.25"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $EC$ is equal to the (square) on $ED$."
      (step25 : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)|) := by sorry

    euclid_sentence "3.36.26"
      "And $EC$ (is) equal to $EB$."
      (step26 : |(e─c)| = |(e─b)|) := by sorry

    euclid_sentence "3.36.27"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $EB$ is equal to the (square) on $ED$."
      (step27 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)|) := by sorry

    -- @assumption ("$EBD$ (is) a right-angle", ∠ e:b:d = ∟)
    euclid_sentence "3.36.28"
      "And the (sum of the squares) on $EB$ and $BD$ is equal to the (square) on $ED$. For $EBD$ (is) a right-angle [Prop.~1.47]."
      (step28 : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)|) := by sorry

    euclid_sentence "3.36.29"
      "Thus, the (rectangle contained) by $AD$ and $DC$ plus the (square) on $EB$ is equal to the (sum of the squares) on $EB$ and $BD$."
      (step29 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)|) := by sorry

    euclid_sentence "3.36.30"
      "Let the (square) on $EB$ be subtracted from both."
      (step30 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|) := by sorry

    euclid_sentence "3.36.31"
      "Thus, the remaining (rectangle contained) by $AD$ and $DC$ is equal to the (square) on $BD$."
      (step31 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|) := by sorry

    exact step31
    euclid_conclude_sentence "3.36.32"
      "Thus, if some point is taken outside a circle, and two straight-lines radiate from it towards the circle, and (one) of them cuts the circle, and (the other) touches (it), (then) the (rectangle contained) by the whole (straight-line) cutting (the circle), and the (part of it) cut off outside (the circle), between the point and the convex circumference, will be equal to the square on the tangent (line). (Which is) the very thing it was required to show."

end Elements.Book3
