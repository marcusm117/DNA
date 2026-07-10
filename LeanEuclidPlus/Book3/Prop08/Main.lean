import SystemE
import Book3.Prop01.Main
import Mathlib.Tactic.Linarith
import Book3.Prop08.step1
import Book3.Prop08.step2
import Book3.Prop08.step3
import Book3.Prop08.step4
import Book3.Prop08.step5
import Book3.Prop08.step6
import Book3.Prop08.step7
import Book3.Prop08.step8
import Book3.Prop08.step9
import Book3.Prop08.step10
import Book3.Prop08.step11
import Book3.Prop08.step12
import Book3.Prop08.step13
import Book3.Prop08.step14
import Book3.Prop08.step15
import Book3.Prop08.step16
import Book3.Prop08.step17
import Book3.Prop08.step18
import Book3.Prop08.step19
import Book3.Prop08.step20
import Book3.Prop08.step21
import Book3.Prop08.step23
import Book3.Prop08.step24
import Book3.Prop08.step25
import Book3.Prop08.step26
import Book3.Prop08.step28
import Book3.Prop08.step29
import Book3.Prop08.step30
import Book3.Prop08.step31
import Book3.Prop08.step32
import Book3.Prop08.step5_assumption1
import Book3.Prop08.step13_assumption1
import Book3.Prop08.step15_assumption1
import Book3.Prop08.hb0_exist
import Book3.Prop08.huniq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_8 : ∀ (ABC : Circle) (m d a e f c g k l h : Point) (AG : Line),
  m.isCentre ABC →
  d.outsideCircle ABC →
  -- Diameter: G convex (near, between D and center), A concave (far, beyond center from D)
  a.onCircle ABC →
  g.onCircle ABC →
  distinctPointsOnLine a g AG →
  d.onLine AG →
  between d g m →
  between g m a →
  -- Concave-arc points: E, F, C — each has a convex (near) partner between D and it on the same line
  e.onCircle ABC → (∃ en : Point, en.onCircle ABC ∧ between d en e) →
  f.onCircle ABC → (∃ fn : Point, fn.onCircle ABC ∧ between d fn f) →
  c.onCircle ABC → (∃ cn : Point, cn.onCircle ABC ∧ between d cn c) →
  -- Convex-arc points: K, L, H — each has a concave (far) partner beyond it from D on the same line
  k.onCircle ABC → (∃ kf : Point, kf.onCircle ABC ∧ between d k kf) →
  l.onCircle ABC → (∃ lf : Point, lf.onCircle ABC ∧ between d l lf) →
  h.onCircle ABC → (∃ hf : Point, hf.onCircle ABC ∧ between d h hf) →
  -- Non-degeneracy: concave arc points ≠ far endpoint; c also ≠ near endpoint g (not angle-derivable)
  e ≠ a → f ≠ a → c ≠ a → c ≠ g →
  k ≠ g → l ≠ g → h ≠ g →
  -- Angle ordering at M for concave lines (nearer to DA = larger angle at M)
  ∠ e:m:d > ∠ f:m:d → ∠ f:m:d > ∠ c:m:d →
  -- Angle ordering at M for convex lines (nearer to DG = smaller angle at M)
  ∠ k:m:d < ∠ l:m:d → ∠ l:m:d < ∠ h:m:d →
  -- Same-side condition for convex arc: k and l on same side of diameter AG (figure-reading)
  l.sameSide k AG →
  -- (1) CONCAVE: DA is the greatest line to the concave arc; nearer-to-DA is greater
  ( |(d─a)| > |(d─e)| ∧ |(d─e)| > |(d─f)| ∧ |(d─f)| > |(d─c)| ) ∧
  -- (2) CONVEX: DG is the least line to the convex arc; nearer-to-DG is less
  ( |(d─g)| < |(d─k)| ∧ |(d─k)| < |(d─l)| ∧ |(d─l)| < |(d─h)| ) ∧
  -- (3) Exactly two equal lines from D to the circle, one each side of DG: DK and its angle-mirror DB
  ∃ b : Point, b.onCircle ABC ∧ b.opposingSides k AG ∧ |(d─b)| = |(d─k)| ∧
    ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b :=
by
  euclid_intros
  euclid_intro_sentence "3.8.0"
    "If some point is taken outside a circle, and some straight-lines are drawn from the point to the (circumference of the) circle, one of which (passes) through the center, the remainder (being) random, (then) for the straight-lines radiating towards the concave (part of the) circumference, the greatest is that (passing) through the center. For the others, a (straight-line) nearer$^\\dag$ to the (straight-line) through the center is always greater than one further away. For the straight-lines radiating towards the convex (part of the) circumference, the least is that between the point and the diameter. For the others, a (straight-line) nearer to the least (straight-line) is always less than one further away. And only two equal (straight-lines) will radiate from the point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). Let $ABC$ be a circle, and let some point $D$ be taken outside $ABC$, and from it let some straight-lines, $DA$, $DE$, $DF$, and $DC$, be drawn through (the circle), and let $DA$ be through the center. I say that for the straight-lines radiating towards the concave (part of the) circumference, $AEFC$, the greatest is the one (passing) through the center, (namely) $AD$, and (that) $DE$ (is) greater than $DF$, and $DF$ than $DC$. For the straight-lines radiating towards the convex (part of the) circumference, $HLKG$, the least is the one between the point and the diameter $AG$, (namely) $DG$, and a (straight-line) nearer to the least (straight-line) $DG$ is always less than one farther away, (so that) $DK$ (is less) than $DL$, and $DL$ than than $DH$."

  euclid_apply (proposition_1 ABC) as m'
  euclid_sentence "3.8.1"
    "For let the center of the circle be found [Prop.~3.1], and let it be (at point) $M$ [Prop.~3.1]."
    (step1 : m'.isCentre ABC ∧ m' = m) := by euclid_apply (helper_3_8_step1 ABC m m' (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show m'.isCentre ABC; assumption)))

  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points m f) as MF
  euclid_apply (line_from_points m c) as MC
  euclid_apply (line_from_points m k) as MK
  euclid_apply (line_from_points m l) as ML
  euclid_apply (line_from_points m h) as MH
  euclid_sentence "3.8.2"
    "And let $ME$, $MF$, $MC$, $MK$, $ML$, and $m\\kern -.7pt h$ be joined."
    (step2 : distinctPointsOnLine m e ME ∧ distinctPointsOnLine m f MF ∧ distinctPointsOnLine m c MC ∧
             distinctPointsOnLine m k MK ∧ distinctPointsOnLine m l ML ∧ distinctPointsOnLine m h MH) := by euclid_apply (helper_3_8_step2 ABC m e f c k l h ME MF MC MK ML MH (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show m.onLine MF; assumption)) (by euclid_assumption "" (show f.onLine MF; assumption)) (by euclid_assumption "" (show m.onLine MC; assumption)) (by euclid_assumption "" (show c.onLine MC; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine ML; assumption)) (by euclid_assumption "" (show m.onLine MH; assumption)) (by euclid_assumption "" (show h.onLine MH; assumption)))

  -- @assumption_valid
  have step3_assumption1 : |(m─a)| = |(m─e)| := by euclid_finish
  -- @assumption ("$AM$ is equal to $EM$", |(m─a)| = |(m─e)|)
  euclid_sentence "3.8.3"
    "And since $AM$ is equal to $EM$, let $MD$ be added to both."
    (step3 : |(m─a)| + |(m─d)| = |(e─m)| + |(m─d)|) := by euclid_apply (helper_3_8_step3 (by euclid_assumption "$AM$ is equal to $EM$" (show |(m─a)| = |(m─e)|; assumption)))

  euclid_sentence "3.8.4"
    "Thus, $AD$ is equal to $EM$ and $MD$."
    (step4 : |(d─a)| = |(e─m)| + |(m─d)|) := by euclid_apply (helper_3_8_step4 d g m a e (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show |(m─a)| + |(m─d)| = |(e─m)| + |(m─d)|; assumption)))

  -- @assumption_gap
  have step5_assumption1 : |(e─m)| + |(m─d)| > |(e─d)| := by euclid_apply (helper_3_8_step5_assumption1 ABC m e f d g a ME AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show ∠ e:m:d > ∠ f:m:d; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)))
  -- @assumption ("$EM$ and $MD$ is greater than $ED$", |(e─m)| + |(m─d)| > |(e─d)|)
  euclid_sentence "3.8.5"
    "But, $EM$ and $MD$ is greater than $ED$ [Prop.~1.20]. Thus, $AD$ is also greater than $ED$."
    (step5 : |(d─a)| > |(d─e)|) := by euclid_apply (helper_3_8_step5 ABC m e f d g a ME AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show ∠e:m:d > ∠f:m:d; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show |(d─a)| = |(e─m)| + |(m─d)|; assumption)) (by euclid_assumption "$EM$ and $MD$ is greater than $ED$" (show |(e─m)| + |(m─d)| > |(e─d)|; assumption)))

  -- @assumption_valid
  have step6_assumption1 : |(m─e)| = |(m─f)| := by euclid_finish
  -- @assumption_valid
  have step6_assumption2 : |(m─d)| = |(m─d)| := by rfl
  -- @assumption ("$ME$ is equal to $MF$", |(m─e)| = |(m─f)|)
  -- @assumption ("$MD$ (is) common", |(m─d)| = |(m─d)|)
  euclid_sentence "3.8.6"
    "Again, since $ME$ is equal to $MF$, and $MD$ (is) common, the (straight-lines) $EM$, $MD$ are thus equal to $FM$, $MD$."
    (step6 : |(e─m)| + |(m─d)| = |(f─m)| + |(m─d)|) := by euclid_apply (helper_3_8_step6 (by euclid_assumption "$ME$ is equal to $MF$" (show |(m─e)| = |(m─f)|; assumption)) (by euclid_assumption "$MD$ (is) common" (show |(m─d)| = |(m─d)|; assumption)))

  euclid_sentence "3.8.7"
    "And angle $EMD$ is greater than angle $FMD$.$^\\ddag$"
    (step7 : ∠ e:m:d > ∠ f:m:d) := by euclid_apply (helper_3_8_step7 e m f d (by euclid_assumption "" (show ∠ e:m:d > ∠ f:m:d; assumption)))

  euclid_sentence "3.8.8"
    "Thus, the base $ED$ is greater than the base $FD$ [Prop.~1.24]."
    (step8 : |(d─e)| > |(d─f)|) := by euclid_apply (helper_3_8_step8 ABC m e f c d g a ME MF AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)) (by euclid_assumption "" (show |(m─e)| = |(m─f)|; assumption)) (by euclid_assumption "" (show ∠ e:m:d > ∠ f:m:d; assumption)) (by euclid_assumption "" (show ∠ f:m:d > ∠ c:m:d; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show m.onLine MF; assumption)) (by euclid_assumption "" (show f.onLine MF; assumption)))

  euclid_sentence "3.8.9"
    "So, similarly, we can show that $FD$ is also greater than $CD$."
    (step9 : |(d─f)| > |(d─c)|) := by euclid_apply (helper_3_8_step9 ABC m f c d g a MF MC AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)) (by euclid_assumption "" (show ∠ f:m:d > ∠ c:m:d; assumption)) (by euclid_assumption "" (show m.onLine MF; assumption)) (by euclid_assumption "" (show f.onLine MF; assumption)) (by euclid_assumption "" (show m.onLine MC; assumption)) (by euclid_assumption "" (show c.onLine MC; assumption)))

  euclid_sentence "3.8.10"
    "Thus, $AD$ (is) the greatest (straight-line),"
    (step10 : |(d─a)| > |(d─e)|) := by euclid_apply (helper_3_8_step10 d a e (by euclid_assumption "" (show |(d─a)| > |(d─e)|; assumption)))

  euclid_sentence "3.8.11"
    "and $DE$ (is) greater than $DF$,"
    (step11 : |(d─e)| > |(d─f)|) := by euclid_apply (helper_3_8_step11 d e f (by euclid_assumption "" (show |(d─e)| > |(d─f)|; assumption)))

  euclid_sentence "3.8.12"
    "and $DF$ than $DC$."
    (step12 : |(d─f)| > |(d─c)|) := by euclid_apply (helper_3_8_step12 d f c (by euclid_assumption "" (show |(d─f)| > |(d─c)|; assumption)))

  -- @assumption_gap
  have step13_assumption1 : |(m─k)| + |(k─d)| > |(m─d)| := by euclid_apply (helper_3_8_step13_assumption1 ABC m k d g a l MK AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show k ≠ g; assumption)) (by euclid_assumption "" (show ∠k:m:d < ∠l:m:d; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)))
  -- @assumption_valid
  have step13_assumption2 : |(m─g)| = |(m─k)| := by euclid_finish
  -- @assumption ("$MK$ and $KD$ is greater than $MD$", |(m─k)| + |(k─d)| > |(m─d)|)
  -- @assumption ("$MG$ (is) equal to $MK$", |(m─g)| = |(m─k)|)
  euclid_sentence "3.8.13"
    "And since $MK$ and $KD$ is greater than $MD$ [Prop. 1.20], and $MG$ (is) equal to $MK$, the remainder $KD$ is thus greater than the remainder $GD$."
    (step13 : |(d─k)| > |(d─g)|) := by euclid_apply (helper_3_8_step13 k g m d (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "$MK$ and $KD$ is greater than $MD$" (show |(m─k)| + |(k─d)| > |(m─d)|; assumption)) (by euclid_assumption "$MG$ (is) equal to $MK$" (show |(m─g)| = |(m─k)|; assumption)))

  euclid_sentence "3.8.14"
    "So $GD$ is less than $KD$."
    (step14 : |(d─g)| < |(d─k)|) := by euclid_apply (helper_3_8_step14 d g k (by euclid_assumption "" (show |(d─k)| > |(d─g)|; assumption)))

  euclid_apply (line_from_points l d) as LD
  -- @assumption_gap
  -- @euclid_gap: Euclid reads K inside triangle MLD from the figure; m.sameSide k LD is false when D is barely outside the circle (K can lie on the wrong side of LD); handled via by_cases in step15
  have step15_assumption1 : formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG := by euclid_apply (helper_3_8_step15_assumption1 ABC m k l d g a h MK ML LD AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show k ≠ g; assumption)) (by euclid_assumption "" (show l ≠ g; assumption)) (by euclid_assumption "" (show ∠k:m:d < ∠l:m:d; assumption)) (by euclid_assumption "" (show ∠l:m:d < ∠h:m:d; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine LD; assumption)) (by euclid_assumption "" (show d.onLine LD; assumption)) (by euclid_assumption "" (show l.sameSide k AG; assumption)))
  -- @suppress_deps_check "source cites [Prop.~1.21] (internal lines < two sides) but I.21 requires m.sameSide k LD which is the @euclid_gap (K inside triangle MLD not provable without figure assumption); formal proof uses proposition_24 via angle comparison"
  -- @assumption ("in triangle $MLD$, the two internal straight-lines $MK$ and $KD$ were constructed on one of the sides, $MD$", formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG)
  euclid_sentence "3.8.15"
    "And since in triangle $MLD$, the two internal straight-lines $MK$ and $KD$ were constructed on one of the sides, $MD$, (then) $MK$ and $KD$ are thus less than $ML$ and $LD$ [Prop.~1.21]."
    (step15 : |(m─k)| + |(k─d)| < |(m─l)| + |(l─d)|) := by euclid_apply (helper_3_8_step15 ABC m k l d MK ML LD AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show ∠k:m:d < ∠l:m:d; assumption)) (by euclid_assumption "in triangle $MLD$, the two internal straight-lines $MK$ and $KD$ were constructed on one of the sides, $MD$" (show formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG; assumption)))

  euclid_sentence "3.8.16"
    "And $MK$ (is) equal to $ML$."
    (step16 : |(m─k)| = |(m─l)|) := by euclid_apply (helper_3_8_step16 ABC m k l (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)))

  euclid_sentence "3.8.17"
    "Thus, the remainder $DK$ is less than the remainder $DL$."
    (step17 : |(d─k)| < |(d─l)|) := by euclid_apply (helper_3_8_step17 (by euclid_assumption "" (show |(m─k)| + |(k─d)| < |(m─l)| + |(l─d)|; assumption)) (by euclid_assumption "" (show |(m─k)| = |(m─l)|; assumption)))

  -- Reconstruct the far-partner existential for h from the destructured inaccessible parts
  -- (the proposition's ∃ hf was destructured by euclid_intros into w✝/left✝¹⁸/right✝¹²)
  have hhfar_h : ∃ p : Point, p.onCircle ABC ∧ between d h p := ⟨_, by assumption, by assumption⟩
  euclid_sentence "3.8.18"
    "So, similarly, we can show that $DL$ is also less than $DH$."
    (step18 : |(d─l)| < |(d─h)|) := by euclid_apply (helper_3_8_step18 ABC m k l d h g a ML LD MH AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.insideCircle ABC; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show h ≠ g; assumption)) (by euclid_assumption "" (show a ≠ g; assumption)) (by euclid_assumption "" (show m.onLine MH; assumption)) (by euclid_assumption "" (show h.onLine MH; assumption)) (by euclid_assumption "" (show m ≠ h; assumption)) (by euclid_assumption "" (show ∠l:m:d < ∠h:m:d; assumption)) (by euclid_assumption "" (show ∃ p : Point, p.onCircle ABC ∧ between d h p; assumption)) (by euclid_assumption "" (show formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG; assumption)))

  euclid_sentence "3.8.19"
    "Thus, $DG$ (is) the least (straight-line),"
    (step19 : |(d─g)| < |(d─k)|) := by euclid_apply (helper_3_8_step19 (by euclid_assumption "" (show |(d─g)| < |(d─k)|; assumption)))

  euclid_sentence "3.8.20"
    "and $DK$ (is) less than $DL$,"
    (step20 : |(d─k)| < |(d─l)|) := by euclid_apply (helper_3_8_step20 (by euclid_assumption "" (show |(d─k)| < |(d─l)|; assumption)))

  euclid_sentence "3.8.21"
    "and $DL$ than $DH$."
    (step21 : |(d─l)| < |(d─h)|) := by euclid_apply (helper_3_8_step21 (by euclid_assumption "" (show |(d─l)| < |(d─h)|; assumption)))

  euclid_wts "3.8.22"
    "I also say that only two equal (straight-lines) will radiate from point $D$ towards (the circumference of) the circle, (one) on each (side) on the least (straight-line), $DG$."

  have hb0_exist : ∃ b0 : Point, b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d := by euclid_apply (helper_3_8_hb0_exist ABC m k l d g a AG MK (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show l.sameSide k AG; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m ≠ k; assumption)))
  obtain ⟨b0, hb0_circ, hb0_opp, hb0_ang⟩ := hb0_exist
  euclid_apply (line_from_points d b0) as DB
  euclid_sentence "3.8.23"
    "Let the angle $DMB$, equal to angle $KMD$, be constructed on the straight-line $MD$, at the point $M$ on it [Prop.~1.23], and let $DB$ be joined."
    (step23 : b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d ∧ distinctPointsOnLine d b0 DB) := by euclid_apply (helper_3_8_step23 ABC m d k b0 AG DB MK (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬d.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show b0.onCircle ABC; assumption)) (by euclid_assumption "" (show ∠ d:m:b0 = ∠ k:m:d; assumption)) (by euclid_assumption "" (show ¬b0.onLine AG; assumption)) (by euclid_assumption "" (show ¬k.onLine AG; assumption)) (by euclid_assumption "" (show ¬b0.sameSide k AG; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b0.onLine DB; assumption)) (by euclid_assumption "" (show m.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)))

  -- @assumption_valid
  have step24_assumption1 : |(m─k)| = |(m─b0)| := by euclid_finish
  -- @assumption_valid
  have step24_assumption2 : |(m─d)| = |(m─d)| := by rfl
  -- @assumption ("$MK$ is equal to $MB$", |(m─k)| = |(m─b0)|)
  -- @assumption ("$MD$ (is) common", |(m─d)| = |(m─d)|)
  euclid_sentence "3.8.24"
    "And since $MK$ is equal to $MB$, and $MD$ (is) common, the two (straight-lines) $KM$, $MD$ are equal to the two (straight-lines) $BM$, $MD$, respectively."
    (step24 : |(k─m)| = |(b0─m)|) := by euclid_apply (helper_3_8_step24 m k b0 d (by euclid_assumption "$MK$ is equal to $MB$" (show |(m─k)| = |(m─b0)|; assumption)) (by euclid_assumption "$MD$ (is) common" (show |(m─d)| = |(m─d)|; assumption)))

  euclid_sentence "3.8.25"
    "And angle $KMD$ (is) equal to angle $BMD$."
    (step25 : ∠ k:m:d = ∠ b0:m:d) := by euclid_apply (helper_3_8_step25 ABC m k d b0 g (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show b0.onCircle ABC; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show ∠ d:m:b0 = ∠ k:m:d; assumption)))

  euclid_sentence "3.8.26"
    "Thus, the base $DK$ is equal to the base $DB$ [Prop.~1.4]."
    (step26 : |(d─k)| = |(d─b0)|) := by euclid_apply (helper_3_8_step26 ABC m k d b0 g MK DB AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show b0.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m ≠ k; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b0.onLine DB; assumption)) (by euclid_assumption "" (show m.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show ¬k.onLine AG; assumption)) (by euclid_assumption "" (show ¬b0.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show |(m─k)| = |(m─b0)|; assumption)) (by euclid_assumption "" (show ∠ k:m:d = ∠ b0:m:d; assumption)))

  euclid_wts "3.8.27"
    "[So] I say that another (straight-line) equal to $DK$ will not radiate towards the (circumference of the) circle from point $D$."

  -- Uniqueness reductio: suppose another point N on the circle with |DN| = |DK|, N ≠ K, N ≠ B.
  have habsurd1 : ¬(∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0) := by
    intro hsuppose1
    obtain ⟨n, hn_circ, hn_dist, hn_ne_k, hn_ne_b⟩ := hsuppose1
    euclid_sentence "3.8.28"
      "For, if possible, let (such a straight-line) radiate, and let it be $DN$."
      (step28 : n.onCircle ABC ∧ |(d─n)| = |(d─k)|) := by euclid_apply (helper_3_8_step28 ABC d k n (by euclid_assumption "" (show n.onCircle ABC; assumption)) (by euclid_assumption "" (show |(d─n)| = |(d─k)|; assumption)))

    -- @assumption_valid
    have step29_assumption1 : |(d─k)| = |(d─n)| := by linarith
    -- @assumption_valid
    have step29_assumption2 : |(d─k)| = |(d─b0)| := by assumption
    -- @assumption ("$DK$ is equal to $DN$", |(d─k)| = |(d─n)|)
    -- @assumption ("$DK$ is equal to $DB$", |(d─k)| = |(d─b0)|)
    euclid_sentence "3.8.29"
      "Therefore, since $DK$ is equal to $DN$, but $DK$ is equal to $DB$, (then) $DB$ is thus also equal to $DN$,"
      (step29 : |(d─b0)| = |(d─n)|) := by euclid_apply (helper_3_8_step29 d k b0 n (by euclid_assumption "$DK$ is equal to $DN$" (show |(d─k)| = |(d─n)|; assumption)) (by euclid_assumption "$DK$ is equal to $DB$" (show |(d─k)| = |(d─b0)|; assumption)))

    euclid_sentence "3.8.30"
      "(so that) a (straight-line) nearer to the least (straight-line) $DG$ [is] equal to one further away."
      (step30 : |(d─b0)| = |(d─n)|) := by euclid_apply (helper_3_8_step30 d b0 n (by euclid_assumption "" (show |(d─b0)| = |(d─n)|; assumption)))

    euclid_sentence "3.8.31"
      "The very thing was shown (to be) impossible."
      (step31 : False) := by euclid_apply (helper_3_8_step31 ABC m k d b0 n g a AG MK (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show b0.onCircle ABC; assumption)) (by euclid_assumption "" (show n.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show |(d─n)| = |(d─k)|; assumption)) (by euclid_assumption "" (show n ≠ k; assumption)) (by euclid_assumption "" (show n ≠ b0; assumption)) (by euclid_assumption "" (show ¬k.onLine AG; assumption)) (by euclid_assumption "" (show ¬b0.onLine AG; assumption)) (by euclid_assumption "" (show ¬b0.sameSide k AG; assumption)) (by euclid_assumption "" (show |(d─b0)| = |(d─n)|; assumption)) (by euclid_assumption "" (show m.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show |(m─g)| = |(m─k)|; assumption)) (by euclid_assumption "" (show |(d─g)| < |(d─k)|; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m ≠ k; assumption)))
    exact step31

  euclid_sentence "3.8.32"
    "Thus, not more than two equal (straight-lines) will radiate towards (the circumference of) circle $ABC$ from point $D$, (one) on each side of the least (straight-line) $DG$."
    (step32 : ¬(∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0)) := by euclid_apply (helper_3_8_step32 ABC k d b0 (by euclid_assumption "" (show ¬∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0; assumption)))

  -- Assemble the three-part goal.
  have huniq : ∀ n : Point, n.onCircle ABC → |(d─n)| = |(d─k)| → n = k ∨ n = b0 := by euclid_apply (helper_3_8_huniq ABC k d b0 (by euclid_assumption "" (show ¬∃ n : Point, n.onCircle ABC ∧ |(d─n)| = |(d─k)| ∧ n ≠ k ∧ n ≠ b0; assumption)))
  exact ⟨⟨step10, step11, step12⟩, ⟨step19, step20, step21⟩, b0, step23.1, step23.2.1, step26.symm, huniq⟩
  euclid_conclude_sentence "3.8.33"
    "Thus, if some point is taken outside a circle, and some straight-lines are drawn from the point to the (circumference of the) circle, one of which (passes) through the center, the remainder (being) random, (then) for the straight-lines radiating towards the concave (part of the) circumference, the greatest is that (passing) through the center. For the others, a (straight-line) nearer to the (straight-line) through the center is always greater than one further away. For the straight-lines radiating towards the convex (part of the) circumference, the least is that between the point and the diameter. For the others, a (straight-line) nearer to the least (straight-line) is always less than one further away. And only two equal (straight-lines) will radiate from the point towards the (circumference of the) circle, (one) on each (side) of the least (straight-line). (Which is) the very thing it was required to show."

end Elements.Book3
