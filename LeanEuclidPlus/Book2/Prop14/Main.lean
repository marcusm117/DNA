import SystemE
import Book.Prop03
import Book.Prop10
import Book.Prop11
import Book.Prop45
import Book2.Prop05.Main
import Book2.Prop14.step1
import Book2.Prop14.step2
import Book2.Prop14.step3
import Book2.Prop14.step4
import Book2.Prop14.step5
import Book2.Prop14.step6
import Book2.Prop14.step7
import Book2.Prop14.step8
import Book2.Prop14.step9
import Book2.Prop14.step10
import Book2.Prop14.step11
import Book2.Prop14.step12
import Book2.Prop14.step13
import Book2.Prop14.step14
import Book2.Prop14.step15
import Book2.Prop14.step16
import Book2.Prop14.step17
import Book2.Prop14.step18
import Book2.Prop14.step19
import Book2.Prop14.step20
import Book2.Prop14.step21
import Book2.Prop14.fp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/-!
Prop 2.14 — quadrature: "To construct a square equal to a given rectilinear figure A."

Modeling: System E has no general rectilinear-figure type; area is `Triangle.area` and a polygon is a
sum of triangle areas (as Prop 1.45 does). Euclid's text cites **[Prop. 1.45]** ("construct a
parallelogram equal to a given rectilinear figure"), so the given figure A is modeled as a
QUADRILATERAL `a b c q` (the smallest figure to which 1.45 genuinely applies), with diagonal `QB`
splitting it into triangles `a:b:q` and `q:b:c`; its area is `△ a:b:q + △ q:b:c`. Step 1 builds the
right-angled parallelogram BD via **Prop 1.45**. Rectangle corners: `b₀ = B`, `e = E`, `d = D`,
`c₀ = C` (right angle at `b₀`); `b₀, c₀` are subscripted to avoid clashing with `a b c`, and A's 4th
vertex is `q` (not `d`) to avoid clashing with the rectangle's `d = D`.

Structure note: the geometric-mean construction works whether BE = ED or not (it always produces
`h` with `|e─h|² = |b₀─e|·|e─f|`), so it is built UNCONDITIONALLY and the witness is always `(e, h)`.
Euclid's "if BE = ED then BD is a square" case discussion (steps 2/3) and the trichotomy (step 4)
are recorded as a nested `by_cases` inside `have hcase` (like Book1/Prop06's `have habsurd`) —
NOT as `→` claims, and with no heavy construction inside the case branches.
-/

theorem proposition_14 : ∀ (a b c q : Point) (AB BC CQ AQ QB : Line),
  formTriangle a b q AB QB AQ ∧ formTriangle b c q BC CQ QB ∧ a.opposingSides c QB →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c := by
  euclid_intros
  euclid_intro_sentence "2.14.0"
    "To construct a square equal to a given rectilinear figure. Let $A$ be the given rectilinear figure. So it is required to construct a square equal to the rectilinear figure $A$."

  -- Construct a right-angled parallelogram (rectangle) BD equal to the rectilinear figure A.
  euclid_apply (Elements.Book1.proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  euclid_apply (Elements.Book1.proposition_45 a b c q p a b AB BC CQ AQ QB AP AB) as (e, d, b₀, c₀, ED, B₀C₀, BE, DC)
  have fp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC := by euclid_apply (helper_2_14_fp e d b₀ c₀ ED B₀C₀ BE DC (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show c₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c₀.onLine DC; assumption)) (by euclid_assumption "" (show d ≠ c₀; assumption)) (by euclid_assumption "" (show e.sameSide b₀ DC; assumption)) (by euclid_assumption "" (show ¬ED.intersectsLine B₀C₀; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine DC; assumption)))
  euclid_sentence "2.14.1"
    "For let the right-angled parallelogram $BD$, equal to the rectilinear figure $A$, be constructed [Prop. 1.45]."
    (step1 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟) := by euclid_apply (helper_2_14_step1 a b c q e d b₀ c₀ p ED B₀C₀ BE DC (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show c₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c₀.onLine DC; assumption)) (by euclid_assumption "" (show d ≠ c₀; assumption)) (by euclid_assumption "" (show e.sameSide b₀ DC; assumption)) (by euclid_assumption "" (show ¬ED.intersectsLine B₀C₀; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine DC; assumption)) (by euclid_assumption "" (show ∠ e:b₀:c₀ = ∠ p:a:b; assumption)) (by euclid_assumption "" (show ∠ p:a:b = ∟; assumption)) (by euclid_assumption "" (show Triangle.area △e:b₀:c₀ + Triangle.area △e:d:c₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c; assumption)))

  -- Euclid's case discussion (steps 2/3/4): if BE = ED, BD is already a square; else one is greater.
  -- Nested in `have hcase` (Prop06-style); the construction itself is unconditional (below).
  have hcase : True := by
    by_cases heq : |(b₀─e)| = |(e─d)|
    -- Case BE = ED: BD is a square on BE.
    · euclid_sentence "2.14.2"
        "Therefore, if $BE$ is equal to $ED$ then that (which) was prescribed has taken place."
        (step2 : |(b₀─e)| * |(b₀─e)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by euclid_apply (helper_2_14_step2 a b c q e d b₀ c₀ ED B₀C₀ BE DC (by euclid_assumption "" (show formParallelogram e d b₀ c₀ ED B₀C₀ BE DC; assumption)) (by euclid_assumption "" (show Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟; assumption)) (by euclid_assumption "" (show |(b₀─e)| = |(e─d)|; assumption)))
      euclid_sentence "2.14.3"
        "For the square $BD$, equal to the rectilinear figure $A$, has been constructed."
        (step3 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(b₀─e)| * |(b₀─e)|) := by euclid_apply (helper_2_14_step3 a b c q e d b₀ c₀ ED B₀C₀ BE DC (by euclid_assumption "" (show formParallelogram e d b₀ c₀ ED B₀C₀ BE DC; assumption)) (by euclid_assumption "" (show Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟; assumption)) (by euclid_assumption "" (show |(b₀─e)| = |(e─d)|; assumption)))
      trivial
    -- Case BE ≠ ED: one of BE, ED is greater.
    · euclid_sentence "2.14.4"
        "And if not, (then) one of the (straight-lines) $BE$ or $ED$ is greater (than the other)."
        (step4 : |(b₀─e)| > |(e─d)| ∨ |(e─d)| > |(b₀─e)|) := by euclid_apply (helper_2_14_step4 b₀ e d (by euclid_assumption "" (show |(b₀─e)| ≠ |(e─d)|; assumption)))
      trivial

  -- The geometric-mean construction (unconditional). Produce BE beyond E, make EF = ED (Prop 1.3).
  euclid_apply (extend_point_longer BE b₀ e (e─d)) as ffar
  euclid_apply (Elements.Book1.proposition_3 e ffar e d BE ED) as f
  euclid_sentence "2.14.5"
    "Let $BE$ be greater, and let it be produced to $F$,"
    (step5 : between b₀ e f ∧ f.onLine BE) := by euclid_apply (helper_2_14_step5 b₀ e f ffar BE (by euclid_assumption "" (show between b₀ e ffar; assumption)) (by euclid_assumption "" (show ffar.onLine BE; assumption)) (by euclid_assumption "" (show between e f ffar; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)))
  euclid_sentence "2.14.6"
    "and let $EF$ be made equal to $ED$ [Prop.~1.3]."
    (step6 : |(e─f)| = |(e─d)|) := by euclid_apply (helper_2_14_step6 e f d (by euclid_assumption "" (show |(e─f)| = |(e─d)|; assumption)))
  -- Bisect BF at G (Prop 1.10).
  euclid_apply (Elements.Book1.proposition_10 b₀ f BE) as g
  euclid_sentence "2.14.7"
    "And let $BF$ be cut in half at (point) $G$ [Prop.~1.10]."
    (step7 : between b₀ g f ∧ |(b₀─g)| = |(g─f)|) := by euclid_apply (helper_2_14_step7 b₀ g f (by euclid_assumption "" (show between b₀ g f; assumption)) (by euclid_assumption "" (show |(b₀─g)| = |(g─f)|; assumption)))
  -- Draw the semicircle BHF on BF (centre G); produce DE to meet it at H.
  euclid_apply (circle_from_points g b₀) as BHF
  euclid_apply (point_on_circle_if g b₀ f BHF)
  euclid_apply (circle_points_between b₀ f e BHF)
  -- "DE produced to H beyond E": pick the intersection on the FAR side of e from d
  -- (gives `between h e d`), so H is the faithful produced point — not an arbitrary intersection.
  euclid_apply (intersection_circle_line_extending_points BHF ED e d) as h
  euclid_apply (point_on_circle_onlyif g b₀ h BHF)
  euclid_sentence "2.14.8"
    "And, with center $G$, and radius one of the (straight-lines) $GB$ or $GF$, let the semi-circle $BHF$ be drawn."
    (step8 : |(g─h)| = |(g─b₀)|) := by euclid_apply (helper_2_14_step8 g h b₀ (by euclid_assumption "" (show |(g─h)| = |(g─b₀)|; assumption)))
  euclid_sentence "2.14.9"
    "And let $DE$ be produced to $H$,"
    (step9 : h.onLine ED ∧ ¬(between e h d)) := by euclid_apply (helper_2_14_step9 h e d ED (by euclid_assumption "" (show h.onLine ED; assumption)) (by euclid_assumption "" (show between h e d; assumption)))
  euclid_apply (line_from_points g h) as GH
  euclid_sentence "2.14.10"
    "and let $GH$ be joined."
    (step10 : distinctPointsOnLine g h GH) := by euclid_apply (helper_2_14_step10 g h b₀ f GH (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show |(g─h)| = |(g─b₀)|; assumption)) (by euclid_assumption "" (show between b₀ g f; assumption)))
  -- @assumption ("the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$", |(b₀─g)| = |(g─f)| ∧ between b₀ e f)
  euclid_sentence "2.14.11"
    "Therefore, since the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$---the rectangle contained by $BE$ and $EF$, plus the square on $EG$, is thus equal to the square on $GF$ [Prop.~2.5]."
    (step11 : |(b₀─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|) := by euclid_apply (helper_2_14_step11 b₀ e f g BE (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show between b₀ e f; assumption)) (by euclid_assumption "" (show between b₀ g f; assumption)) (by euclid_assumption "" (show |(b₀─g)| = |(g─f)|; assumption)))
  euclid_sentence "2.14.12"
    "And $GF$ (is) equal to $GH$."
    (step12 : |(g─f)| = |(g─h)|) := by euclid_apply (helper_2_14_step12 g f h b₀ (by euclid_assumption "" (show |(b₀─g)| = |(g─f)|; assumption)) (by euclid_assumption "" (show |(g─h)| = |(g─b₀)|; assumption)))
  euclid_sentence "2.14.13"
    "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (square) on $GH$."
    (step13 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)|) := by euclid_apply (helper_2_14_step13 b₀ e f g h (by euclid_assumption "" (show |(b₀─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|; assumption)) (by euclid_assumption "" (show |(g─f)| = |(g─h)|; assumption)))
  euclid_sentence "2.14.14"
    "And the (sum of the) squares on $HE$ and $EG$ is equal to the (square) on $GH$ [Prop.~1.47]."
    (step14 : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)|) := by euclid_apply (helper_2_14_step14 e d b₀ c₀ g h f ED B₀C₀ BE DC GH (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show h.onLine ED; assumption)) (by euclid_assumption "" (show b₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show c₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c₀.onLine DC; assumption)) (by euclid_assumption "" (show ∠ c₀:b₀:e = ∟; assumption)) (by euclid_assumption "" (show ¬ED.intersectsLine B₀C₀; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine DC; assumption)) (by euclid_assumption "" (show e.sameSide b₀ DC; assumption)) (by euclid_assumption "" (show between h e d; assumption)) (by euclid_assumption "" (show between b₀ e f; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show between b₀ g f; assumption)))
  euclid_sentence "2.14.15"
    "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (sum of the squares) on $HE$ and $EG$."
    (step15 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)|) := by euclid_apply (helper_2_14_step15 b₀ e f g h (by euclid_assumption "" (show |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)|; assumption)) (by euclid_assumption "" (show |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)|; assumption)))
  euclid_sentence "2.14.16"
    "Let the square on $GE$ be taken from both."
    (step16 : |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|) := by euclid_apply (helper_2_14_step16 b₀ e f g h (by euclid_assumption "" (show |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)|; assumption)))
  euclid_sentence "2.14.17"
    "Thus, the remaining rectangle contained by $BE$ and $EF$ is equal to the square on $EH$."
    (step17 : |(b₀─e)| * |(e─f)| = |(e─h)| * |(e─h)|) := by euclid_apply (helper_2_14_step17 b₀ e f h (by euclid_assumption "" (show |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|; assumption)))
  -- @assumption ("$EF$ (is) equal to $ED$", |(e─f)| = |(e─d)|)
  euclid_sentence "2.14.18"
    "But, $BD$ is the (rectangle contained) by $BE$ and $EF$. For $EF$ (is) equal to $ED$."
    (step18 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(b₀─e)| * |(e─f)|) := by euclid_apply (helper_2_14_step18 e d b₀ c₀ f ED B₀C₀ BE DC (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show c₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c₀.onLine DC; assumption)) (by euclid_assumption "" (show d ≠ c₀; assumption)) (by euclid_assumption "" (show e.sameSide b₀ DC; assumption)) (by euclid_assumption "" (show ¬ED.intersectsLine B₀C₀; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine DC; assumption)) (by euclid_assumption "" (show ∠ c₀:b₀:e = ∟; assumption)) (by euclid_assumption "$EF$ (is) equal to $ED$" (show |(e─f)| = |(e─d)|; assumption)))
  euclid_sentence "2.14.19"
    "Thus, the parallelogram $BD$ is equal to the square on $HE$."
    (step19 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(h─e)| * |(h─e)|) := by euclid_apply (helper_2_14_step19 b₀ e d c₀ f h (by euclid_assumption "" (show (△ b₀:e:d).area + (△ b₀:c₀:d).area = |(b₀─e)| * |(e─f)|; assumption)) (by euclid_assumption "" (show |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|; assumption)))
  euclid_sentence "2.14.20"
    "And $BD$ (is) equal to the rectilinear figure $A$."
    (step20 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by euclid_apply (helper_2_14_step20 a b c q b₀ e d c₀ (by euclid_assumption "" (show Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c; assumption)))
  euclid_sentence "2.14.21"
    "Thus, the rectilinear figure $A$ is also equal to the square (which) can be described on $EH$."
    (step21 : |(e─h)| * |(e─h)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by euclid_apply (helper_2_14_step21 a b c q b₀ e d c₀ h (by euclid_assumption "" (show Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(h─e)| * |(h─e)|; assumption)) (by euclid_assumption "" (show Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c; assumption)))

  -- The witness: the segment e─h (whose square is the area, step 21).
  exact ⟨e, h, step21⟩
  euclid_conclude_sentence "2.14.22"
    "Thus, a square---(namely), that (which) can be described on $EH$---has been constructed, equal to the given rectilinear figure $A$. (Which is) the very thing it was required to do."

end Elements.Book2
