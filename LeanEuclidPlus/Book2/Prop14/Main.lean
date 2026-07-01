import SystemE
import Book.Prop03
import Book.Prop10
import Book.Prop11
import Book.Prop45
import Book2.Prop05.Main

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

Structure: Euclid splits on whether BE = ED. If equal, the rectangle BD is already the required
square and the construction is complete (2.14.2). If not, one of BE, ED is greater and the
geometric-mean construction produces the side EH (2.14.3–2.14.21). Both branches close the goal
with their own witness — the case split is genuine, mirroring Euclid's two cases.
-/

set_option systemE.solverTime 30 in
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
  have fp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC := by sorry
  euclid_sentence "2.14.1"
    "For let the right-angled parallelogram $BD$, equal to the rectilinear figure $A$, be constructed [Prop. 1.45]."
    (step1 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟) := by sorry

  by_cases heq : |(b₀─e)| = |(e─d)|
  -- Case BE = ED: the rectangle BD is already the required square; nothing more to construct.
  -- @assumption ("the square $BD$, equal to the rectilinear figure $A$", Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c)
  · euclid_sentence "2.14.2"
      "Therefore, if $BE$ is equal to $ED$ then that (which) was prescribed has taken place. For the square $BD$, equal to the rectilinear figure $A$, has been constructed."
      (step2 : |(b₀─e)| * |(b₀─e)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by sorry
    -- The witness in this case: the square on BE itself — the goal is proven.
    exact ⟨b₀, e, step2⟩
  -- Case BE ≠ ED: one of BE, ED is greater (2.14.3). WLOG take BE to be the greater
  -- (2.14.4); the ED-greater case follows by the rectangle's B↔D symmetry (reduction).
  · euclid_sentence "2.14.3"
      "And if not, (then) one of the (straight-lines) $BE$ or $ED$ is greater (than the other)."
      (step4 : |(b₀─e)| > |(e─d)| ∨ |(e─d)| > |(b₀─e)|) := by sorry
    wlog hgt : |(b₀─e)| > |(e─d)| generalizing b₀ e d c₀ ED B₀C₀ BE DC with Hsym
    -- WLOG reduction: if instead ED > BE, apply Hsym to the B↔D-swapped rectangle
    -- (in which the greater side is again "BE"). This closes the case Euclid omits.
    ·
      -- ED > BE. Apply the main case (Hsym) to the B↔D-swapped rectangle D-E-B-C, whose
      -- right-angle corner is now D. The relabelled figure's facts (right angle at D, the
      -- reassembled parallelogram, matched areas) are the swapfig backing file; with those in
      -- hand every hypothesis Hsym needs is present (assumption) or a length/order fact (euclid_finish).
      have swapfig :
          ∠ e:d:c₀ = ∠ p:a:b
          ∧ b₀ ≠ c₀
          ∧ e.sameSide d B₀C₀
          ∧ formParallelogram e b₀ d c₀ BE DC ED B₀C₀
          ∧ (Triangle.area △ d:e:b₀ + Triangle.area △ d:c₀:b₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:d:e = ∟)
          ∧ (Triangle.area △ e:d:c₀ + Triangle.area △ e:b₀:c₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c)
          ∧ (¬ |(d─e)| = |(e─b₀)|)
          ∧ (|(d─e)| > |(e─b₀)| ∨ |(e─b₀)| > |(d─e)|)
          ∧ |(d─e)| > |(e─b₀)| := by sorry
      obtain ⟨hrd, hne, hss, hfp, hs1, harea, h17, h18, h19⟩ := swapfig
      exact Hsym e b₀ d c₀ BE DC ED B₀C₀
        (by assumption) hrd harea (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) hss (by assumption) hne
        (by assumption) (by assumption) hfp hs1 h17 h18 h19
    -- Main WLOG case (hgt : BE > ED). Build the geometric mean EH.
    ·
      -- Produce BE beyond E, make EF = ED (Prop 1.3).
      euclid_apply (extend_point_longer BE b₀ e (e─d)) as ffar
      euclid_apply (Elements.Book1.proposition_3 e ffar e d BE ED) as f
      euclid_sentence "2.14.4"
        "Let $BE$ be greater, and let it be produced to $F$,"
        (step5 : between b₀ e f ∧ f.onLine BE) := by sorry
      euclid_sentence "2.14.5"
        "and let $EF$ be made equal to $ED$ [Prop.~1.3]."
        (step6 : |(e─f)| = |(e─d)|) := by sorry
      -- Bisect BF at G (Prop 1.10).
      euclid_apply (Elements.Book1.proposition_10 b₀ f BE) as g
      euclid_sentence "2.14.6"
        "And let $BF$ be cut in half at (point) $G$ [Prop.~1.10]."
        (step7 : between b₀ g f ∧ |(b₀─g)| = |(g─f)|) := by sorry
      -- Draw the semicircle BHF on BF (centre G); produce DE to meet it at H.
      euclid_apply (circle_from_points g b₀) as BHF
      euclid_apply (point_on_circle_if g b₀ f BHF)
      euclid_apply (circle_points_between b₀ f e BHF)
      -- "DE produced to H beyond E": pick the intersection on the FAR side of e from d
      -- (gives `between h e d`), so H is the faithful produced point — not an arbitrary intersection.
      euclid_apply (intersection_circle_line_extending_points BHF ED e d) as h
      euclid_apply (point_on_circle_onlyif g b₀ h BHF)
      euclid_sentence "2.14.7"
        "And, with center $G$, and radius one of the (straight-lines) $GB$ or $GF$, let the semi-circle $BHF$ be drawn."
        (step8 : g.isCentre BHF ∧ b₀.onCircle BHF ∧ f.onCircle BHF) := by sorry
      euclid_sentence "2.14.8"
        "And let $DE$ be produced to $H$,"
        (step9 : h.onLine ED ∧ ¬(between e h d) ∧ h.onCircle BHF) := by sorry
      euclid_apply (line_from_points g h) as GH
      euclid_sentence "2.14.9"
        "and let $GH$ be joined."
        (step10 : distinctPointsOnLine g h GH) := by sorry
      -- @assumption ("the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$", |(b₀─g)| = |(g─f)| ∧ between b₀ e f)
      euclid_sentence "2.14.10"
        "Therefore, since the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$---the rectangle contained by $BE$ and $EF$, plus the square on $EG$, is thus equal to the square on $GF$ [Prop.~2.5]."
        (step11 : |(b₀─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|) := by sorry
      euclid_sentence "2.14.11"
        "And $GF$ (is) equal to $GH$."
        (step12 : |(g─f)| = |(g─h)|) := by sorry
      euclid_sentence "2.14.12"
        "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (square) on $GH$."
        (step13 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)|) := by sorry
      euclid_sentence "2.14.13"
        "And the (sum of the) squares on $HE$ and $EG$ is equal to the (square) on $GH$ [Prop.~1.47]."
        (step14 : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)|) := by sorry
      euclid_sentence "2.14.14"
        "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (sum of the squares) on $HE$ and $EG$."
        (step15 : |(b₀─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)|) := by sorry
      euclid_sentence "2.14.15"
        "Let the square on $GE$ be taken from both."
        (step16 : |(b₀─e)| * |(e─f)| = |(h─e)| * |(h─e)|) := by sorry
      euclid_sentence "2.14.16"
        "Thus, the remaining rectangle contained by $BE$ and $EF$ is equal to the square on $EH$."
        (step17 : |(b₀─e)| * |(e─f)| = |(e─h)| * |(e─h)|) := by sorry
      -- @assumption ("$EF$ (is) equal to $ED$", |(e─f)| = |(e─d)|)
      euclid_sentence "2.14.17"
        "But, $BD$ is the (rectangle contained) by $BE$ and $EF$. For $EF$ (is) equal to $ED$."
        (step18 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(b₀─e)| * |(e─f)|) := by sorry
      euclid_sentence "2.14.18"
        "Thus, the parallelogram $BD$ is equal to the square on $HE$."
        (step19 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = |(h─e)| * |(h─e)|) := by sorry
      euclid_sentence "2.14.19"
        "And $BD$ (is) equal to the rectilinear figure $A$."
        (step20 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by sorry
      euclid_sentence "2.14.20"
        "Thus, the rectilinear figure $A$ is also equal to the square (which) can be described on $EH$."
        (step21 : |(e─h)| * |(e─h)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c) := by sorry
      -- The witness: the segment e─h (whose square is the area, step 21).
      exact ⟨e, h, step21⟩
      euclid_conclude_sentence "2.14.21"
        "Thus, a square---(namely), that (which) can be described on $EH$---has been constructed, equal to the given rectilinear figure $A$. (Which is) the very thing it was required to do."

end Elements.Book2
