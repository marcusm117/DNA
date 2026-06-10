import SystemE
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1

/-
─────────────────────────────────────────────────────────────────────────────
STATEMENT (Prop 2.4)        faithful statement only.
Convention: "square on XY"            = |XY|·|XY|
            "rectangle contained X,Y" = |X|·|Y|   (length-product)
─────────────────────────────────────────────────────────────────────────────
"If a straight-line is cut at random, (then) the square on the whole
 (straight-line) is equal to the (sum of the) squares on the pieces (of the
 straight-line), and twice the rectangle contained by the pieces."

Setup: straight-line AB cut at random at C (C between A and B).
GOAL : square(AB) = square(AC) + square(CB) + 2·rect(AC,CB)
       |AB|·|AB| = |AC|·|AC| + |CB|·|CB| + 2·(|AC|·|CB|)
-/

-- For let the straight-line $AB$ be cut, at random, at (point) $C$.
-- I say that the square on $AB$ is equal to the (sum of the) squares on $AC$
-- and $CB$, and twice the rectangle contained by $AC$ and $CB$.
theorem proposition_4 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  euclid_intro_sentence "2.4.0"
    "If a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."

  -- Constructions: square ADEB on AB; BD joined; CF through C ∥ AD; G = CF∩BD; HK through G ∥ AB.
  euclid_apply (proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF DE) as f
  euclid_apply (intersection_lines CF BD) as g
  euclid_apply (proposition_31 g a b AB) as HK
  euclid_apply (intersection_lines HK AD) as h
  euclid_apply (intersection_lines HK BE) as k
  euclid_sentence "2.4.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46], and let $BD$ be joined, and let $CF$ be drawn through $C$, parallel to either of $AD$ or $EB$ [Prop.~1.31], and let $HK$ be drawn through $G$, parallel to either of $AB$ or $DE$ [Prop.~1.31]."
    (step1 :
      |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) ∧
      c.onLine CF ∧ ¬(CF.intersectsLine AD) ∧
      g.onLine HK ∧ ¬(HK.intersectsLine AB)) := by sorry

  euclid_sentence "2.4.2"
    "And since $CF$ is parallel to $AD$, and $BD$ has fallen across them, the external angle $CGB$ is equal to the internal and opposite (angle) $ADB$ [Prop.~1.29]."
    (step2 : ∠ c:g:b = ∠ a:d:b) := by sorry

  euclid_sentence "2.4.3"
    "But, $ADB$ is equal to $ABD$, since the side $BA$ is also equal to $AD$ [Prop.~1.5]."
    (step3 : ∠ a:d:b = ∠ a:b:d) := by sorry

  euclid_sentence "2.4.4"
    "Thus, angle $CGB$ is also equal to $GBC$."
    (step4 : ∠ c:g:b = ∠ g:b:c) := by sorry

  euclid_sentence "2.4.5"
    "So the side $BC$ is equal to the side $CG$ [Prop.~1.6]."
    (step5 : |(b─c)| = |(c─g)|) := by sorry

  euclid_sentence "2.4.6"
    "But, $CB$ is equal to $GK$, and $CG$ to $KB$ [Prop.~1.34]."
    (step6 : |(c─b)| = |(g─k)| ∧ |(c─g)| = |(k─b)|) := by sorry

  euclid_sentence "2.4.7"
    "Thus, $GK$ is also equal to $KB$."
    (step7 : |(g─k)| = |(k─b)|) := by sorry

  euclid_sentence "2.4.8"
    "Thus, $CGKB$ is equilateral."
    (step8 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by sorry

  euclid_sentence "2.4.9"
    "So I say that (it is) also right-angled."
    (step9 : True) := by sorry

  euclid_sentence "2.4.10"
    "For since $CG$ is parallel to $BK$ [and the straight-line $CB$ has fallen across them], the angles $KBC$ and $GCB$ are thus equal to two right-angles [Prop.~1.29]."
    (step10 : ∠ k:b:c + ∠ g:c:b = ∟ + ∟) := by sorry

  euclid_sentence "2.4.11"
    "But $KBC$ (is) a right-angle."
    (step11 : ∠ k:b:c = ∟) := by sorry

  euclid_sentence "2.4.12"
    "Thus, $BCG$ (is) also a right-angle."
    (step12 : ∠ b:c:g = ∟) := by sorry

  euclid_sentence "2.4.13"
    "So the opposite (angles) $CGK$ and $GKB$ are also right-angles [Prop.~1.34]."
    (step13 : ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟) := by sorry

  euclid_sentence "2.4.14"
    "Thus, $CGKB$ is right-angled."
    (step14 : ∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟) := by sorry

  euclid_sentence "2.4.15"
    "And it was also shown (to be) equilateral."
    (step15 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by sorry

  euclid_sentence "2.4.16"
    "Thus, it is a square."
    (step16 : (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
              (∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟)) := by sorry

  euclid_sentence "2.4.17"
    "And it is on $CB$."
    (step17 : |(c─b)| = |(b─c)|) := by sorry

  euclid_sentence "2.4.18"
    "So, for the same (reasons), $HF$ is also a square."
    (step18 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
              (∠ d:h:g = ∟ ∧ ∠ h:g:f = ∟ ∧ ∠ g:f:d = ∟ ∧ ∠ f:d:h = ∟)) := by sorry

  euclid_sentence "2.4.19"
    "And it is on $HG$, that is to say [on] $AC$ [Prop.~1.34]."
    (step19 : |(h─g)| = |(a─c)|) := by sorry

  euclid_sentence "2.4.20"
    "Thus, the squares $HF$ and $KC$ are on $AC$ and $CB$ (respectively)."
    (step20 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
              (Triangle.area △ c:b:k + Triangle.area △ c:k:g = |(c─b)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.21"
    "And the (rectangle) $AG$ is equal to the (rectangle) $GE$ [Prop.~1.43]."
    (step21 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
              Triangle.area △ g:k:e + Triangle.area △ g:e:f) := by sorry

  euclid_sentence "2.4.22"
    "And $AG$ is the (rectangle contained) by $AC$ and $CB$. For $GC$ (is) equal to $CB$."
    (step22 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.23"
    "Thus, $GE$ is also equal to the (rectangle contained) by $AC$ and $CB$."
    (step23 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.24"
    "Thus, the (rectangles) $AG$ and $GE$ are equal to twice the (rectangle contained) by $AC$ and $CB$."
    (step24 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
              (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = 2 * (|(a─c)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.25"
    "And $HF$ and $CK$ are the squares on $AC$ and $CB$ (respectively)."
    (step25 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
              (Triangle.area △ c:b:k + Triangle.area △ c:k:g = |(c─b)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.26"
    "Thus, the four (figures) $HF$, $CK$, $AG$, and $GE$ are equal to the (sum of the) squares on $AC$ and $BC$, and twice the rectangle contained by $AC$ and $CB$."
    (step26 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
              (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
              (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
              (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
              |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.27"
    "But, the (figures) $HF$, $CK$, $AG$, and $GE$ are (equivalent to) the whole of $ADEB$, which is the square on $AB$."
    (step27 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
              (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
              (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
              (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "2.4.28"
    "Thus, the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."
    (step28 : |(a─b)| * |(a─b)| =
              |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by sorry

  exact step28
  euclid_conclude_sentence "2.4.29"
    "Thus, if a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. (Which is) the very thing it was required to show."

end Elements.Book2
