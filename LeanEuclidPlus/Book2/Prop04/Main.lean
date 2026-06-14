import SystemE
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_4 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  euclid_intro_sentence "2.4.0"
    "If a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."

  euclid_apply (Elements.Book1.proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_sentence "2.4.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46],"
    (step1 : |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by sorry

  euclid_apply (line_from_points b d) as BD
  euclid_sentence "2.4.2"
    "and let $BD$ be joined,"
    (step2 : distinctPointsOnLine b d BD) := by sorry

  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF BD) as g
  euclid_apply (intersection_lines CF DE) as f
  euclid_sentence "2.4.3"
    "and let $CF$ be drawn through $C$, parallel to either of $AD$ or $EB$ [Prop.~1.31],"
    (step3 : c.onLine CF ∧ ¬(CF.intersectsLine AD)) := by sorry

  euclid_apply (Elements.Book1.proposition_31 g a b AB) as HK
  euclid_apply (intersection_lines HK AD) as h
  euclid_apply (intersection_lines HK BE) as k
  euclid_sentence "2.4.4"
    "and let $HK$ be drawn through $G$, parallel to either of $AB$ or $DE$ [Prop.~1.31]."
    (step4 : g.onLine HK ∧ ¬(HK.intersectsLine AB)) := by sorry

  euclid_sentence "2.4.5"
    "And since $CF$ is parallel to $AD$, and $BD$ has fallen across them, the external angle $CGB$ is equal to the internal and opposite (angle) $ADB$ [Prop.~1.29]."
    (step5 : ∠ c:g:b = ∠ a:d:b) := by sorry

  euclid_sentence "2.4.6"
    "But, $ADB$ is equal to $ABD$, since the side $BA$ is also equal to $AD$ [Prop.~1.5]."
    (step6 : ∠ a:d:b = ∠ a:b:d) := by sorry

  euclid_sentence "2.4.7"
    "Thus, angle $CGB$ is also equal to $GBC$."
    (step7 : ∠ c:g:b = ∠ g:b:c) := by sorry

  euclid_sentence "2.4.8"
    "So the side $BC$ is equal to the side $CG$ [Prop.~1.6]."
    (step8 : |(b─c)| = |(c─g)|) := by sorry

  euclid_sentence "2.4.9"
    "But, $CB$ is equal to $GK$,"
    (step9 : |(c─b)| = |(g─k)|) := by sorry

  euclid_sentence "2.4.10"
    "and $CG$ to $KB$ [Prop.~1.34]."
    (step10 : |(c─g)| = |(k─b)|) := by sorry

  euclid_sentence "2.4.11"
    "Thus, $GK$ is also equal to $KB$."
    (step11 : |(g─k)| = |(k─b)|) := by sorry

  euclid_sentence "2.4.12"
    "Thus, $CGKB$ is equilateral."
    (step12 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by sorry

  euclid_sentence "2.4.13"
    "So I say that (it is) also right-angled."
    (step13 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by sorry

  euclid_sentence "2.4.14"
    "For since $CG$ is parallel to $BK$ [and the straight-line $CB$ has fallen across them], the angles $KBC$ and $GCB$ are thus equal to two right-angles [Prop.~1.29]."
    (step14 : ∠ k:b:c + ∠ g:c:b = ∟ + ∟) := by sorry

  euclid_sentence "2.4.15"
    "But $KBC$ (is) a right-angle."
    (step15 : ∠ k:b:c = ∟) := by sorry

  euclid_sentence "2.4.16"
    "Thus, $BCG$ (is) also a right-angle."
    (step16 : ∠ b:c:g = ∟) := by sorry

  euclid_sentence "2.4.17"
    "So the opposite (angles) $CGK$ and $GKB$ are also right-angles [Prop.~1.34]."
    (step17 : (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by sorry

  euclid_sentence "2.4.18"
    "Thus, $CGKB$ is right-angled."
    (step18 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by sorry

  euclid_sentence "2.4.19"
    "And it was also shown (to be) equilateral."
    (step19 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by sorry

  euclid_sentence "2.4.20"
    "Thus, it is a square."
    (step20 : (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
      ((∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟))) := by sorry

  euclid_sentence "2.4.21"
    "And it is on $CB$."
    (step21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.22"
    "So, for the same (reasons), $HF$ is also a square."
    (step22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟))) := by sorry

  euclid_sentence "2.4.23"
    "And it is on $HG$, that is to say [on] $AC$ [Prop.~1.34]."
    (step23 : |(h─g)| = |(a─c)|) := by sorry

  euclid_sentence "2.4.24"
    "Thus, the squares $HF$ and $KC$ are on $AC$ and $CB$ (respectively)."
    (step24 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.25"
    "And the (rectangle) $AG$ is equal to the (rectangle) $GE$ [Prop.~1.43]."
    (step25 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ g:k:e + Triangle.area △ g:e:f) := by sorry

  euclid_sentence "2.4.26"
    "And $AG$ is the (rectangle contained) by $AC$ and $CB$. For $GC$ (is) equal to $CB$."
    (step26 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.27"
    "Thus, $GE$ is also equal to the (rectangle contained) by $AC$ and $CB$."
    (step27 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.28"
    "Thus, the (rectangles) $AG$ and $GE$ are equal to twice the (rectangle contained) by $AC$ and $CB$."
    (step28 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
      (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(c─b)| + |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.4.29"
    "And $HF$ and $CK$ are the squares on $AC$ and $CB$ (respectively)."
    (step29 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.30"
    "Thus, the four (figures) $HF$, $CK$, $AG$, and $GE$ are equal to the (sum of the) squares on $AC$ and $BC$, and twice the rectangle contained by $AC$ and $CB$."
    (step30 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by sorry

  euclid_sentence "2.4.31"
    "But, the (figures) $HF$, $CK$, $AG$, and $GE$ are (equivalent to) the whole of $ADEB$,"
    (step31 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b) := by sorry

  euclid_sentence "2.4.32"
    "which is the square on $AB$."
    (step32 : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "2.4.33"
    "Thus, the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."
    (step33 : |(a─b)| * |(a─b)| =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by sorry

  exact step33
  euclid_conclude_sentence "2.4.34"
    "Thus, if a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. (Which is) the very thing it was required to show."

end Elements.Book2
