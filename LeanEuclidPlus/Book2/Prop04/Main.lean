import SystemE
import Book.Prop31
import Book.Prop46
import Book2.Prop04.step1
import Book2.Prop04.step2
import Book2.Prop04.step3
import Book2.Prop04.step4
import Book2.Prop04.step5
import Book2.Prop04.step6
import Book2.Prop04.step7
import Book2.Prop04.step8
import Book2.Prop04.step9
import Book2.Prop04.step10
import Book2.Prop04.step11
import Book2.Prop04.step12
import Book2.Prop04.step13
import Book2.Prop04.step14
import Book2.Prop04.step15
import Book2.Prop04.step16
import Book2.Prop04.step17
import Book2.Prop04.step18
import Book2.Prop04.step19
import Book2.Prop04.step20
import Book2.Prop04.step21
import Book2.Prop04.step22
import Book2.Prop04.step23
import Book2.Prop04.step24
import Book2.Prop04.step25
import Book2.Prop04.step26
import Book2.Prop04.step27
import Book2.Prop04.step28
import Book2.Prop04.step29
import Book2.Prop04.step30
import Book2.Prop04.step31
import Book2.Prop04.step32
import Book2.Prop04.step33
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

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
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by euclid_apply (helper_2_4_step1 a b d e (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (line_from_points b d) as BD
  euclid_sentence "2.4.2"
    "and let $BD$ be joined,"
    (step2 : distinctPointsOnLine b d BD) := by euclid_apply (helper_2_4_step2 a b d AB AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF BD) as g
  euclid_apply (intersection_lines CF DE) as f
  euclid_sentence "2.4.3"
    "and let $CF$ be drawn through $C$, parallel to either of $AD$ or $EB$ [Prop.~1.31],"
    (step3 : c.onLine CF ∧ ¬(CF.intersectsLine AD)) := by euclid_apply (helper_2_4_step3 c CF AD (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (Elements.Book1.proposition_31 g a b AB) as HK
  euclid_apply (intersection_lines HK AD) as h
  euclid_apply (intersection_lines HK BE) as k
  euclid_sentence "2.4.4"
    "and let $HK$ be drawn through $G$, parallel to either of $AB$ or $DE$ [Prop.~1.31]."
    (step4 : g.onLine HK ∧ ¬(HK.intersectsLine AB)) := by euclid_apply (helper_2_4_step4 g HK AB (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.5"
    "And since $CF$ is parallel to $AD$, and $BD$ has fallen across them, the external angle $CGB$ is equal to the internal and opposite (angle) $ADB$ [Prop.~1.29]."
    (step5 : ∠ c:g:b = ∠ a:d:b) := by euclid_apply (helper_2_4_step5 a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.6"
    "But, $ADB$ is equal to $ABD$, since the side $BA$ is also equal to $AD$ [Prop.~1.5]."
    (step6 : ∠ a:d:b = ∠ a:b:d) := by euclid_apply (helper_2_4_step6 a b d AB AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.7"
    "Thus, angle $CGB$ is also equal to $GBC$."
    (step7 : ∠ c:g:b = ∠ g:b:c) := by euclid_apply (helper_2_4_step7 a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.8"
    "So the side $BC$ is equal to the side $CG$ [Prop.~1.6]."
    (step8 : |(b─c)| = |(c─g)|) := by euclid_apply (helper_2_4_step8 a b c d g h AB CF AD BD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.9"
    "But, $CB$ is equal to $GK$,"
    (step9 : |(c─b)| = |(g─k)|) := by euclid_apply (helper_2_4_step9 a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.10"
    "and $CG$ to $KB$ [Prop.~1.34]."
    (step10 : |(c─g)| = |(k─b)|) := by euclid_apply (helper_2_4_step10 a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.11"
    "Thus, $GK$ is also equal to $KB$."
    (step11 : |(g─k)| = |(k─b)|) := by euclid_apply (helper_2_4_step11 b c g k (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.12"
    "Thus, $CGKB$ is equilateral."
    (step12 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by euclid_apply (helper_2_4_step12 b c g k (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.13"
    "So I say that (it is) also right-angled."
    (step13 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by euclid_apply (helper_2_4_step13 a b c d e g k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.14"
    "For since $CG$ is parallel to $BK$ [and the straight-line $CB$ has fallen across them], the angles $KBC$ and $GCB$ are thus equal to two right-angles [Prop.~1.29]."
    (step14 : ∠ k:b:c + ∠ g:c:b = ∟ + ∟) := by euclid_apply (helper_2_4_step14 a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.15"
    "But $KBC$ (is) a right-angle."
    (step15 : ∠ k:b:c = ∟) := by euclid_apply (helper_2_4_step15 a b c d e g k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.16"
    "Thus, $BCG$ (is) also a right-angle."
    (step16 : ∠ b:c:g = ∟) := by euclid_apply (helper_2_4_step16 a b c g k (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.17"
    "So the opposite (angles) $CGK$ and $GKB$ are also right-angles [Prop.~1.34]."
    (step17 : (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by euclid_apply (helper_2_4_step17 a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.18"
    "Thus, $CGKB$ is right-angled."
    (step18 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) := by euclid_apply (helper_2_4_step18 b c g k (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.19"
    "And it was also shown (to be) equilateral."
    (step19 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) := by euclid_apply (helper_2_4_step19 b c g k (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.20"
    "Thus, it is a square."
    (step20 : (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
      ((∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟))) := by euclid_apply (helper_2_4_step20 b c g k (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.21"
    "And it is on $CB$."
    (step21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by euclid_apply (helper_2_4_step21 a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.22"
    "So, for the same (reasons), $HF$ is also a square."
    (step22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟))) := by euclid_apply (helper_2_4_step22 a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.23"
    "And it is on $HG$, that is to say [on] $AC$ [Prop.~1.34]."
    (step23 : |(h─g)| = |(a─c)|) := by euclid_apply (helper_2_4_step23 a b c d g h AB CF AD BD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.24"
    "Thus, the squares $HF$ and $KC$ are on $AC$ and $CB$ (respectively)."
    (step24 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by euclid_apply (helper_2_4_step24 a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.25"
    "And the (rectangle) $AG$ is equal to the (rectangle) $GE$ [Prop.~1.43]."
    (step25 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ g:k:e + Triangle.area △ g:e:f) := by euclid_apply (helper_2_4_step25 a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.26"
    "And $AG$ is the (rectangle contained) by $AC$ and $CB$. For $GC$ (is) equal to $CB$."
    (step26 : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)|) := by euclid_apply (helper_2_4_step26 a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.27"
    "Thus, $GE$ is also equal to the (rectangle contained) by $AC$ and $CB$."
    (step27 : Triangle.area △ g:k:e + Triangle.area △ g:e:f = |(a─c)| * |(c─b)|) := by euclid_apply (helper_2_4_step27 a b c e f g h k (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.28"
    "Thus, the (rectangles) $AG$ and $GE$ are equal to twice the (rectangle contained) by $AC$ and $CB$."
    (step28 : (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
      (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(c─b)| + |(a─c)| * |(c─b)|) := by euclid_apply (helper_2_4_step28 a b c e f g h k (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.29"
    "And $HF$ and $CK$ are the squares on $AC$ and $CB$ (respectively)."
    (step29 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)) := by euclid_apply (helper_2_4_step29 a b c d f g h k (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.30"
    "Thus, the four (figures) $HF$, $CK$, $AG$, and $GE$ are equal to the (sum of the) squares on $AC$ and $BC$, and twice the rectangle contained by $AC$ and $CB$."
    (step30 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by euclid_apply (helper_2_4_step30 a b c d e f g h k (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.31"
    "But, the (figures) $HF$, $CK$, $AG$, and $GE$ are (equivalent to) the whole of $ADEB$,"
    (step31 : (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b) := by euclid_apply (helper_2_4_step31 a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.32"
    "which is the square on $AB$."
    (step32 : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_4_step32 a b d e BE AD AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.4.33"
    "Thus, the square on $AB$ is equal to the (sum of the) squares on $AC$ and $CB$, and twice the rectangle contained by $AC$ and $CB$."
    (step33 : |(a─b)| * |(a─b)| =
      |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|)) := by euclid_apply (helper_2_4_step33 a b c d e f g h k (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  exact step33
  euclid_conclude_sentence "2.4.34"
    "Thus, if a straight-line is cut at random, (then) the square on the whole (straight-line) is equal to the (sum of the) squares on the pieces (of the straight-line), and twice the rectangle contained by the pieces. (Which is) the very thing it was required to show."

end Elements.Book2
