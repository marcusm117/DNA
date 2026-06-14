import SystemE
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_6 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between a b d →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  euclid_intro_sentence "2.6.0"
    "If a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having being added, and the (straight-line) having being added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added. For let any straight-line $AB$ be cut in half at point $C$, and let any straight-line $BD$ be added to it straight-on. I say that the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the square on $CD$."

  euclid_apply (Elements.Book1.proposition_46 c d AB) as (e, f, EF, CE, DF)
  euclid_sentence "2.6.1"
    "For let the square $CEFD$ be described on $CD$ [Prop.~1.46],"
    (step1 : |(c─e)| = |(c─d)| ∧ |(d─f)| = |(c─d)| ∧ |(e─f)| = |(c─d)| ∧
      (∠ d:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:d:f = ∟) ∧ (∠ d:f:e = ∟)) := by sorry

  euclid_apply (line_from_points d e) as DE
  euclid_sentence "2.6.2"
    "and let $DE$ be joined,"
    (step2 : distinctPointsOnLine d e DE) := by sorry

  euclid_apply (Elements.Book1.proposition_31 b c e CE) as BG
  euclid_apply (intersection_lines BG EF) as g
  euclid_apply (intersection_lines BG DE) as h
  euclid_sentence "2.6.3"
    "and let $BG$ be drawn through point $B$, parallel to either of $EC$ or $DF$ [Prop.~1.31],"
    (step3 : b.onLine BG ∧ ¬(BG.intersectsLine CE)) := by sorry

  euclid_apply (Elements.Book1.proposition_31 h a b AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM DF) as m
  euclid_sentence "2.6.4"
    "and let $KM$ be drawn through point $H$, parallel to either of $AB$ or $EF$ [Prop.~1.31],"
    (step4 : h.onLine KM ∧ ¬(KM.intersectsLine AB)) := by sorry

  euclid_apply (Elements.Book1.proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines KM AK) as k
  euclid_sentence "2.6.5"
    "and finally let $AK$ be drawn through $A$, parallel to either of $CL$ or $DM$ [Prop.~1.31]."
    (step5 : a.onLine AK ∧ ¬(AK.intersectsLine CE)) := by sorry

  euclid_sentence "2.6.6"
    "Therefore, since $AC$ is equal to $CB$, (rectangle) $AL$ is also equal to (rectangle) $CH$ [Prop.~1.36]."
    (step6 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ c:b:h + Triangle.area △ c:h:l) := by sorry

  euclid_sentence "2.6.7"
    "But, (rectangle) $CH$ is equal to (rectangle) $HF$ [Prop.~1.43]."
    (step7 : Triangle.area △ c:b:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by sorry

  euclid_sentence "2.6.8"
    "Thus, (rectangle) $AL$ is also equal to (rectangle) $HF$."
    (step8 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by sorry

  euclid_sentence "2.6.9"
    "Let (rectangle) $CM$ be added to both."
    (step9 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l)) := by sorry

  euclid_sentence "2.6.10"
    "Thus, the whole (rectangle) $AM$ is equal to the gnomon $NOP$."
    (step10 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) := by sorry

  euclid_sentence "2.6.11"
    "But, $AM$ is the (rectangle contained) by $AD$ and $DB$. For $DM$ is equal to $DB$."
    (step11 : Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─b)|) := by sorry

  euclid_sentence "2.6.12"
    "Thus, gnomon $NOP$ is also equal to the [rectangle contained] by $AD$ and $DB$."
    (step12 : (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) = |(a─d)| * |(d─b)|) := by sorry

  euclid_sentence "2.6.13"
    "Let $LG$, which is equal to the square on $BC$, be added to both."
    (step13 : Triangle.area △ l:h:g + Triangle.area △ l:g:e = |(c─b)| * |(c─b)|) := by sorry

  euclid_sentence "2.6.14"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the gnomon $NOP$ and the (square) $LG$."
    (step14 : |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| =
      ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e)) := by sorry

  euclid_sentence "2.6.15"
    "But the gnomon $NOP$ and the (square) $LG$ is (equivalent to) the whole square $CEFD$, which is on $CD$."
    (step15 : (((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
        Triangle.area △ c:e:f + Triangle.area △ c:f:d) ∧
      (Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)|)) := by sorry

  euclid_sentence "2.6.16"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CB$, is equal to the square on $CD$."
    (step16 : |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)|) := by sorry

  exact step16
  euclid_conclude_sentence "2.6.17"
    "Thus, if a straight-line is cut in half, and any straight-line added to it straight-on, (then) the rectangle contained by the whole (straight-line) with the (straight-line) having being added, and the (straight-line) having being added, plus the square on half (of the original straight-line), is equal to the square on the sum of half (of the original straight-line) and the (straight-line) having been added. (Which is) the very thing it was required to show."

end Elements.Book2
