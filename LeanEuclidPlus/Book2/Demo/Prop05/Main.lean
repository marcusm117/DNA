import SystemE
import Book1.Prop31.Main
import Book1Variants.Prop46

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_5 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c d ∧ between c d b ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| :=
by
  euclid_intros
  euclid_intro_sentence "2.5.0"
    "If a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line). For let any straight-line $AB$ be cut---equally at $C$, and unequally at $D$. I say that the rectangle contained by $AD$ and $DB$, plus the square on $CD$, is equal to the square on $CB$."

  euclid_apply (Elements.Book1.proposition_46 c b AB) as (e, f, EF, CE, BF)
  euclid_sentence "2.5.1"
    "For let the square $CEFB$ be described on $CB$ [Prop.~1.46],"
    (step1 : |(c─e)| = |(c─b)| ∧ |(b─f)| = |(c─b)| ∧ |(e─f)| = |(c─b)| ∧
      (∠ b:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:b:f = ∟) ∧ (∠ b:f:e = ∟)) := by sorry

  euclid_apply (line_from_points b e) as BE
  euclid_sentence "2.5.2"
    "and let $BE$ be joined,"
    (step2 : distinctPointsOnLine b e BE) := by sorry

  euclid_apply (Elements.Book1.proposition_31 d c e CE) as DG
  euclid_apply (intersection_lines DG EF) as g
  euclid_apply (intersection_lines DG BE) as h
  euclid_sentence "2.5.3"
    "and let $DG$ be drawn through $D$, parallel to either of $CE$ or $BF$ [Prop.~1.31],"
    (step3 : d.onLine DG ∧ ¬(DG.intersectsLine CE)) := by sorry

  euclid_apply (Elements.Book1.proposition_31 h a b AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM BF) as m
  euclid_sentence "2.5.4"
    "and again let $KM$ be drawn through $H$, parallel to either of $AB$ or $EF$ [Prop.~1.31],"
    (step4 : h.onLine KM ∧ ¬(KM.intersectsLine AB)) := by sorry

  euclid_apply (Elements.Book1.proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines AK KM) as k
  euclid_sentence "2.5.5"
    "and again let $AK$ be drawn through $A$, parallel to either of $CL$ or $BM$ [Prop.~1.31]."
    (step5 : a.onLine AK ∧ ¬(AK.intersectsLine CE)) := by sorry

  euclid_sentence "2.5.6"
    "And since the complement $CH$ is equal to the complement $HF$ [Prop.~1.43], let the (square) $DM$ be added to both."
    (step6 : Triangle.area △ c:d:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by sorry

  have step7_cmpar : formParallelogram c b l m AB KM CE BF := by sorry
  have step7_dfpar : formParallelogram d g b f DG BF AB EF := by sorry
  have step7_lhm : between l h m := by sorry
  have step7_dhg : between d h g := by sorry
  have step7_bmf : between b m f := by sorry

  euclid_sentence "2.5.7"
    "Thus, the whole (rectangle) $CM$ is equal to the whole (rectangle) $DF$."
    (step7 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) := by sorry
  
  euclid_sentence "2.5.8"
    "But, (rectangle) $CM$ is equal to (rectangle) $AL$, since $AC$ is also equal to $CB$ [Prop.~1.36]."
    (step8 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k) := by sorry

  euclid_sentence "2.5.9"
    "Thus, (rectangle) $AL$ is also equal to (rectangle) $DF$."
    (step9 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) := by sorry

  euclid_sentence "2.5.10"
    "Let (rectangle) $CH$ be added to both."
    (step10 : (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l) =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) := by sorry

  euclid_sentence "2.5.11"
    "Thus, the whole (rectangle) $AH$ is equal to the gnomon $NOP$."
    (step11 : Triangle.area △ a:d:h + Triangle.area △ a:h:k =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) := by sorry

  euclid_sentence "2.5.12"
    "But, $AH$ is the (rectangle contained) by $AD$ and $DB$."
    (step12 : Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)|) := by sorry

  euclid_sentence "2.5.13"
    "For $DH$ (is) equal to $DB$."
    (step13 : |(d─h)| = |(d─b)|) := by sorry

  euclid_sentence "2.5.14"
    "Thus, the gnomon $NOP$ is also equal to the (rectangle contained) by $AD$ and $DB$."
    (step14 : (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l) = |(a─d)| * |(d─b)|) := by sorry

  euclid_sentence "2.5.15"
    "Let $LG$, which is equal to the (square) on $CD$, be added to both."
    (step15 : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)|) := by sorry

  euclid_sentence "2.5.16"
    "Thus, the gnomon $NOP$ and the (square) $LG$ are equal to the rectangle contained by $AD$ and $DB$, and the square on $CD$."
    (step16 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|) := by sorry

  euclid_sentence "2.5.17"
    "But, the gnomon $NOP$ and the (square) $LG$ is (equivalent to) the whole square $CEFB$, which is on $CB$."
    (step17 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(c─b)| * |(c─b)|) := by sorry

  euclid_sentence "2.5.18"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CD$, is equal to the square on $CB$."
    (step18 : |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)|) := by sorry

  exact step18
  euclid_conclude_sentence "2.5.19"
    "Thus, if a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
