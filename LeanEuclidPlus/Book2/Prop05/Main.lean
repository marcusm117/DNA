import SystemE
import Book.Prop31
import Book.Prop46
import Book2.Prop05.step1
import Book2.Prop05.step2
import Book2.Prop05.step3
import Book2.Prop05.step4
import Book2.Prop05.step5
import Book2.Prop05.step6
import Book2.Prop05.step7
import Book2.Prop05.step8
import Book2.Prop05.step9
import Book2.Prop05.step10
import Book2.Prop05.step11
import Book2.Prop05.step12
import Book2.Prop05.step13
import Book2.Prop05.step14
import Book2.Prop05.step15
import Book2.Prop05.step16
import Book2.Prop05.step17
import Book2.Prop05.step18
import Book2.Prop05.step7_cmpar
import Book2.Prop05.step7_dfpar
import Book2.Prop05.step7_lhm
import Book2.Prop05.step7_dhg
import Book2.Prop05.step7_bmf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

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
      (∠ b:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:b:f = ∟) ∧ (∠ b:f:e = ∟)) := by euclid_apply (helper_2_5_step1 b c e f (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(e─f)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:f = ∟; assumption)) (by euclid_assumption "" (show ∠ b:f:e = ∟; assumption)))

  euclid_apply (line_from_points b e) as BE
  euclid_sentence "2.5.2"
    "and let $BE$ be joined,"
    (step2 : distinctPointsOnLine b e BE) := by euclid_apply (helper_2_5_step2 b c e BE BF (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)))

  euclid_apply (Elements.Book1.proposition_31 d c e CE) as DG
  euclid_apply (intersection_lines DG EF) as g
  euclid_apply (intersection_lines DG BE) as h
  euclid_sentence "2.5.3"
    "and let $DG$ be drawn through $D$, parallel to either of $CE$ or $BF$ [Prop.~1.31],"
    (step3 : d.onLine DG ∧ ¬(DG.intersectsLine CE)) := by euclid_apply (helper_2_5_step3 d DG CE (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))

  euclid_apply (Elements.Book1.proposition_31 h a b AB) as KM
  euclid_apply (intersection_lines KM CE) as l
  euclid_apply (intersection_lines KM BF) as m
  euclid_sentence "2.5.4"
    "and again let $KM$ be drawn through $H$, parallel to either of $AB$ or $EF$ [Prop.~1.31],"
    (step4 : h.onLine KM ∧ ¬(KM.intersectsLine AB)) := by euclid_apply (helper_2_5_step4 h KM AB (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))

  euclid_apply (Elements.Book1.proposition_31 a c e CE) as AK
  euclid_apply (intersection_lines AK KM) as k
  euclid_sentence "2.5.5"
    "and again let $AK$ be drawn through $A$, parallel to either of $CL$ or $BM$ [Prop.~1.31]."
    (step5 : a.onLine AK ∧ ¬(AK.intersectsLine CE)) := by euclid_apply (helper_2_5_step5 a AK CE (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))

  euclid_sentence "2.5.6"
    "And since the complement $CH$ is equal to the complement $HF$ [Prop.~1.43], let the (square) $DM$ be added to both."
    (step6 : Triangle.area △ c:d:h + Triangle.area △ c:h:l =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by euclid_apply (helper_2_5_step6 a b c d e f g h l m AB BE CE BF EF DG KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:f = ∟; assumption)) (by euclid_assumption "" (show ∠ b:f:e = ∟; assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)))

  have step7_cmpar : formParallelogram c b l m AB KM CE BF := by euclid_apply (helper_2_5_step7_cmpar b c d e h l m AB KM CE BF BE DG (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show between c d b; assumption)))
  have step7_dfpar : formParallelogram d g b f DG BF AB EF := by euclid_apply (helper_2_5_step7_dfpar b c d e f g AB BF CE DG EF (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ∠b:c:e = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)))
  have step7_lhm : between l h m := by euclid_apply (helper_2_5_step7_lhm b c d e f g h l m AB BF BE EF CE DG KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show formParallelogram c b l m AB KM CE BF; assumption)) (by euclid_assumption "" (show formParallelogram d g b f DG BF AB EF; assumption)) (by euclid_assumption "" (show between c d b; assumption)))
  have step7_dhg : between d h g := by euclid_apply (helper_2_5_step7_dhg b c d e g h AB BE CE DG EF KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between c d b; assumption)))
  have step7_bmf : between b m f := by euclid_apply (helper_2_5_step7_bmf b c d e f h m AB BF BE EF CE DG KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)) (by euclid_assumption "" (show between c d b; assumption)))

  euclid_sentence "2.5.7"
    "Thus, the whole (rectangle) $CM$ is equal to the whole (rectangle) $DF$."
    (step7 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) := by euclid_apply (helper_2_5_step7 c d b f g h l m AB KM CE BF DG EF (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show Triangle.area △ c:d:h + Triangle.area △ c:h:l = Triangle.area △ h:m:f + Triangle.area △ h:f:g; assumption)) (by euclid_assumption "" (show formParallelogram c b l m AB KM CE BF; assumption)) (by euclid_assumption "" (show formParallelogram d g b f DG BF AB EF; assumption)) (by euclid_assumption "" (show between l h m; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show between b m f; assumption)))
  
  euclid_sentence "2.5.8"
    "But, (rectangle) $CM$ is equal to (rectangle) $AL$, since $AC$ is also equal to $CB$ [Prop.~1.36]."
    (step8 : Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k) := by euclid_apply (helper_2_5_step8 a b c d k l m AB KM AK CE BF (by euclid_assumption "" (show |(a─c)| = |(c─b)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show formParallelogram c b l m AB KM CE BF; assumption)))

  euclid_sentence "2.5.9"
    "Thus, (rectangle) $AL$ is also equal to (rectangle) $DF$."
    (step9 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) := by euclid_apply (helper_2_5_step9 a b c d f g k l m (by euclid_assumption "" (show Triangle.area △ c:b:m + Triangle.area △ c:m:l = Triangle.area △ d:b:f + Triangle.area △ d:f:g; assumption)) (by euclid_assumption "" (show Triangle.area △ c:b:m + Triangle.area △ c:m:l = Triangle.area △ a:c:l + Triangle.area △ a:l:k; assumption)))

  euclid_sentence "2.5.10"
    "Let (rectangle) $CH$ be added to both."
    (step10 : (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l) =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) := by euclid_apply (helper_2_5_step10 a b c d f g h k l m (by euclid_assumption "" (show Triangle.area △ a:c:l + Triangle.area △ a:l:k = Triangle.area △ d:b:f + Triangle.area △ d:f:g; assumption)))

  euclid_sentence "2.5.11"
    "Thus, the whole (rectangle) $AH$ is equal to the gnomon $NOP$."
    (step11 : Triangle.area △ a:d:h + Triangle.area △ a:h:k =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) := by euclid_apply (helper_2_5_step11 a b c d e f g h k l AB KM AK DG CE EF BF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show ∠ c:b:f = ∟; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show Triangle.area △ a:c:l + Triangle.area △ a:l:k = Triangle.area △ d:b:f + Triangle.area △ d:f:g; assumption)))

  euclid_sentence "2.5.12"
    "But, $AH$ is the (rectangle contained) by $AD$ and $DB$."
    (step12 : Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)|) := by euclid_apply (helper_2_5_step12 a b c d e f g h k l AB KM AK DG CE EF BF BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show ∠ c:b:f = ∟; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))

  euclid_sentence "2.5.13"
    "For $DH$ (is) equal to $DB$."
    (step13 : |(d─h)| = |(d─b)|) := by euclid_apply (helper_2_5_step13 b c d e h AB CE DG BE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))

  euclid_sentence "2.5.14"
    "Thus, the gnomon $NOP$ is also equal to the (rectangle contained) by $AD$ and $DB$."
    (step14 : (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l) = |(a─d)| * |(d─b)|) := by euclid_apply (helper_2_5_step14 a b c d f g h k l m (by euclid_assumption "" (show Triangle.area △ a:d:h + Triangle.area △ a:h:k = (Triangle.area △ d:b:f + Triangle.area △ d:f:g) + (Triangle.area △ c:d:h + Triangle.area △ c:h:l); assumption)) (by euclid_assumption "" (show Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)|; assumption)))

  euclid_sentence "2.5.15"
    "Let $LG$, which is equal to the (square) on $CD$, be added to both."
    (step15 : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)|) := by euclid_apply (helper_2_5_step15 b c d e g h l AB CE DG KM EF BE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))

  euclid_sentence "2.5.16"
    "Thus, the gnomon $NOP$ and the (square) $LG$ are equal to the rectangle contained by $AD$ and $DB$, and the square on $CD$."
    (step16 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|) := by euclid_apply (helper_2_5_step16 a b c d f g h k l m e (by euclid_assumption "" (show (Triangle.area △ d:b:f + Triangle.area △ d:f:g) + (Triangle.area △ c:d:h + Triangle.area △ c:h:l) = |(a─d)| * |(d─b)|; assumption)) (by euclid_assumption "" (show Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)|; assumption)))

  euclid_sentence "2.5.17"
    "But, the gnomon $NOP$ and the (square) $LG$ is (equivalent to) the whole square $CEFB$, which is on $CB$."
    (step17 : ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(c─b)| * |(c─b)|) := by euclid_apply (helper_2_5_step17 a b c d e f g h l (by euclid_assumption "" (show |(a─c)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) + (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) + (Triangle.area △ l:e:g + Triangle.area △ l:g:h) = |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|; assumption)))

  euclid_sentence "2.5.18"
    "Thus, the rectangle contained by $AD$ and $DB$, plus the square on $CD$, is equal to the square on $CB$."
    (step18 : |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)|) := by euclid_apply (helper_2_5_step18 a b c d e f g h k l m (by euclid_assumption "" (show ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) + (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) + (Triangle.area △ l:e:g + Triangle.area △ l:g:h) = |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)|; assumption)) (by euclid_assumption "" (show ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) + (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) + (Triangle.area △ l:e:g + Triangle.area △ l:g:h) = |(c─b)| * |(c─b)|; assumption)))

  exact step18
  euclid_conclude_sentence "2.5.19"
    "Thus, if a straight-line is cut into equal and unequal (pieces, then) the rectangle contained by the unequal pieces of the whole (straight-line), plus the square on the (difference) between the (equal and unequal) pieces, is equal to the square on half (of the straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
