import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  euclid_intros
  euclid_intro_sentence "1.37.0"
    "Triangles which are on the same base and between the same parallels are equal to one another.    Let $ABC$ and $DBC$ be triangles on the same base $BC$, and between the same parallels $AD$ and $BC$. I say that triangle $ABC$ is equal to triangle $DBC$. "

  euclid_apply (extend_point AD d a) as e
  euclid_apply (extend_point AD a d) as f
  euclid_sentence "1.37.1"
    "Let $AD$ have been produced in both directions to $E$ and $F$,"
    (step1 : between d a e ∧ between a d f) := by sorry

  euclid_apply (line_from_points b e) as BE
  euclid_sentence "1.37.2"
    "and let the (straight-line) $BE$ have been drawn through $B$ parallel to $CA$ [Prop.~1.31],"
    (step2 : b.onLine BE ∧ e.onLine BE ∧ ¬(BE.intersectsLine AC)) := by sorry

  euclid_apply (line_from_points c f) as CF
  euclid_sentence "1.37.3"
    "and let the (straight-line) $CF$ have been drawn through $C$ parallel to $BD$ [Prop.~1.31]."
    (step3 : c.onLine CF ∧ f.onLine CF ∧ ¬(CF.intersectsLine BD)) := by sorry

  euclid_sentence "1.37.4"
    "Thus, $EBCA$ and $DBCF$ are both parallelograms,"
    (step4 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF) := by sorry

  -- @assumption_valid
  have step5_assumption1 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF := by assumption
  -- @assumption ("they are on the same base $BC$, and between the same parallels $BC$ and $EF$", formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF)
  euclid_sentence "1.37.5"
    "and are equal. For they are on the same base $BC$, and between the same parallels $BC$ and $EF$ [Prop.~1.35]."
    (step5 : Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f) := by sorry

  euclid_sentence "1.37.6"
    "And the triangle $ABC$ is half of  the parallelogram $EBCA$. For the diagonal $AB$ cuts the latter in half [Prop.~1.34]."
    (step6 : Triangle.area △ a:b:c = Triangle.area △ e:a:b) := by sorry

  euclid_sentence "1.37.7"
    "And the  triangle $DBC$ (is) half of the parallelogram $DBCF$. For the diagonal $DC$ cuts the latter in half [Prop.~1.34]."
    (step7 : Triangle.area △ d:b:c = Triangle.area △ f:d:c) := by sorry

  euclid_sentence "1.37.8"
    "[And the halves of equal things are equal to one another.]"
    (step8 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) := by sorry

  euclid_sentence "1.37.9"
    "Thus, triangle $ABC$ is equal to triangle $DBC$. "
    (step9 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) := by sorry

  exact step9
  euclid_conclude_sentence "1.37.10"
    "Thus, triangles which are on the same base and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
