import SystemE
import Book3.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step4 (b a' f e : Point) (ABCD : Circle) (EF BA : Line)
  (hassump1 : b.onLine EF ∧ b.onCircle ABCD ∧ ¬EF.intersectsCircle ABCD)   -- "some straight-line $EF$ touches the circle $ABCD$ at point $B$"
  (hassump2 : distinctPointsOnLine b a' BA ∧ ∠ a':b:f = ∟)   -- "$BA$ has been drawn from the point of contact, at right-angles to the tangent"
  (h_f_EF : f.onLine EF) (h_ebf : between e b f)
  : ∀ o : Point, o.isCentre ABCD → o.onLine BA := by
  euclid_apply (Elements.Book3.proposition_19 a' b f ABCD EF BA)
  assumption

end Elements.Book3
