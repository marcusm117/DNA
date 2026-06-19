import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

/- Shared parallelogram-area recast. The `parallelogram_area` axiom splits a parallelogram `a b c d`
   along its two diagonals into the equal triangle sums `△a:c:d + △a:d:b = △b:a:c + △b:c:d`. The
   recurring Book-2 "complement" leaves (e.g. Prop05 step6_lhs / step6_rhs) each apply that axiom and
   then `euclid_finish` to permute the vertex labels into THIS figure's triangulation. This wrapper
   proves the split from the `formParallelogram` fact in one shot; the only thing left at a call site
   is the (cheap, symmetry-only) relabel, which `euclid_finish` closes.

   Single atomic hyp (`formParallelogram …`, which the parent already has) so `(by assumption)`
   discharges it. Cites no proposition — pure axiom glue, faithfulness-neutral. -/
theorem parallelogram_area' (a b c d : Point) (AB CD AC BD : Line)
    (hpar : formParallelogram a b c d AB CD AC BD) :
    Triangle.area △ a:c:d + Triangle.area △ a:d:b
      = Triangle.area △ b:a:c + Triangle.area △ b:c:d := by
  euclid_apply (parallelogram_area a b c d AB CD AC BD)
  euclid_finish

end Elements
