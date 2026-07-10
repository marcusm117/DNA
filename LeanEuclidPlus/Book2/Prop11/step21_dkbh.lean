import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem helper_2_11_step21_dkbh
    (d k b h : Point) (CD AB BD GH : Line)
    (hpar : formParallelogram d k b h CD AB BD GH)
    (hkb : k ≠ b) :
    |(d─k)| = |(b─h)| := by
  -- opposite sides of the parallelogram HBDK are equal (proposition_34, diagonal KB).
  euclid_apply (line_from_points k b) as KB
  euclid_apply (proposition_34 d k b h CD AB BD GH KB)
  euclid_finish

end Elements.Book2
