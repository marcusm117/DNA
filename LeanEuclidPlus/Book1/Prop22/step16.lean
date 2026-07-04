import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step16 (k f g a a' b b' c c' : Point)
    (h11 : |(k─f)| = |(a─a')|) (h15 : |(f─g)| = |(b─b')|) (h14 : |(k─g)| = |(c─c')|) :
    |(k─f)| = |(a─a')| ∧ |(f─g)| = |(b─b')| ∧ |(g─k)| = |(c─c')| :=
  ⟨h11, h15, (segment_symmetric g k).trans h14⟩

end Elements.Book1
