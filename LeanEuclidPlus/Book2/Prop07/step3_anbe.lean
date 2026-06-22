import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: a ∉ BE. If a ∈ BE then a, b, e are collinear on BE (b, e already on BE), making the
   square's right angle ∠ a:b:e = ∟ a degenerate angle of three collinear points — impossible. -/
theorem helper_2_7_step3_anbe (a b e : Point) (BE : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hab : a ≠ b) (heb : e ≠ b)
    (habe : ∠ a:b:e = ∟) :
    ¬(a.onLine BE) := by
  intro haBE
  euclid_finish

end Elements.Book2
