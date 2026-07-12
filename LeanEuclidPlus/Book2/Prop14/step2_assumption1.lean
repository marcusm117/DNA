import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.14.2 @assumption: "the square BD, equal to the rectilinear figure A, has been constructed" —
   the area equality is exactly step1's first conjunct (BD = A), so this just projects it. -/
theorem helper_2_14_step2_assumption1 (a b c q b₀ c₀ d e : Point)
    (hstep1 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d =
        Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟) :
    Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d =
      Triangle.area △ a:b:q + Triangle.area △ q:b:c :=
  hstep1.1

end Elements.Book2
