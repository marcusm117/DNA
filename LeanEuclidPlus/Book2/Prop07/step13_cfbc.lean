import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: area(CF = CBFG) = |b─c|². CBFG = formParallelogram c g b f CN BE AB HF with the right
   angle ∠c:b:f = ∟ (vertex b in the c-slot); rectangle_area gives △c:b:f + △c:g:f = |c─b|·|c─g|,
   and |c─g| = |b─c| (the square is equilateral, step9_bccg), so the area (= △c:b:f + △c:f:g) is
   |b─c|·|b─c|. -/
theorem helper_2_7_step13_cfbc (c g b f : Point) (CN BE AB HF : Line)
    (hpar : formParallelogram c g b f CN BE AB HF)
    (hcbf : ∠ c:b:f = ∟) (hbccg : |(b─c)| = |(c─g)|) :
    Triangle.area △ c:b:f + Triangle.area △ c:f:g = |(b─c)| * |(b─c)| := by
  euclid_intros
  euclid_apply (rectangle_area c g b f CN BE AB HF)
  euclid_finish

end Elements.Book2
