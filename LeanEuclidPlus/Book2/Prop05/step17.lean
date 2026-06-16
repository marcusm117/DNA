import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.17: Gnomon NOP + square LG = square CEFB = |CB|². The whole square CEFB
   decomposes into the gnomon (DF + CH) and the square LG. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step17 (c b d e f g h l : Point) (CE BF : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hstep1 : |(c─e)| = |(c─b)| ∧ |(b─f)| = |(c─b)| ∧ |(e─f)| = |(c─b)| ∧
      (∠ b:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:b:f = ∟) ∧ (∠ b:f:e = ∟)) :
    ((Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
        (Triangle.area △ c:d:h + Triangle.area △ c:h:l)) +
      (Triangle.area △ l:e:g + Triangle.area △ l:g:h) =
      |(c─b)| * |(c─b)| := by
  euclid_finish

end Elements.Book2