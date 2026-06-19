import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15: LG = |CD|². The square LG has area equal to the square on CD. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step15 (c d e g h l : Point) (CE DG KM : Line)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hgDG : g.onLine DG) (hhDG : h.onLine DG)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hcCE : c.onLine CE) (hdDG : d.onLine DG) :
    Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)| := by
  euclid_finish

end Elements.Book2