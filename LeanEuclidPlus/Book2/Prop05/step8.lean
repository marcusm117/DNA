import SystemE
import Book.Prop36
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8: CM = AL via AC = CB [Prop.~1.36]. Equal parallelograms on equal bases and same parallels. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8 (a b c k l m : Point) (AB CE KM : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hlCE : l.onLine CE) (hmKM : m.onLine KM)
    (hKMCE : ¬(KM.intersectsLine CE))
    (hacb : |(a─c)| = |(c─b)|) :
    Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k := by
  -- Uses proposition_36 for criterion-3 (equal pgrams on equal bases, same parallels)
  euclid_apply (Elements.Book1.proposition_36 a c l k b m CE KM AB)
  euclid_finish

end Elements.Book2