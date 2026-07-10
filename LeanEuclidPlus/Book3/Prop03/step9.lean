import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step9
    (a b e f : Point) (AB EA EB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (heAB : ¬e.onLine AB)
    (heEA : e.onLine EA) (haEA : a.onLine EA)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (hbet : between a f b)
    (hassump1 : |(e─a)| = |(e─b)|)
    : ∠ e:a:f = ∠ e:b:f := by
  have htri : formTriangle e a b EA AB EB := by euclid_finish
  have h5 : ∠ e:a:b = ∠ e:b:a := by
    euclid_apply (Elements.Book1.proposition_5' e a b EA AB EB)
    euclid_finish
  euclid_finish

end Elements.Book3
