import SystemE
import Book1.Prop26.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step12
    (a b e f : Point) (AB CD EA EB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (heCD : e.onLine CD) (hfCD : f.onLine CD) (heAB : ¬e.onLine AB)
    (heEA : e.onLine EA) (haEA : a.onLine EA)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (hbet : between a f b)
    (step9_assumption1 : |(e─a)| = |(e─b)|)
    (step11 : formTriangle e a f EA AB CD ∧ formTriangle e f b CD AB EB ∧
              ∠ e:a:f = ∠ e:b:f ∧ ∠ a:f:e = ∠ b:f:e ∧ |(f─e)| = |(f─e)|)
    : |(e─a)| = |(e─b)| ∧ |(a─f)| = |(f─b)| := by
  have htri1 := step11.1
  have htri2 : formTriangle e b f EB AB CD := by euclid_finish
  have hang1 := step11.2.2.1
  have hang2 := step11.2.2.2.1
  euclid_apply (Elements.Book1.proposition_26 e a f e b f EA AB CD EB AB CD)
  euclid_finish

end Elements.Book3
