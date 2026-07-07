import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step4
    (a b e f : Point) (AB CD EA EB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (heCD : e.onLine CD) (hfCD : f.onLine CD) (heAB : ¬e.onLine AB)
    (heEA : e.onLine EA) (haEA : a.onLine EA)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (hbet : between a f b)
    (step2 : |(a─f)| = |(f─b)| ∧ |(f─e)| = |(f─e)|)
    (step3 : |(e─a)| = |(e─b)|)
    : ∠ a:f:e = ∠ b:f:e := by
  euclid_apply (Elements.Book1.proposition_8 f a e f b e AB EA CD AB EB CD)
  euclid_finish

end Elements.Book3
