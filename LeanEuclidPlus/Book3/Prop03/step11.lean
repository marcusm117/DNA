import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step11
    (a b e f : Point) (AB CD EA EB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (heCD : e.onLine CD) (hfCD : f.onLine CD) (heAB : ¬e.onLine AB)
    (heEA : e.onLine EA) (haEA : a.onLine EA)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (hbet : between a f b)
    (step9 : ∠ e:a:f = ∠ e:b:f)
    (step10 : ∠ a:f:e = ∠ b:f:e)
    : formTriangle e a f EA AB CD ∧ formTriangle e f b CD AB EB ∧
      ∠ e:a:f = ∠ e:b:f ∧ ∠ a:f:e = ∠ b:f:e ∧ |(f─e)| = |(f─e)| :=
  ⟨by euclid_finish, by euclid_finish, step9, step10, rfl⟩

end Elements.Book3
