import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e1 is off AB: e1 lies on AE (with a), and a is on AB; if e1 were also on AB then AE = AB
-- (two common points a ≠ e1), so e0 ∈ AE would be on AB — contradicting ¬e0.onLine AB.
theorem helper_3_33_hFG_int_AE_he1off
    (a e0 e1 : Point) (AB AE : Line)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (he1 : between e0 a e1) (he0off : ¬ e0.onLine AB) :
    ¬ e1.onLine AB := by
  intro he1AB
  euclid_finish

end Elements.Book3
