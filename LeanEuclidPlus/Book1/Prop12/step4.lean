import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step4 (c e g h : Point) (AB CG CH CE : Line)
    (hcAB : ¬c.onLine AB) (heAB : e.onLine AB) (hgAB : g.onLine AB)
    (hbetween : between e h g)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) :
    distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE := by
  euclid_finish

end Elements.Book1
