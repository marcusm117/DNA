import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step8 (c e g h : Point) (AB CG CH CE : Line) (EFG : Circle)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hcCG : c.onLine CG) (hgCG : g.onLine CG)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (heAB : e.onLine AB) (hgAB : g.onLine AB)
    (hbetween : between e h g)
    (hcen : c.isCentre EFG) (heEFG : e.onCircle EFG) (hgEFG : g.onCircle EFG)
    (hstep4 : distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE)
    (hcAB : ¬c.onLine AB)
    (hstep6a1 : |(g─h)| = |(h─e)|)
    (hstep7 : |(c─g)| = |(c─e)|) :
    ∠ c:h:g = ∠ e:h:c := by
  euclid_apply (proposition_8 h c g h c e CH CG AB CH CE AB)
  euclid_finish

end Elements.Book1
