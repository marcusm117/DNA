import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step10 (c e g h : Point) (AB : Line)
    (heAB : e.onLine AB) (hgAB : g.onLine AB) (hhAB : h.onLine AB)
    (hbetween : between e h g)
    (hcAB : ¬c.onLine AB)
    (hassump1 : ∠ c:h:g = ∠ e:h:c) :
    ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟ := by
  euclid_apply (perpendicular_if e g h c AB)
  euclid_finish

end Elements.Book1
