import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (heAB : e.onLine AB) (hgAB : g.onLine AB) (hhAB : h.onLine AB)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hbetween : between e h g)
    (hcAB : ¬c.onLine AB)
    (hab_ne : a ≠ b)
    (hstep10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  by_cases h1 : a = h
  · right
    by_cases h2 : between b h g
    · euclid_apply (equal_angles h b e c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h b g c c AB CH)
      euclid_finish
  · left
    by_cases h2 : between a h g
    · euclid_apply (equal_angles h a e c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h a g c c AB CH)
      euclid_finish

end Elements.Book1
