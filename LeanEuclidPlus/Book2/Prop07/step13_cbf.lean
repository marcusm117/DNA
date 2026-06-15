import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: ∠ c:b:f = ∟. c is between a and b on AB, so ray b→c coincides with ray b→a; f is
   between b and e on BE, so ray b→f coincides with ray b→e. Hence ∠ c:b:f = ∠ a:b:e = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_cbf (a b c e f : Point) (AB BE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hfBE : f.onLine BE)
    (habe : ∠ a:b:e = ∟)
    (hacb : between a c b) (hbfe : between b f e) :
    ∠ c:b:f = ∟ := by
  euclid_intros
  euclid_apply (equal_angles b c a f f AB BE)
  euclid_apply (equal_angles b f e c c BE AB)
  euclid_finish

end Elements.Book2
