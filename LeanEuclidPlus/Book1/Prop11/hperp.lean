import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_11_hperp
    (a b c d e f : Point) (AB FC : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB)
    (hdAB : d.onLine AB)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hadc : between a d c)
    (hfAB : ¬(f.onLine AB))
    (hright : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) :
    ∠ a:c:f = ∟ := by
  obtain ⟨h_dcf_right, _⟩ := hright
  have h_eq : ∠ a:c:f = ∠ d:c:f := by
    euclid_apply (equal_angles c a d f f AB FC)
    euclid_finish
  euclid_finish

end Elements.Book1
