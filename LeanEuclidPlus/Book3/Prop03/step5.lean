import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_3_step5
    (a b e f : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB) (heAB : ¬e.onLine AB)
    (hbet : between a f b)
    (hassump1 : ∠ a:f:e = ∠ b:f:e)
    : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟ := by
  have hperp : ∠ a:f:e = ∟ := by
    euclid_apply (perpendicular_if a b f e AB)
    euclid_finish
  exact ⟨hperp, hassump1.symm.trans hperp⟩

end Elements.Book3
