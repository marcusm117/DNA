import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠d:a:e = ∟ : e (the diameter's far end) lies on AE, and AD ⊥ AE at a (∠d:a:e0 = ∟ with e0 on AE);
-- either e is on the same ray as e0 (equal_angles) or opposite (perpendicular_onlyif on the straight
-- line e0-a-e) — either way ∠d:a:e = ∟.
theorem helper_3_33_step38_hperp
    (a d e e0 : Point) (AD AE : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0offAD : ¬ e0.onLine AD)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE) (he_ne : e ≠ a)
    (hassump1 : ∠ d:a:e0 = ∟) :
    ∠ d:a:e = ∟ := by
  by_cases hbet : between e0 a e
  · euclid_apply (perpendicular_onlyif e0 e a d AE)
    euclid_finish
  · euclid_apply (equal_angles a e0 e d d AE AD)
    euclid_finish

end Elements.Book3
