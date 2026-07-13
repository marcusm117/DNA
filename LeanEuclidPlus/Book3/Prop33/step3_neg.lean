import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e, e0 on the same ray of AE (¬between e0 a e): ∠d:a:e = ∠d:a:e0 = ∟ (equal_angles).
theorem helper_3_33_step3_neg
    (a d e e0 g : Point) (AD AE : Line)
    (hperp : ∠ d:a:e0 = ∟) (hdoffAE : ¬ d.onLine AE)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE)
    (hega : between e g a) (hbet : ¬ between e0 a e) :
    ∠ d:a:e = ∟ := by
  euclid_apply (equal_angles a e0 e d d AE AD)
  euclid_finish

end Elements.Book3
