import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e, e0 on opposite rays of AE (between e0 a e): ∠d:a:e is the supplement of ∠d:a:e0 = ∟, so ∟.
theorem helper_3_33_step3_pos
    (a d e e0 : Point) (AE : Line)
    (hperp : ∠ d:a:e0 = ∟) (hdoffAE : ¬ d.onLine AE)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE)
    (hbet : between e0 a e) :
    ∠ d:a:e = ∟ := by
  euclid_apply (perpendicular_onlyif e0 e a d AE)
  euclid_finish

end Elements.Book3
