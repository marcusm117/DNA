import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b,d opposite sides of AE; b same side of AD as e0 and d same side of AB as e0: e0 is the
-- interior ray, ∠b:a:d = ∠b:a:e0 + ∠e0:a:d = 2∟, contradicting ∠d:a:b < ∟.
theorem helper_3_33_hFG_int_AE_hos_tt
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE)
    (h4 : b.sameSide e0 AD) (h5 : d.sameSide e0 AB) :
    False := by
  euclid_apply (sum_angles_onlyif a b d e0 AB AD)
  euclid_finish

end Elements.Book3
