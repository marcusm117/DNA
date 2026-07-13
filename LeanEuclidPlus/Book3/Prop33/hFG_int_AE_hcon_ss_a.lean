import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b same side of AE as d, and e0 same side of AB as d: ∠e0:a:b = ∠e0:a:d + ∠d:a:b
-- (sum_angles_onlyif, d the interior ray).  With ∠e0:a:b = ∠e0:a:d = ∟ this gives ∠d:a:b = 0.
theorem helper_3_33_hFG_int_AE_hcon_ss_a
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : b.sameSide d AE) (h2 : e0.sameSide d AB) :
    False := by
  euclid_apply (sum_angles_onlyif a e0 b d AE AB)
  euclid_finish

end Elements.Book3
