import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b same side of AE as d, e0 opposite side of AB from d.  Take e1 = AE reflected past a
-- (between e0 a e1); then ∠b:a:e1 = ∠d:a:e1 = ∟ and e1 is on d's side of AB, so
-- ∠e1:a:b = ∠e1:a:d + ∠d:a:b forces ∠d:a:b = 0, contradicting 0 < ∠d:a:b.
theorem helper_3_33_hFG_int_AE_hcon_ss_b
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : b.sameSide d AE) (hnh2 : ¬ e0.sameSide d AB) :
    False := by
  euclid_apply (extend_point AE e0 a) as e1
  euclid_apply (perpendicular_onlyif e0 e1 a b AE)
  euclid_apply (perpendicular_onlyif e0 e1 a d AE)
  have hss : e1.sameSide d AB := by euclid_finish
  euclid_apply (sum_angles_onlyif a e1 b d AE AB)
  euclid_finish

end Elements.Book3
