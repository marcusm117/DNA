import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step16_ahab
    (a b h f c x : Point) (AH AB AC : Line)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_caf : between c a f)
    (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟)
    (hxoff : ¬x.onLine AC) (hboff : ¬b.onLine AC) (hhoff : ¬h.onLine AC)
    (hhnsx : ¬h.sameSide x AC) (hxnsb : ¬x.sameSide b AC) :
    AH = AB := by
  euclid_finish

end Elements.Book2
