import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: the top-half rectangle ABFH as formParallelogram h f a b HF AB AD BE (h,f on HF;
   a,b on AB; h,a on AD; f,b on BE; h.sameSide a BE; HF ∥ AB; AD ∥ BE). This orientation puts the
   right-angle vertex a in the third (c) slot for rectangle_area. -/
theorem helper_2_7_step8_parAF2 (h f a b : Point) (HF AB AD BE : Line)
    (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hhAD : h.onLine AD) (haAD : a.onLine AD)
    (hfBE : f.onLine BE) (hbBE : b.onLine BE)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hhsa : h.sameSide a BE) (hfb : f ≠ b) :
    formParallelogram h f a b HF AB AD BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
