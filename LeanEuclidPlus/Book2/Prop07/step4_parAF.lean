import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: the top-half rectangle ABFH as formParallelogram a b h f AB HF AD BE (a,b on AB;
   h,f on HF; a,h on AD; b,f on BE; a.sameSide h BE; AB ∥ HF; AD ∥ BE). -/
theorem helper_2_7_step4_parAF (a b h f : Point) (AB HF AD BE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hash : a.sameSide h BE) (hbf : b ≠ f) :
    formParallelogram a b h f AB HF AD BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
