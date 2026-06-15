import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: GKEF as formParallelogram g k f e HK DE CF BE (g,k on HK; f,e on DE; g,f on CF;
   k,e on BE; g.sameSide f BE; HK ∥ DE; CF ∥ BE). sameSide g f BE (g,f on CF ∥ BE) + non-intersections
   + k ≠ e supplied. -/
theorem helper_2_4_step25_pargkef (g k f e : Point) (HK DE CF BE : Line)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK)
    (hfDE : f.onLine DE) (heDE : e.onLine DE)
    (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hkBE : k.onLine BE) (heBE : e.onLine BE)
    (hHKDE : ¬(HK.intersectsLine DE)) (hCFBE : ¬(CF.intersectsLine BE))
    (hgfbe : g.sameSide f BE) (hke : k ≠ e) :
    formParallelogram g k f e HK DE CF BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
