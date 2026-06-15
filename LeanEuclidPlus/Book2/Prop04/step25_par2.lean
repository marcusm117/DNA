import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: HGFD as formParallelogram g f h d CF AD HK DE (g,f on CF; h,d on AD; g,h on HK;
   f,d on DE; g.sameSide h DE; CF ∥ AD; HK ∥ DE). sameSide g h DE (g,h on HK ∥ DE) + non-intersections
   + f ≠ d supplied. -/
theorem helper_2_4_step25_par2 (g f h d : Point) (CF AD HK DE : Line)
    (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK)
    (hfDE : f.onLine DE) (hdDE : d.onLine DE)
    (hCFAD : ¬(CF.intersectsLine AD)) (hHKDE : ¬(HK.intersectsLine DE))
    (hghde : g.sameSide h DE) (hfd : f ≠ d) :
    formParallelogram g f h d CF AD HK DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
