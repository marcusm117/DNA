import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: HGFD is a parallelogram, formParallelogram h g d f HK DE AD CF. Sides: h,g on HK;
   d,f on DE (∥ HK); h,d on AD; g,f on CF (∥ AD). The atoms HK ∥ DE (step22_hkde),
   h.sameSide d CF (step22_hsd) and g ≠ f (step22_gf) are supplied by sub-nodes. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_par (h g f d : Point) (HK DE AD CF : Line)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK)
    (hdDE : d.onLine DE) (hfDE : f.onLine DE)
    (hhAD : h.onLine AD) (hdAD : d.onLine AD)
    (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hHKDE : ¬(HK.intersectsLine DE)) (hADCF : ¬(AD.intersectsLine CF))
    (hhsd : h.sameSide d CF) (hgf : g ≠ f) :
    formParallelogram h g d f HK DE AD CF := by
  euclid_intros
  euclid_finish

end Elements.Book2
