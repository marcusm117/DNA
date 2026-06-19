import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: DG = KM. k,h both on DG and KM with k≠h →
   two_points_determine_line k h DG KM → DG = KM. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_aoffDG_km (k h : Point) (DG KM : Line)
    (hkDG : k.onLine DG) (hhDG : h.onLine DG)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM)
    (hkh : k ≠ h) :
    DG = KM := by
  euclid_intros
  euclid_apply (two_points_determine_line k h DG KM)
  euclid_finish

end Elements.Book2
