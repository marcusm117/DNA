import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: k ≠ h. k ∈ AK∩KM; h ∈ DG∩KM; from between k l h, l strictly between them → k≠h. -/
theorem helper_2_5_step11_ahpar_kh (k h l : Point) (KM : Line)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hklh : between k l h) :
    k ≠ h := by
  euclid_intros
  euclid_finish

end Elements.Book2
