import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 9: "DE produced to H" — H is on line ED, beyond E (the produced point with `between h e d`),
-- hence H is NOT between E and D.
theorem helper_2_14_step9 (h e d : Point) (ED : Line)
    (h_onED : h.onLine ED) (h_bet : between h e d) :
    h.onLine ED ∧ ¬between e h d := by
  euclid_finish

end Elements.Book2
