import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 9: DE produced to H — H is on line ED, on the semicircle, and (from `between h e d`, the order
-- h–e–d given by intersection_circle_line_extending_points) NOT between E and D. The context carries
-- `between h e d`; `¬ between e h d` is derived in-body (betweenness exclusivity).
theorem helper_2_14_step9 (h e d : Point) (ED : Line) (BHF : Circle)
    (h_hED : h.onLine ED) (h_bet : between h e d) (h_hc : h.onCircle BHF) :
    h.onLine ED ∧ ¬ between e h d ∧ h.onCircle BHF := by euclid_finish

end Elements.Book2
