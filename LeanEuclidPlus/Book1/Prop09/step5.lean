import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_step5 (a f : Point) (DE AF : Line)
    (h1 : a.onLine AF) (h2 : f.onLine AF)
    (h3 : ¬f.onLine DE) (h4 : ¬a.onLine DE) (h5 : ¬f.sameSide a DE) :
    distinctPointsOnLine a f AF := by euclid_finish

end Elements.Book1
