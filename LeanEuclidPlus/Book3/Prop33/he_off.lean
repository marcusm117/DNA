import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- e is off AB: e lies on FG (⊥ to AB at f), and e ≠ f (between e f g0), so e ∉ AB (AB ∩ FG = {f}).
theorem helper_3_33_he_off
    (a b e f g0 : Point) (AB FG : Line)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hafb : between a f b)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (heFG : e.onLine FG) (hefg : between e f g0) :
    ¬ e.onLine AB := by
  intro heAB
  euclid_apply (two_points_determine_line e f AB FG)
  euclid_finish

end Elements.Book3
