import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step3 (a b d : Point) (ABC : Circle) (DA DB : Line)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hd : d.isCentre ABC)
    (hdDA : d.onLine DA) (haDA : a.onLine DA)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) :
    distinctPointsOnLine d a DA ∧ distinctPointsOnLine d b DB := by
  constructor <;> euclid_finish

end Elements.Book3
