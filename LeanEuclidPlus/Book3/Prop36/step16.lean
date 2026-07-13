import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step16 (b d e : Point) (ABC : Circle) (DB : Line)
    (hbABC : b.onCircle ABC) (hbDB : b.onLine DB) (hnint : ¬DB.intersectsCircle ABC)
    (he_centre : e.isCentre ABC) (hdDB : d.onLine DB) (hdnot : ¬d.onCircle ABC) :
    ∠ e:b:d = ∟ := by
  euclid_apply (proposition_18 b e ABC DB)
  euclid_finish

end Elements.Book3
