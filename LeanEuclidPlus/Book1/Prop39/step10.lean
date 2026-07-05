import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_39_step10
    (d e b c : Point) (BC AD : Line) (a : Point)
    (step7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c)
    (step8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c)
    : ∀ (L : Line), a.onLine L → L ≠ AD → L.intersectsLine BC :=
  fun _ _ _ => absurd step7 step8

end Elements.Book1
