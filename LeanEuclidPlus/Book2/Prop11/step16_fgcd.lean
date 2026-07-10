import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem helper_2_11_step16_fgcd
    (FG AB CD : Line)
    (hFGAB : ¬FG.intersectsLine AB) (hABCD : ¬AB.intersectsLine CD)
    (hFGneAB : FG ≠ AB) (hABneCD : AB ≠ CD) (hFGneCD : FG ≠ CD) :
    ¬FG.intersectsLine CD := by
  euclid_apply (proposition_30 FG CD AB)
  euclid_finish

end Elements.Book2
