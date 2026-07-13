import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step15 (b c d e : Point) (ABC : Circle) (EB EC ED : Line)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (heEC : e.onLine EC) (hcEC : c.onLine EC)
    (heED : e.onLine ED) (hdED : d.onLine ED)
    (he_centre : e.isCentre ABC) (hb_circ : b.onCircle ABC) (hc_circ : c.onCircle ABC)
    (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC) :
    distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED := by
  euclid_finish

end Elements.Book3
