import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step17_par
    (a b c d : Point) (AB CD AC BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hdb : d ≠ b)
    (hca_ss : c.sameSide a BD)
    (hCDAB : ¬CD.intersectsLine AB)
    (hACBD : ¬AC.intersectsLine BD) :
    formParallelogram a b c d AB CD AC BD := by
  euclid_intros
  have hABCD : ¬AB.intersectsLine CD := fun hh => hCDAB (intersection_symm AB CD hh)
  have hss : a.sameSide c BD := by euclid_finish
  euclid_finish

end Elements.Book2
