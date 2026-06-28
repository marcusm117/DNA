import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_step1
    (a b c d : Point) (AB CD AC BD : Line)
    (hab : a ≠ b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (hdb : d ≠ b)
    (hsameSide : c.sameSide a BD)
    (hpar1 : ¬CD.intersectsLine AB) (hpar2 : ¬AC.intersectsLine BD)
    (hcd : |(c─d)| = |(a─b)|) (hac : |(a─c)| = |(a─b)|)
    (hbd : |(b─d)| = |(a─b)|)
    (hang1 : ∠ b:a:c = ∟) (hang2 : ∠ a:c:d = ∟)
    (hang3 : ∠ a:b:d = ∟) (hang4 : ∠ b:d:c = ∟) :
    formParallelogram c d a b CD AB AC BD ∧ |(c─d)| = |(a─b)| ∧ |(a─c)| = |(a─b)| ∧ |(b─d)| = |(a─b)| ∧ ∠ b:a:c = ∟ ∧ ∠ a:c:d = ∟ ∧ ∠ a:b:d = ∟ ∧ ∠ c:d:b = ∟ := by
  euclid_finish

end Elements.Book2
