import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- AL ∥ BD and BD meets BC at b ⟹ AL meets BC. (else AL ∥ BC ⟹ BD = BC via
-- parallel_line_unique, contradicting d ∈ BD but d ∉ BC.)
theorem helper_1_47_hALBC
    (a b d : Point) (AL BD BC : Line)
    (ha_AL : a.onLine AL) (h_nALBD : ¬AL.intersectsLine BD) (hoffBD : ¬a.onLine BD)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hb_BC : b.onLine BC) (h_d_nBC : ¬d.onLine BC) :
    AL.intersectsLine BC := by
  by_contra hcon
  have hbAL : ¬b.onLine AL := by
    intro hb_AL
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  euclid_apply (parallel_line_unique b AL BD BC)
  euclid_finish

end Elements.Book1
