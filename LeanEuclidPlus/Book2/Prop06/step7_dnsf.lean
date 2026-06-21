import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: ¬d.sameSide f KM (d and f are on opposite sides of the middle line KM). d, e are the
   ends of the diagonal DE and h (on KM) is between them (step7_dhe), so by pasch_3 d and e are on
   opposite sides of KM (step7_dnse: ¬d.sameSide e KM). e and f lie on EF ∥ KM, hence on the same
   side (step7_essf: e.sameSide f KM). If d.sameSide f then with e.sameSide f (symm) same_side_trans
   would give d.sameSide e — contradicting step7_dnse. -/
theorem helper_2_6_step7_dnsf (d e f : Point) (KM : Line)
    (hdnse : ¬(d.sameSide e KM)) (hessf : e.sameSide f KM) :
    ¬(d.sameSide f KM) := by
  intro hdsf
  euclid_apply (same_side_symm e f KM)
  euclid_apply (same_side_symm d f KM)
  euclid_apply (same_side_trans f d e KM)
  euclid_finish

end Elements.Book2
