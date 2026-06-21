import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: ¬d.sameSide e KM. d and e are the ends of the diagonal DE; h lies on KM and between d
   and e (step7_dhe). By pasch_3, a point of KM strictly between d and e forces d, e onto opposite
   sides of KM. -/
theorem helper_2_6_step7_dnse (d e h : Point) (KM : Line)
    (hhKM : h.onLine KM) (hdhe : between d h e) :
    ¬(d.sameSide e KM) := by
  euclid_intros
  euclid_apply (pasch_3 d h e KM)
  euclid_finish

end Elements.Book2
