import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12: AH = |(a─d)| * |(d─b)|. The parallelogram AH (area △adh + △ahk) is the rectangle with
   sides AD and DH; and DH = DB (the shared worker step13_dhdb), so it equals |a─d|·|d─b|. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12 (a b c d e h k : Point) (AB CE DG BE AK KM : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcdb : between c d b)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE)) :
    Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)| := by
  have step13_dhdb : |(d─h)| = |(d─b)| := by sorry
  euclid_finish

end Elements.Book2
