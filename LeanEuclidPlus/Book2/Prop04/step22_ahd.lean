import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: h (= HK ∩ AD) is between a and d on the left side AD. HK separates a from d:
   • g (∈ HK) is between b and d on BD (step5_bgd), so b and d are on opposite sides of HK (pasch_3);
   • a and b both lie on AB ∥ HK, so they are on the same side of HK (step22_absHK);
   hence a and d are on opposite sides of HK, and h (= AD ∩ HK) lies between them (pasch_4). -/
theorem helper_2_4_step22_ahd (a b d g h : Point) (AD HK BD AB : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbgd : between b g d)
    (hanHK : ¬(a.onLine HK)) (hdnHK : ¬(d.onLine HK)) (had : a ≠ d)
    (habsHK : a.sameSide b HK) :
    between a h d := by
  euclid_intros
  -- a ≠ h and d ≠ h since a, d ∉ HK but h ∈ HK
  have hah : a ≠ h := fun hh => hanHK (hh ▸ hhHK)
  have hdh : d ≠ h := fun hh => hdnHK (hh ▸ hhHK)
  -- b, d on opposite sides of HK (g between them, g ∈ HK)
  euclid_apply (pasch_3 b g d HK)
  euclid_apply (pasch_4 a h d HK AD)
  euclid_finish

end Elements.Book2
