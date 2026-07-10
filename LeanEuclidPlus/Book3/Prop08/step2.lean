import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step2 (ABC : Circle) (m e f c k l h : Point) (ME MF MC MK ML MH : Line)
    (hm : m.isCentre ABC)
    (he : e.onCircle ABC) (hf : f.onCircle ABC) (hc : c.onCircle ABC)
    (hk : k.onCircle ABC) (hl : l.onCircle ABC) (hh : h.onCircle ABC)
    (hme1 : m.onLine ME) (hme2 : e.onLine ME)
    (hmf1 : m.onLine MF) (hmf2 : f.onLine MF)
    (hmc1 : m.onLine MC) (hmc2 : c.onLine MC)
    (hmk1 : m.onLine MK) (hmk2 : k.onLine MK)
    (hml1 : m.onLine ML) (hml2 : l.onLine ML)
    (hmh1 : m.onLine MH) (hmh2 : h.onLine MH) :
    distinctPointsOnLine m e ME ∧ distinctPointsOnLine m f MF ∧ distinctPointsOnLine m c MC ∧
    distinctPointsOnLine m k MK ∧ distinctPointsOnLine m l ML ∧ distinctPointsOnLine m h MH := by
  euclid_finish

end Elements.Book3
