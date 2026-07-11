import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- d, b cannot BOTH lie on the centre-line GH: if they did, each of g, h (equidistant from d and b, and
-- on GH) would be the midpoint of db, forcing g = h — contradicting g ≠ h.
theorem helper_3_13_step4_int_nboth (ABDC EBFD : Circle) (d b g h : Point) (GH : Line)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hdb : d ≠ b)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h) :
    ¬(d.onLine GH ∧ b.onLine GH) := by
  rintro ⟨hd_on, hb_on⟩
  euclid_finish

end Elements.Book3
