import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step12
    (ABC : Circle) (d : Point) (GK HL : Line)
    (hstep9 : ∀ o : Point, o.isCentre ABC → o.onLine GK)
    (hstep10 : ∀ o : Point, o.isCentre ABC → o.onLine HL)
    (hstep11 : ∀ p : Point, p.onLine GK → p.onLine HL → p = d)
    : d.isCentre ABC := by
  obtain ⟨o, ho⟩ := exists_centre ABC
  have ho_GK : o.onLine GK := hstep9 o ho
  have ho_HL : o.onLine HL := hstep10 o ho
  have hod : o = d := hstep11 o ho_GK ho_HL
  exact hod ▸ ho

end Elements.Book3
