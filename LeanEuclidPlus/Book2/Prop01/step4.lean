import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.4: DK, EL, CH drawn through D, E, C parallel to BG (line BF) [Prop.~1.31]. Each line's
   through-point incidence and parallelism are produced by the proposition_31 constructions in
   Main; this helper repackages them. -/
theorem helper_2_1_step4 (d e c : Point) (DK EL CH BF : Line)
    (hdDK : d.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (heEL : e.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hcCH : c.onLine CH) (hCHBF : ¬(CH.intersectsLine BF)) :
    d.onLine DK ∧ ¬(DK.intersectsLine BF) ∧
      e.onLine EL ∧ ¬(EL.intersectsLine BF) ∧
      c.onLine CH ∧ ¬(CH.intersectsLine BF) := by
  exact ⟨hdDK, hDKBF, heEL, hELBF, hcCH, hCHBF⟩

end Elements.Book2
