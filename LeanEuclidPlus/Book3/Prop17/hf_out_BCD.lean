import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- f is outside BCD: same radius as a from center e (both on AFG), a is outside BCD.
theorem helper_3_17_hf_out_BCD (a d e f : Point) (BCD AFG : Circle)
    (hcen_BCD : e.isCentre BCD)
    (hcen_AFG : e.isCentre AFG)
    (ha_onAFG : a.onCircle AFG)
    (hf_onAFG : f.onCircle AFG)
    (hd_onBCD : d.onCircle BCD)
    (ha_not_inside : ¬a.insideCircle BCD)
    (ha_not_on : ¬a.onCircle BCD) :
    f.outsideCircle BCD := by
  have h_ef_ea : |(e─f)| = |(e─a)| :=
    point_on_circle_onlyif e a f AFG ⟨hcen_AFG, ha_onAFG, hf_onAFG⟩
  constructor
  · intro hf_in
    have hf_lt : |(e─f)| < |(e─d)| :=
      point_in_circle_onlyif e d f BCD ⟨hcen_BCD, hd_onBCD, hf_in⟩
    exact ha_not_inside (point_in_circle_if e d a BCD ⟨hcen_BCD, hd_onBCD, by linarith⟩)
  · intro hf_on
    have h_ef_ed : |(e─f)| = |(e─d)| :=
      point_on_circle_onlyif e d f BCD ⟨hcen_BCD, hd_onBCD, hf_on⟩
    exact ha_not_on (point_on_circle_if e d a BCD ⟨hcen_BCD, hd_onBCD, by linarith⟩)

end Elements.Book3
