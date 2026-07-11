import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step5
    (ABC : Circle) (b g l m₀ : Point) (BG NO : Line)
    (hbABC : b.onCircle ABC) (hgABC : g.onCircle ABC)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG)
    (hm₀offBG : ¬m₀.onLine BG) (hm₀NO : m₀.onLine NO)
    (hassump1 : l.onLine NO ∧ between b l g ∧ |(b─l)| = |(l─g)| ∧ ∠ b:l:m₀ = ∟)
    : ∃ o : Point, o.isCentre ABC ∧ o.onLine NO := by
  obtain ⟨hlNO, hblg, hbisect, hperp⟩ := hassump1
  obtain ⟨o, ho⟩ := exists_centre ABC
  refine ⟨o, ho, ?_⟩
  have h_ob_og : |(o─b)| = |(o─g)| := by
    have := point_on_circle_onlyif o b g ABC ⟨ho, hbABC, hgABC⟩
    linarith
  have hlBG : l.onLine BG := between_same_line_in b l g BG ⟨hblg, hbBG, hgBG⟩
  by_cases hoLBG : o.onLine BG
  · have hol : o = l := by euclid_finish
    rw [hol]; exact hlNO
  · have h_eq_angles : ∠ b:l:o = ∠ o:l:g := by euclid_finish
    have h_blo_perp : ∠ b:l:o = ∟ :=
      perpendicular_if b g l o BG ⟨hbBG, hgBG, hblg, hoLBG, h_eq_angles⟩
    have hlNo : l ≠ o := fun h => hoLBG (h ▸ hlBG)
    obtain ⟨LO, hlLO, hoLO⟩ := line_from_points l o hlNo
    by_contra h_o_notNO
    have hLONeNO : LO ≠ NO := fun h => h_o_notNO (h ▸ hoLO)
    euclid_finish

end Elements.Book3
