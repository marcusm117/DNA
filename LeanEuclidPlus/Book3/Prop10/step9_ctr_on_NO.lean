import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step9_ctr_on_NO
    (DEF : Circle) (b g l m₀ : Point) (BG NO : Line)
    (hbDEF : b.onCircle DEF) (hgDEF : g.onCircle DEF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG)
    (hlBG : l.onLine BG)
    (hm₀offBG : ¬m₀.onLine BG) (hm₀NO : m₀.onLine NO)
    (hlNO : l.onLine NO) (hblg : between b l g)
    (hblg' : |(b─l)| = |(l─g)|) (hperp_blm₀ : ∠ b:l:m₀ = ∟)
    : ∃ o : Point, o.isCentre DEF ∧ o.onLine NO := by
  obtain ⟨o, ho⟩ := exists_centre DEF
  refine ⟨o, ho, ?_⟩
  have h_ob_og : |(o─b)| = |(o─g)| := by
    have := point_on_circle_onlyif o b g DEF ⟨ho, hbDEF, hgDEF⟩
    linarith
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
