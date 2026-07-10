import SystemE
import Book.Prop04
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step26
    (ABC : Circle) (m k d b0 g : Point) (MK DB AG : Line)
    (hm : m.isCentre ABC)
    (hk : k.onCircle ABC)
    (hb0_circ : b0.onCircle ABC)
    (hdnotCircle : ¬d.onCircle ABC)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK) (hne_mk : m ≠ k)
    (hdDB : d.onLine DB) (hb0DB : b0.onLine DB)
    (hmAG : m.onLine AG) (hdAG : d.onLine AG)
    (hkoffAG : ¬k.onLine AG) (hb0offAG : ¬b0.onLine AG)
    (hbet_dgm : between d g m)
    (hstep24 : |(m─k)| = |(m─b0)|)
    (hstep25 : ∠ k:m:d = ∠ b0:m:d) :
    |(d─k)| = |(d─b0)| := by
  have hne_dm : d ≠ m := by euclid_finish
  have hne_kd : k ≠ d := fun h => hdnotCircle (h ▸ hk)
  have hne_b0d : b0 ≠ d := fun h => hdnotCircle (h ▸ hb0_circ)
  have hne_b0m : b0 ≠ m := fun h => absurd (h ▸ hb0_circ) (by euclid_finish)
  obtain ⟨KD, hkKD, hdKD⟩ := line_from_points k d hne_kd
  obtain ⟨MB, hmMB, hb0MB⟩ := line_from_points m b0 hne_b0m.symm
  have hft_mkd : formTriangle m k d MK KD AG := by euclid_finish
  have hft_mb0d : formTriangle m b0 d MB DB AG := by euclid_finish
  have hconj4 : formTriangle m k d MK KD AG ∧ formTriangle m b0 d MB DB AG ∧
      |(m─k)| = |(m─b0)| ∧ |(m─d)| = |(m─d)| ∧ ∠k:m:d = ∠b0:m:d :=
    ⟨hft_mkd, hft_mb0d, hstep24, rfl, hstep25⟩
  euclid_apply (Elements.Book1.proposition_4 m k d m b0 d MK KD AG MB DB AG)
  linarith [segment_symmetric k d, segment_symmetric b0 d]

end Elements.Book3
