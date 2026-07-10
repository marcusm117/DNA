import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step13_assumption1 (ABC : Circle) (m k d g a l : Point) (MK AG : Line)
    (hm : m.isCentre ABC) (hk : k.onCircle ABC) (hg : g.onCircle ABC) (ha : a.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_kg : k ≠ g)
    (hangle_kl : ∠k:m:d < ∠l:m:d)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK) :
    |(m─k)| + |(k─d)| > |(m─d)| := by
  have hmAG : m.onLine AG := by euclid_finish
  have hne_kd : k ≠ d := by intro h; exact hdnot (h ▸ hk)
  have hne_km : k ≠ m := by euclid_finish
  have hne_ka : k ≠ a := by
    intro heq
    have hpi : ∠a:m:d = ∟+∟ := by euclid_finish
    have hpi_k : ∠k:m:d = ∟+∟ := heq.symm ▸ hpi
    linarith [(angle_range (Angle.ofPoints l m d)).2, hangle_kl]
  have hkoffAG : ¬k.onLine AG := by
    intro hkAG
    have hrk : |(m─k)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : k = g ∨ k = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_kg rfl
    · exact hne_ka rfl
  euclid_apply (line_from_points k d) as KD
  have hformTri : formTriangle k m d MK AG KD := by euclid_finish
  euclid_apply (Elements.Book1.proposition_20 k m d MK AG KD)
  euclid_finish

end Elements.Book3
