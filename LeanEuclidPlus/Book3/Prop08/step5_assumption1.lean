import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step5_assumption1 (ABC : Circle) (m e f d g a : Point) (ME AG : Line)
    (hm : m.isCentre ABC) (he : e.onCircle ABC) (ha : a.onCircle ABC) (hg : g.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_ea : e ≠ a)
    (hang : ∠ e:m:d > ∠ f:m:d)
    (hMEm : m.onLine ME) (hMEe : e.onLine ME) :
    |(e─m)| + |(m─d)| > |(e─d)| := by
  have hmAG : m.onLine AG := by euclid_finish
  have hne_ed : e ≠ d := by intro h; rw [h] at he; exact hdnot he
  have hne_em : e ≠ m := by euclid_finish
  -- e ≠ g: if e = g then ∠ g:m:d = 0 (degenerate, since between d g m)
  -- but hang gives ∠ e:m:d > ∠ f:m:d ≥ 0, so ∠ g:m:d > 0. Contradiction.
  have hne_eg : e ≠ g := by
    intro heq
    have hzero : ∠ g:m:d = 0 := by euclid_finish
    have hang' : ∠ g:m:d > ∠ f:m:d := heq ▸ hang
    linarith [(angle_range (Angle.ofPoints f m d)).1]
  -- e not on AG: e is on the circle; the only circle points on AG are a and g;
  -- e ≠ a and e ≠ g → e ∉ line AG
  have heoffAG : ¬e.onLine AG := by
    intro heAG
    have hre : |(m─e)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : e = g ∨ e = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_eg rfl
    · exact hne_ea rfl
  have hne_meAG : ME ≠ AG := by euclid_finish
  euclid_apply (line_from_points e d) as ED
  have hformTri : formTriangle m e d ME ED AG := by euclid_finish
  euclid_apply (Elements.Book1.proposition_20 m e d ME ED AG)
  euclid_finish

end Elements.Book3
