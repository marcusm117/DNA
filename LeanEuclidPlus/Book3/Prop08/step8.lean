import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step8 (ABC : Circle) (m e f c d g a : Point) (ME MF AG : Line)
    (hm : m.isCentre ABC) (he : e.onCircle ABC) (hf : f.onCircle ABC)
    (ha : a.onCircle ABC) (hg : g.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_ea : e ≠ a) (hne_fa : f ≠ a)
    (hstep6_a1 : |(m─e)| = |(m─f)|)
    (hstep7 : ∠ e:m:d > ∠ f:m:d)
    (hang_fc : ∠ f:m:d > ∠ c:m:d)
    (hMEm : m.onLine ME) (hMEe : e.onLine ME)
    (hMFm : m.onLine MF) (hMFf : f.onLine MF) :
    |(d─e)| > |(d─f)| := by
  have hmAG : m.onLine AG := by euclid_finish
  have hne_ed : e ≠ d := by intro h; rw [h] at he; exact hdnot he
  have hne_fd : f ≠ d := by intro h; exact hdnot (h ▸ hf)
  have hne_em : e ≠ m := by euclid_finish
  have hne_fm : f ≠ m := by euclid_finish
  have hne_eg : e ≠ g := by
    intro heq
    have hzero : ∠ g:m:d = 0 := by euclid_finish
    have hang' : ∠ g:m:d > ∠ f:m:d := heq ▸ hstep7
    linarith [(angle_range (Angle.ofPoints f m d)).1]
  have hne_fg : f ≠ g := by
    intro heq
    have hzero : ∠ g:m:d = 0 := by euclid_finish
    have hang' : ∠ g:m:d > ∠ c:m:d := heq ▸ hang_fc
    linarith [(angle_range (Angle.ofPoints c m d)).1]
  have heoffAG : ¬e.onLine AG := by
    intro heAG
    have hre : |(m─e)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : e = g ∨ e = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_eg rfl
    · exact hne_ea rfl
  have hfoffAG : ¬f.onLine AG := by
    intro hfAG
    have hrf : |(m─f)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : f = g ∨ f = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_fg rfl
    · exact hne_fa rfl
  euclid_apply (line_from_points e d) as ED
  euclid_apply (line_from_points f d) as FD
  have hformTri1 : formTriangle m e d ME ED AG := by euclid_finish
  have hformTri2 : formTriangle m f d MF FD AG := by euclid_finish
  have hconj24 : formTriangle m e d ME ED AG ∧ formTriangle m f d MF FD AG ∧
      |(m─e)| = |(m─f)| ∧ |(m─d)| = |(m─d)| ∧ ∠e:m:d > ∠f:m:d :=
    ⟨hformTri1, hformTri2, hstep6_a1, rfl, hstep7⟩
  euclid_apply (Elements.Book1.proposition_24 m e d m f d ME ED AG MF FD AG)
  euclid_finish

end Elements.Book3
