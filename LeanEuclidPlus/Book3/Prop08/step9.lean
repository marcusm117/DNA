import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step9 (ABC : Circle) (m f c d g a : Point) (MF MC AG : Line)
    (hm : m.isCentre ABC) (hf : f.onCircle ABC) (hc : c.onCircle ABC)
    (ha : a.onCircle ABC) (hg : g.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_fa : f ≠ a) (hne_ca : c ≠ a) (hne_cg : c ≠ g)
    (hang_fc : ∠ f:m:d > ∠ c:m:d)
    (hMFm : m.onLine MF) (hMFf : f.onLine MF)
    (hMCm : m.onLine MC) (hMCc : c.onLine MC) :
    |(d─f)| > |(d─c)| := by
  have hmAG : m.onLine AG := by euclid_finish
  have hne_fd : f ≠ d := by intro h; exact hdnot (h ▸ hf)
  have hne_cd : c ≠ d := by intro h; exact hdnot (h ▸ hc)
  have hne_fm : f ≠ m := by euclid_finish
  have hne_cm : c ≠ m := by euclid_finish
  have hne_fg : f ≠ g := by
    intro heq
    have hzero : ∠ g:m:d = 0 := by euclid_finish
    have hang' : ∠ g:m:d > ∠ c:m:d := heq ▸ hang_fc
    linarith [(angle_range (Angle.ofPoints c m d)).1]
  have hfoffAG : ¬f.onLine AG := by
    intro hfAG
    have hrf : |(m─f)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : f = g ∨ f = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_fg rfl
    · exact hne_fa rfl
  have hcoffAG : ¬c.onLine AG := by
    intro hcAG
    have hrc : |(m─c)| = |(m─a)| := by euclid_finish
    have hrg : |(m─g)| = |(m─a)| := by euclid_finish
    have heq : c = g ∨ c = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_cg rfl
    · exact hne_ca rfl
  euclid_apply (line_from_points f d) as FD
  euclid_apply (line_from_points c d) as CD
  have hformTri1 : formTriangle m f d MF FD AG := by euclid_finish
  have hformTri2 : formTriangle m c d MC CD AG := by euclid_finish
  have hfc_radii : |(m─f)| = |(m─c)| := by euclid_finish
  have h24 := Elements.Book1.proposition_24 m f d m c d MF FD AG MC CD AG
    ⟨hformTri1, hformTri2, hfc_radii, rfl, hang_fc⟩
  euclid_finish

end Elements.Book3
