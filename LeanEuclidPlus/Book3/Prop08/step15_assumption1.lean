import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop08.step15_assumption1_hft
import Book3.Prop08.step15_assumption1_hss_kd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step15_assumption1 (ABC : Circle) (m k l d g a h : Point)
    (MK ML LD AG : Line)
    (hm : m.isCentre ABC) (hk : k.onCircle ABC) (hl : l.onCircle ABC)
    (hg : g.onCircle ABC) (ha : a.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_kg : k ≠ g) (hne_lg : l ≠ g)
    (hangle_kl : ∠k:m:d < ∠l:m:d)
    (hangle_lh : ∠l:m:d < ∠h:m:d)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK)
    (hMLm : m.onLine ML) (hMLl : l.onLine ML)
    (hLDl : l.onLine LD) (hLDd : d.onLine LD)
    (hss_lk : l.sameSide k AG) :
    formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG := by
  have hmAG : m.onLine AG := by euclid_finish
  have hne_ld : l ≠ d := by intro h; exact hdnot (h ▸ hl)
  have hne_lm : l ≠ m := by euclid_finish
  have hne_la : l ≠ a := by
    intro heq
    have hpi : ∠a:m:d = ∟+∟ := by euclid_finish
    have hpi_l : ∠l:m:d = ∟+∟ := heq.symm ▸ hpi
    linarith [(angle_range (Angle.ofPoints h m d)).2, hangle_lh]
  have hloffAG : ¬l.onLine AG := by
    intro hlAG
    have : |(m─l)| = |(m─a)| := by euclid_finish
    have heq : l = g ∨ l = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_lg rfl
    · exact hne_la rfl
  have hne_kd : k ≠ d := by intro h; exact hdnot (h ▸ hk)
  have hne_km : k ≠ m := by euclid_finish
  have hne_ka : k ≠ a := by
    intro heq
    have hpi : ∠a:m:d = ∟+∟ := by euclid_finish
    have hpi_k : ∠k:m:d = ∟+∟ := heq.symm ▸ hpi
    linarith [(angle_range (Angle.ofPoints h m d)).2, hangle_kl, hangle_lh]
  have hkoffAG : ¬k.onLine AG := by
    intro hkAG
    have : |(m─k)| = |(m─a)| := by euclid_finish
    have heq : k = g ∨ k = a := by euclid_finish
    rcases heq with rfl | rfl
    · exact hne_kg rfl
    · exact hne_ka rfl
  have hne_dm : m ≠ d := by euclid_finish
  have step15_assumption1_hft : formTriangle m l d ML LD AG := by euclid_apply (helper_3_8_step15_assumption1_hft m l d ML LD AG (by euclid_assumption "" (show m.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show m.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine LD; assumption)) (by euclid_assumption "" (show d.onLine LD; assumption)) (by euclid_assumption "" (show l ≠ m; assumption)) (by euclid_assumption "" (show l ≠ d; assumption)) (by euclid_assumption "" (show m ≠ d; assumption)) (by euclid_assumption "" (show ¬l.onLine AG; assumption)))
  have step15_assumption1_hss_kd : d.sameSide k ML := by euclid_apply (helper_3_8_step15_assumption1_hss_kd m k l d g a h MK ML AG (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show ∠k:m:d < ∠l:m:d; assumption)) (by euclid_assumption "" (show ∠l:m:d < ∠h:m:d; assumption)) (by euclid_assumption "" (show m.onLine MK; assumption)) (by euclid_assumption "" (show k.onLine MK; assumption)) (by euclid_assumption "" (show m.onLine ML; assumption)) (by euclid_assumption "" (show l.onLine ML; assumption)) (by euclid_assumption "" (show m.onLine AG; assumption)) (by euclid_assumption "" (show l ≠ m; assumption)) (by euclid_assumption "" (show k ≠ m; assumption)) (by euclid_assumption "" (show m ≠ d; assumption)) (by euclid_assumption "" (show ¬l.onLine AG; assumption)) (by euclid_assumption "" (show ¬k.onLine AG; assumption)) (by euclid_assumption "" (show l.sameSide k AG; assumption)))
  exact ⟨step15_assumption1_hft, step15_assumption1_hss_kd, hss_lk⟩

end Elements.Book3
