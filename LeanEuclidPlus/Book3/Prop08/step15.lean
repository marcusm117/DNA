import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |MK| = |ML| (equal radii), ∠KMD < ∠LMD, so by Prop I.24: |KD| < |LD|
-- Then linarith: |MK| + |KD| < |ML| + |LD|
-- No by_cases needed — proposition_24 is direct.
set_option systemE.solverTime 30 in
theorem helper_3_8_step15
    (ABC : Circle) (m k l d : Point) (MK ML LD AG : Line)
    (hm : m.isCentre ABC)
    (hdnotCircle : ¬d.onCircle ABC)
    (hk : k.onCircle ABC) (hl : l.onCircle ABC)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK)
    (hangle_kl : ∠k:m:d < ∠l:m:d)
    (hassump1 : formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG) :
    |(m─k)| + |(k─d)| < |(m─l)| + |(l─d)| := by
  have hft := hassump1.1
  have hmAG : m.onLine AG := hft.2.2.2.2.1
  have hdAG : d.onLine AG := hft.2.2.2.1
  -- |m─k| = |m─l| (both radii)
  have hradius : |(m─l)| = |(m─k)| := point_on_circle_onlyif m k l ABC ⟨hm, hk, hl⟩
  -- k ≠ d (k on circle, d not)
  have hne_kd : k ≠ d := by euclid_finish
  -- k is off AG (from l.sameSide k AG → k.sameSide l AG → ¬k.onLine AG)
  have hkoffAG : ¬k.onLine AG :=
    same_side_not_on_line k l AG (same_side_symm l k AG hassump1.2.2)
  -- m ≠ k, m ≠ d for formTriangle
  have hne_mk : m ≠ k := by euclid_finish
  have hne_md : m ≠ d := by euclid_finish
  -- Introduce line KD
  obtain ⟨KD, hkKD, hdKD⟩ := line_from_points k d hne_kd
  -- formTriangle m k d MK KD AG
  have hft2 : formTriangle m k d MK KD AG := by euclid_finish
  -- Prop I.24: equal sides (|ML|=|MK|, |MD|=|MD|), greater angle ∠LMD > ∠KMD → |LD| > |KD|
  have hangle_gt : ∠l:m:d > ∠k:m:d := by linarith
  have hconj24 : formTriangle m l d ML LD AG ∧ formTriangle m k d MK KD AG ∧
      |(m─l)| = |(m─k)| ∧ |(m─d)| = |(m─d)| ∧ ∠l:m:d > ∠k:m:d :=
    ⟨hft, hft2, hradius, rfl, hangle_gt⟩
  euclid_apply (Elements.Book1.proposition_24 m l d m k d ML LD AG MK KD AG)
  linarith [hradius]

end Elements.Book3
