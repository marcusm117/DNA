import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |a─d| > |d─g| via I.19: in triangle d-g-a, ∠d:g:a=∟ > ∠g:a:d<∟ → side |d─a| > |d─g|.
theorem helper_3_16_step15
    (a g d : Point) (ABC : Circle) (FA : Line)
    (left : d.isCentre ABC)
    (hFAon : a.onLine FA)
    (hgFA : g.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (hagne : a ≠ g)
    (hassump1 : ∠ a:g:d = ∟)
    (hassump2 : ∠ d:a:g < ∟)
    : |(a─d)| > |(d─g)| := by
  have hd_off : ¬d.onLine FA := fun hd_on =>
    hFAnot (intersection_circle_line_2 d ABC FA ⟨center_inside_circle d ABC left, hd_on⟩)
  have hda : d ≠ a := fun h => hd_off (h ▸ hFAon)
  have hdg : d ≠ g := fun h => hd_off (h ▸ hgFA)
  obtain ⟨DG, hDGd, hDGg⟩ := line_from_points d g hdg
  obtain ⟨GA, hGAg, hGAa⟩ := line_from_points g a hagne.symm
  obtain ⟨DA, hDAd, hDAa⟩ := line_from_points d a hda
  have htri : formTriangle d g a DG GA DA := by euclid_finish
  -- ∠d:g:a = ∠a:g:d = ∟ (angle_symm at vertex g: angle_symm d g a)
  have h_dga : ∠ d:g:a = ∠ a:g:d := angle_symm d g a ⟨hdg, hagne.symm⟩
  -- ∠g:a:d = ∠d:a:g (angle_symm at vertex a: angle_symm g a d)
  have h_gad : ∠ g:a:d = ∠ d:a:g := angle_symm g a d ⟨hagne.symm, hda.symm⟩
  have hineq : ∠ d:g:a > ∠ g:a:d := by linarith
  have h19 : |(d─a)| > |(d─g)| := by
    euclid_apply (Elements.Book1.proposition_19 d g a DG GA DA ⟨htri, hineq⟩)
  -- h19 : |(d─a)| > |(d─g)|; need |(a─d)| > |(d─g)|
  linarith [segment_symmetric d a]

end Elements.Book3
