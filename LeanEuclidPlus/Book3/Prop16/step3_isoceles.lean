import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠d:a:c = ∠d:c:a by I.5 (isosceles: |d─a|=|d─c|, apex d).
theorem helper_3_16_step3_isoceles
    (d a c : Point) (DA AE DC : Line)
    (hDAd : d.onLine DA) (hDAa : a.onLine DA)
    (hDCd : d.onLine DC) (hDCc : c.onLine DC)
    (hda : d ≠ a) (hdc : d ≠ c)
    (hassump1 : |(d─a)| = |(d─c)|)
    (htri : formTriangle d a c DA AE DC)
    : ∠ d:a:c = ∠ d:c:a := by
  obtain ⟨ext1, _, hbetw1⟩ := extend_point DA d a ⟨hDAd, hDAa, hda⟩
  obtain ⟨ext2, _, hbetw2⟩ := extend_point DC d c ⟨hDCd, hDCc, hdc⟩
  have h5 : (∠ d:a:c = ∠ d:c:a) ∧ (∠ c:a:ext1 = ∠ a:c:ext2) := by
    euclid_apply (Elements.Book1.proposition_5 d a c ext1 ext2 DA AE DC
      ⟨htri, hassump1, hbetw1, hbetw2⟩)
  exact h5.1

end Elements.Book3
