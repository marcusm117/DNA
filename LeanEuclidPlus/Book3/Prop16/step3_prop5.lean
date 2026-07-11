import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_16_step3_prop5
    (d a c : Point) (DC : Line)
    (hda : d ≠ a)
    (hdc : d ≠ c)
    (hcne : c ≠ a)
    (hDCd : d.onLine DC)
    (hDCc : c.onLine DC)
    (hassump1 : |(d─a)| = |(d─c)|)
    : ∠ d:a:c = ∠ d:c:a := by
  obtain ⟨DA, hDAd, hDAa⟩ := line_from_points d a hda
  obtain ⟨AC, hACa, hACc⟩ := line_from_points a c hcne.symm
  have htri : formTriangle d a c DA AC DC := by euclid_finish
  obtain ⟨b', hb'DA, hbet_b'⟩ := extend_point DA d a ⟨hDAd, hDAa, hda⟩
  obtain ⟨c'', hc''DC, hbet_c''⟩ := extend_point DC d c ⟨hDCd, hDCc, hdc⟩
  euclid_apply (Elements.Book1.proposition_5 d a c b' c'' DA AC DC
    ⟨htri, hassump1, hbet_b', hbet_c''⟩)

end Elements.Book3
