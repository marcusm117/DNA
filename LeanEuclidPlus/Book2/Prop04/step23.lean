import SystemE
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step22_ahcf
import Book2.Prop04.step22_adni
import Book2.Prop04.step22_acgh
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.23: the square HF is on HG, that is AC — |h─g| = |a─c|. ACGH is a parallelogram (step22_acgh),
   so |a─c| = |h─g| (its top and bottom sides), giving the claim. -/
theorem helper_2_4_step23 (a b c d g h : Point) (AB CF AD BD HK : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK)
    (hHKAB : ¬(HK.intersectsLine AB)) (hCFAD : ¬(CF.intersectsLine AD))
    (hab : a ≠ b) (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟) :
    |(h─g)| = |(a─c)| := by
  euclid_intros
  -- preamble: off-line roots for the rectangle ACGH
  have had : a ≠ d := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ hcAB)
  have step22_ahcf : a.sameSide h CF := by euclid_apply (helper_2_4_step22_ahcf a h AD CF (by assumption) (by assumption) (by assumption) (by assumption))
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by assumption))
  -- ACGH rectangle: |a─c| = |h─g|
  have step22_acgh : |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by euclid_apply (helper_2_4_step22_acgh a c g h AB HK AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_finish

end Elements.Book2
