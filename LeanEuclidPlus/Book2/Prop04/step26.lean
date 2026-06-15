import SystemE
import Book.Prop34
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step25_cab
import Book2.Prop04.step22_ahcf
import Book2.Prop04.step22_adni
import Book2.Prop04.step25_paracgh
import Book2.Prop04.step22_acgh
import Book2.Prop04.step26_bnad
import Book2.Prop04.step26_gnad
import Book2.Prop04.step15_bnhk
import Book2.Prop04.step22_anhk
import Book2.Prop04.step22_dnhk
import Book2.Prop04.step22_abshk
import Book2.Prop04.step22_ahd
import Book2.Prop04.step26_gh
import Book2.Prop04.step26_bsg
import Book2.Prop04.step26_ahg
import Book2.Prop04.step26_area
import Book2.Prop04.step26_close
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.26: AG is the rectangle on AC and CB — area(ACGH) = |a─c|·|c─b|. ACGH is a parallelogram
   (step25_paracgh) with right angle at h, ∠ a:h:g = ∟ (AD ⊥ HK); rectangle_area gives its area
   (△a:h:g + △a:g:c) = |a─c|·|a─h|; with |a─h| = |c─g| (ACGH, step22_acgh) and |c─g| = |b─c| (step8),
   this is |a─c|·|c─b|. -/
theorem helper_2_4_step26 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) (hstep8 : |(b─c)| = |(c─g)|) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)| := by
  euclid_intros
  -- preamble for the ACGH rectangle
  have had : a ≠ d := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_cab : c.onLine AB := by euclid_apply (helper_2_4_step25_cab a b c AB (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have step22_ahcf : a.sameSide h CF := by euclid_apply (helper_2_4_step22_ahcf a h AD CF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by assumption)); (try split_ands) <;> assumption
  have step25_paracgh : formParallelogram a c h g AB HK AD CF := by euclid_apply (helper_2_4_step25_paracgh a c h g AB HK AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_acgh : |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by euclid_apply (helper_2_4_step22_acgh a c g h AB HK AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- g ∉ AD (g ∈ BD, d ∈ AD∩BD, g ≠ d ⟹ AD=BD ⟹ b ∈ AD, but b ∉ AD)
  have hgd : g ≠ d := by euclid_finish
  have step26_bnad : ¬(b.onLine AD) := by euclid_apply (helper_2_4_step26_bnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step26_gnad : ¬(g.onLine AD) := by euclid_apply (helper_2_4_step26_gnad b d g AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_anhk : ¬(a.onLine HK) := by euclid_apply (helper_2_4_step22_anhk a g AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_abshk : a.sameSide b HK := by euclid_apply (helper_2_4_step22_abshk a b AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_ahd : between a h d := by euclid_apply (helper_2_4_step22_ahd a b d g h AD HK BD AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step26_gh : g ≠ h := by euclid_apply (helper_2_4_step26_gh g h c CF AD (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step26_bsg : b.sameSide g AD := by euclid_apply (helper_2_4_step26_bsg b d g AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the right angle at h and the rectangle area
  have step26_ahg : ∠ a:h:g = ∟ := by euclid_apply (helper_2_4_step26_ahg a b d g h AB AD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step26_area : Triangle.area △ a:h:g + Triangle.area △ a:g:c = |(a─c)| * |(a─h)| := by euclid_apply (helper_2_4_step26_area a c h g AB HK AD CF (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hahcg : |(a─h)| = |(c─g)| := step22_acgh.2
  have step26_close : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)| := by euclid_apply (helper_2_4_step26_close a b c g h (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  exact step26_close

end Elements.Book2
