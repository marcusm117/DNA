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
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  have step25_cab : c.onLine AB := by euclid_apply (helper_2_4_step25_cab a b c AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have step22_ahcf : a.sameSide h CF := by euclid_apply (helper_2_4_step22_ahcf a h AD CF (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step25_paracgh : formParallelogram a c h g AB HK AD CF := by euclid_apply (helper_2_4_step25_paracgh a c h g AB HK AD CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine CF); assumption)) (by euclid_assumption "" (show a.sameSide h CF; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)))
  have step22_acgh : |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by euclid_apply (helper_2_4_step22_acgh a c g h AB HK AD CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine CF); assumption)) (by euclid_assumption "" (show a.sameSide h CF; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)))
  -- g ∉ AD (g ∈ BD, d ∈ AD∩BD, g ≠ d ⟹ AD=BD ⟹ b ∈ AD, but b ∉ AD)
  have hgd : g ≠ d := by euclid_finish
  have step26_bnad : ¬(b.onLine AD) := by euclid_apply (helper_2_4_step26_bnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step26_gnad : ¬(g.onLine AD) := by euclid_apply (helper_2_4_step26_gnad b d g AD BD (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show ¬(b.onLine AD); assumption)))
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_anhk : ¬(a.onLine HK) := by euclid_apply (helper_2_4_step22_anhk a g AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show ¬(b.onLine HK); assumption)))
  have step22_abshk : a.sameSide b HK := by euclid_apply (helper_2_4_step22_abshk a b AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_ahd : between a h d := by euclid_apply (helper_2_4_step22_ahd a b d g h AD HK BD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show ¬(a.onLine HK); assumption)) (by euclid_assumption "" (show ¬(d.onLine HK); assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a.sameSide b HK; assumption)))
  have step26_gh : g ≠ h := by euclid_apply (helper_2_4_step26_gh g h c CF AD (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step26_bsg : b.sameSide g AD := by euclid_apply (helper_2_4_step26_bsg b d g AD BD (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show ¬(g.onLine AD); assumption)))
  -- the right angle at h and the rectangle area
  have step26_ahg : ∠ a:h:g = ∟ := by euclid_apply (helper_2_4_step26_ahg a b d g h AB AD HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show b.sameSide g AD; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step26_area : Triangle.area △ a:h:g + Triangle.area △ a:g:c = |(a─c)| * |(a─h)| := by euclid_apply (helper_2_4_step26_area a c h g AB HK AD CF (by euclid_assumption "" (show formParallelogram a c h g AB HK AD CF; assumption)) (by euclid_assumption "" (show ∠ a:h:g = ∟; assumption)))
  have hahcg : |(a─h)| = |(c─g)| := step22_acgh.2
  have step26_close : Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)| := by euclid_apply (helper_2_4_step26_close a b c g h (by euclid_assumption "" (show Triangle.area △ a:h:g + Triangle.area △ a:g:c = |(a─c)| * |(a─h)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(c─g)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(c─g)|; assumption)))
  exact step26_close

end Elements.Book2
