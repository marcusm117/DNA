import SystemE
import Book1Variants.Prop34
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step15_ande
import Book2.Prop04.step15_bnhk
import Book2.Prop04.step22_anhk
import Book2.Prop04.step22_dnhk
import Book2.Prop04.step22_abshk
import Book2.Prop04.step22_ahd
import Book2.Prop04.step9_cnbe
import Book2.Prop04.step9_cfbe
import Book2.Prop04.step22_hnde
import Book2.Prop04.step22_ahcf
import Book2.Prop04.step22_hsd
import Book2.Prop04.step22_adcf
import Book2.Prop04.step22_hkde
import Book2.Prop04.step22_becf
import Book2.Prop04.step22_gf
import Book2.Prop04.step22_dfe
import Book2.Prop04.step22_adni
import Book2.Prop04.step22_acgh
import Book2.Prop04.step22_par
import Book2.Prop04.step22_eq
import Book2.Prop04.step22_fdh
import Book2.Prop04.step22_ra
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22: "So, for the same (reasons), HF is also a square." HGFD (sides h─g on HK, g─f on CF,
   f─d on DE, d─h on AD) is a square. It is a parallelogram (step22_par) so |h─g| = |f─d| and
   |g─f| = |d─h|, with right angles (rectangle). Equilateral: from the rectangle ACGH (step22_acgh)
   |a─c| = |h─g| and |a─h| = |c─g|; with |c─g| = |c─b| (CGKB equilateral / step8) and the
   collinear sums |a─d| = |a─h| + |h─d| (a-h-d) and |a─b| = |a─c| + |c─b| (a-c-b) plus
   |a─d| = |a─b| (square side), we get |d─h| = |a─c| = |h─g|, so all four sides are equal. -/
theorem helper_2_4_step22 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep8 : |(b─c)| = |(c─g)|) :
    (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)) := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hda : d ≠ a := fun h => had h.symm
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ hcAB)
  have step15_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_4_step15_ande a d AB DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have hgd : g ≠ d := by euclid_finish
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  -- off-HK points (a, b, d) for the foot betweenness a-h-d
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_anhk : ¬(a.onLine HK) := by euclid_apply (helper_2_4_step22_anhk a g AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show ¬(b.onLine HK); assumption)))
  have step22_abshk : a.sameSide b HK := by euclid_apply (helper_2_4_step22_abshk a b AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  -- foot betweenness on AD
  have step22_ahd : between a h d := by euclid_apply (helper_2_4_step22_ahd a b d g h AD HK BD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show ¬(a.onLine HK); assumption)) (by euclid_assumption "" (show ¬(d.onLine HK); assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a.sameSide b HK; assumption)))
  have hhd : h ≠ d := by euclid_finish
  -- line distinctness for the sameSide derivations
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hBEAD : BE ≠ AD := fun hh => step9_anbe (hh ▸ haAD)
  have step9_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_4_step9_cnbe a b c AB BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬(a.onLine BE); assumption)))
  have hCFBE : CF ≠ BE := fun hh => step9_cnbe (hh ▸ hcCF)
  have hBECF : BE ≠ CF := fun hh => hCFBE hh.symm
  have step9_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_4_step9_cfbe CF AD BE (by euclid_assumption "" (show CF ≠ BE; assumption)) (by euclid_assumption "" (show BE ≠ AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  -- distinctness among the horizontals/base for HK ∥ DE
  have hDEAB' : DE ≠ AB := fun hh => step8_dnab (hh ▸ hdDE)
  have step22_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_4_step22_hnde a d h AD DE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h ≠ d; assumption)) (by euclid_assumption "" (show ¬(a.onLine DE); assumption)))
  have hHKDE : HK ≠ DE := fun hh => step22_hnde (hh ▸ hhHK)
  -- sameSide facts (all "two points on a line ∥ CF") — reuse step22_ahcf
  have step22_ahcf : a.sameSide h CF := by euclid_apply (helper_2_4_step22_ahcf a h AD CF (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_hsd : h.sameSide d CF := by euclid_apply (helper_2_4_step22_hsd h d AD CF (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_adcf : a.sameSide d CF := by euclid_apply (helper_2_4_step22_adcf a d AD CF (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_hkde : ¬(HK.intersectsLine DE) := by euclid_apply (helper_2_4_step22_hkde HK DE AB (by euclid_assumption "" (show HK ≠ DE; assumption)) (by euclid_assumption "" (show DE ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have step22_becf : b.sameSide e CF := by euclid_apply (helper_2_4_step22_becf b e BE CF (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show BE ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine BE); assumption)))
  have step22_gf : g ≠ f := by euclid_apply (helper_2_4_step22_gf g f HK DE (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show HK ≠ DE; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine DE); assumption)))
  -- d ≠ f, e ≠ f (d ∈ AD, e ∈ BE, both ∥ CF; f ∈ CF)
  have hdnCF : ¬(d.onLine CF) := by
    intro hdCF; euclid_apply (intersection_lines_common_point d CF AD); euclid_finish
  have hdf : d ≠ f := fun hh => hdnCF (hh ▸ hfCF)
  have henCF : ¬(e.onLine CF) := by
    intro heCF; euclid_apply (intersection_lines_common_point e CF BE); euclid_finish
  have hef : e ≠ f := fun hh => henCF (hh ▸ hfCF)
  -- foot betweenness on DE (uses the sameSide facts above)
  have step22_dfe : between d f e := by euclid_apply (helper_2_4_step22_dfe a b c d e f DE CF AB AD BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show a.sameSide d CF; assumption)) (by euclid_assumption "" (show b.sameSide e CF; assumption)))
  -- the two parallelograms, the equilateral, the corner angle, the right angles
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_acgh : |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by euclid_apply (helper_2_4_step22_acgh a c g h AB HK AD CF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine CF); assumption)) (by euclid_assumption "" (show a.sameSide h CF; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)))
  have hacng : |(a─c)| = |(h─g)| := step22_acgh.1
  have hahcg : |(a─h)| = |(c─g)| := step22_acgh.2
  have step22_par : formParallelogram h g d f HK DE AD CF := by euclid_apply (helper_2_4_step22_par h g f d HK DE AD CF (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine DE); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine CF); assumption)) (by euclid_assumption "" (show h.sameSide d CF; assumption)) (by euclid_assumption "" (show g ≠ f; assumption)))
  have step22_eq : |(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)| := by euclid_apply (helper_2_4_step22_eq a b c d f g h HK DE AD CF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show formParallelogram h g d f HK DE AD CF; assumption)) (by euclid_assumption "" (show |(a─c)| = |(h─g)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(c─g)|; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─c)| = |(c─g)|; assumption)))
  have step22_fdh : ∠ f:d:h = ∟ := by euclid_apply (helper_2_4_step22_fdh a d e f h DE AD (by euclid_assumption "" (show between d f e; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)))
  have step22_ra : (∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟) := by euclid_apply (helper_2_4_step22_ra h g f d HK DE AD CF (by euclid_assumption "" (show formParallelogram h g d f HK DE AD CF; assumption)) (by euclid_assumption "" (show ∠ f:d:h = ∟; assumption)))
  exact ⟨step22_eq, step22_ra⟩

end Elements.Book2
