import SystemE
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step15_ande
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step25_cab
import Book2.Prop04.step9_cnbe
import Book2.Prop04.step15_bnhk
import Book2.Prop04.step22_dnhk
import Book2.Prop04.step22_hnde
import Book2.Prop04.step9_cfbe
import Book2.Prop04.step22_hkde
import Book2.Prop04.step25_bead
import Book2.Prop04.step25_abde
import Book2.Prop04.step25_gnbe
import Book2.Prop04.step31_adbe
import Book2.Prop04.step31_acde
import Book2.Prop04.step31_cbde
import Book2.Prop04.step31_par1
import Book2.Prop04.step31_par2a
import Book2.Prop04.step31_par2b
import Book2.Prop04.step22_adcf
import Book2.Prop04.step22_becf
import Book2.Prop04.step22_dfe
import Book2.Prop04.step22_anhk
import Book2.Prop04.step22_abshk
import Book2.Prop04.step22_ahd
import Book2.Prop04.step15_bke
import Book2.Prop04.step31_csb
import Book2.Prop04.step31_fsd
import Book2.Prop04.step31_cfhk
import Book2.Prop04.step31_cgf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31: the four figures HF, CK, AG, GE tile the whole square ADEB. Cut ADEB by the vertical CF
   (sum_parallelograms_area, cut a-c-b / d-f-e) into left ADFC and right CFEB; then cut each by the
   horizontal HK — ADFC at a-h-d / c-g-f, CFEB at c-g-f / b-k-e. The three equations telescope. -/
theorem helper_2_4_step31 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
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
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
      + (Triangle.area △ c:g:k + Triangle.area △ c:k:b)
      + (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b := by
  euclid_intros
  -- off-line roots and distinctness
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have step15_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_4_step15_ande a d AB DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  have step25_cab : c.onLine AB := by euclid_apply (helper_2_4_step25_cab a b c AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))
  have step9_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_4_step9_cnbe a b c AB BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬(a.onLine BE); assumption)))
  -- h ≠ d (h ∈ HK, d ∉ HK) for step22_hnde
  have hABHK0 : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hgd0 : g ≠ d := by euclid_finish
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show ¬(b.onLine HK); assumption)))
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step22_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_4_step22_hnde a d h AD DE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h ≠ d; assumption)) (by euclid_assumption "" (show ¬(a.onLine DE); assumption)))
  -- line distinctness
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hBEAD : BE ≠ AD := fun hh => step9_anbe (hh ▸ haAD)
  have hADBE2 : AD ≠ BE := fun hh => hBEAD hh.symm
  have hCFBE : CF ≠ BE := fun hh => step9_cnbe (hh ▸ hcCF)
  have hBECF : BE ≠ CF := fun hh => hCFBE hh.symm
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hABDE2 : AB ≠ DE := fun hh => step8_dnab (hh ▸ hdDE)
  have hDEAB' : DE ≠ AB := fun hh => hABDE2 hh.symm
  have hDEHK : DE ≠ HK := fun hh => step22_hnde (hh ▸ hhHK)
  have hHKDE : HK ≠ DE := fun hh => hDEHK hh.symm
  -- non-intersections + symmetric orientations
  have step9_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_4_step9_cfbe CF AD BE (by euclid_assumption "" (show CF ≠ BE; assumption)) (by euclid_assumption "" (show BE ≠ AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step22_hkde : ¬(HK.intersectsLine DE) := by euclid_apply (helper_2_4_step22_hkde HK DE AB (by euclid_assumption "" (show HK ≠ DE; assumption)) (by euclid_assumption "" (show DE ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have step25_bead : ¬(BE.intersectsLine AD) := by euclid_apply (helper_2_4_step25_bead AD BE (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step25_abde : ¬(AB.intersectsLine DE) := by euclid_apply (helper_2_4_step25_abde AB DE (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  -- distinctness of foot/corner points
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  have step25_gnbe : ¬(g.onLine BE) := by euclid_apply (helper_2_4_step25_gnbe g CF BE (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show CF ≠ BE; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine BE); assumption)))
  have hgd : g ≠ d := by euclid_finish
  -- more distinctness for the cuts and cgf
  have hbe2 : b ≠ e := heb.symm
  have hfe : f ≠ e := by euclid_finish
  have hdf : d ≠ f := by euclid_finish
  have hgnDE : ¬(g.onLine DE) := by
    intro hgDE; euclid_apply (intersection_lines_common_point g HK DE); euclid_finish
  have hfg : f ≠ g := fun hh => hgnDE (hh ▸ hfDE)
  have step31_cnDE : ¬(c.onLine DE) := by
    intro hcDE; euclid_apply (intersection_lines_common_point c AB DE); euclid_finish
  have hcf : c ≠ f := fun hh => step31_cnDE (hh ▸ hfDE)
  have hcnHK : ¬(c.onLine HK) := by
    intro hcHK; euclid_apply (intersection_lines_common_point c AB HK); euclid_finish
  have hHKCF : HK ≠ CF := fun hh => hcnHK (hh ▸ hcCF)
  -- the sameSide facts for the three parallelograms
  have step31_adbe : a.sameSide d BE := by euclid_apply (helper_2_4_step31_adbe a d AD BE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ BE; assumption)) (by euclid_assumption "" (show ¬(BE.intersectsLine AD); assumption)))
  have step31_acde : a.sameSide c DE := by euclid_apply (helper_2_4_step31_acde a c AB DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ DE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have step31_cbde : c.sameSide b DE := by euclid_apply (helper_2_4_step31_cbde c b AB DE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ DE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  -- the three parallelograms
  have step31_par1 : formParallelogram a b d e AB DE AD BE := by euclid_apply (helper_2_4_step31_par1 a b d e AB DE AD BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine DE); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show a.sameSide d BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)))
  have step31_par2a : formParallelogram a d c f AD CF AB DE := by euclid_apply (helper_2_4_step31_par2a a d c f AD CF AB DE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine DE); assumption)) (by euclid_assumption "" (show a.sameSide c DE; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)))
  have step31_par2b : formParallelogram c f b e CF BE AB DE := by euclid_apply (helper_2_4_step31_par2b c f b e CF BE AB DE (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine DE); assumption)) (by euclid_assumption "" (show c.sameSide b DE; assumption)) (by euclid_assumption "" (show f ≠ e; assumption)))
  -- betweennesses for the cuts
  have hef : e ≠ f := hfe.symm
  have step22_adcf : a.sameSide d CF := by euclid_apply (helper_2_4_step22_adcf a d AD CF (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step22_becf : b.sameSide e CF := by euclid_apply (helper_2_4_step22_becf b e BE CF (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show BE ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine BE); assumption)))
  have step22_dfe : between d f e := by euclid_apply (helper_2_4_step22_dfe a b c d e f DE CF AB AD BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show a.sameSide d CF; assumption)) (by euclid_assumption "" (show b.sameSide e CF; assumption)))
  have step22_anhk : ¬(a.onLine HK) := by euclid_apply (helper_2_4_step22_anhk a g AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_abshk : a.sameSide b HK := by euclid_apply (helper_2_4_step22_abshk a b AB HK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step22_ahd : between a h d := by euclid_apply (helper_2_4_step22_ahd a b d g h AD HK BD AB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show ¬(a.onLine HK); assumption)) (by euclid_assumption "" (show ¬(d.onLine HK); assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a.sameSide b HK; assumption)))
  have step15_bke : between b k e := by euclid_apply (helper_2_4_step15_bke a b d e g k BE HK DE BD AB CF AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show k.onLine BE; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  have step31_csb : c.sameSide b HK := by euclid_apply (helper_2_4_step31_csb c b AB HK (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AB ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have step31_fsd : f.sameSide d HK := by euclid_apply (helper_2_4_step31_fsd f d DE HK (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show DE ≠ HK; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine DE); assumption)))
  have step31_cfhk : ¬(c.sameSide f HK) := by euclid_apply (helper_2_4_step31_cfhk b c d f g HK BD (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show c.sameSide b HK; assumption)) (by euclid_assumption "" (show f.sameSide d HK; assumption)))
  have step31_cgf : between c g f := by euclid_apply (helper_2_4_step31_cgf c f g CF HK (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)) (by euclid_assumption "" (show HK ≠ CF; assumption)) (by euclid_assumption "" (show ¬(c.sameSide f HK); assumption)))
  -- telescope the three rectangle decompositions
  euclid_apply (sum_parallelograms_area a b d e c f AB DE AD BE)
  euclid_apply (sum_parallelograms_area a d c f h g AD CF AB DE)
  euclid_apply (sum_parallelograms_area c f b e g k CF BE AB DE)
  euclid_finish

end Elements.Book2
