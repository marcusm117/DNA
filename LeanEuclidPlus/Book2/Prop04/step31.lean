import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31: the four figures HF, CK, AG, GE tile the whole square ADEB. Cut ADEB by the vertical CF
   (sum_parallelograms_area, cut a-c-b / d-f-e) into left ADFC and right CFEB; then cut each by the
   horizontal HK — ADFC at a-h-d / c-g-f, CFEB at c-g-f / b-k-e. The three equations telescope. -/
set_option systemE.solverTime 30 in
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
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  have step15_ande : ¬(a.onLine DE) := by sorry
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  have step25_cab : c.onLine AB := by sorry
  have step9_cnbe : ¬(c.onLine BE) := by sorry
  -- h ≠ d (h ∈ HK, d ∉ HK) for step22_hnde
  have hABHK0 : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hgd0 : g ≠ d := by euclid_finish
  have step15_bnhk : ¬(b.onLine HK) := by sorry
  have step22_dnhk : ¬(d.onLine HK) := by sorry
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step22_hnde : ¬(h.onLine DE) := by sorry
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
  have step9_cfbe : ¬(CF.intersectsLine BE) := by sorry
  have step22_hkde : ¬(HK.intersectsLine DE) := by sorry
  have step25_bead : ¬(BE.intersectsLine AD) := by sorry
  have step25_abde : ¬(AB.intersectsLine DE) := by sorry
  -- distinctness of foot/corner points
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  have step25_gnbe : ¬(g.onLine BE) := by sorry
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
  have step31_adbe : a.sameSide d BE := by sorry
  have step31_acde : a.sameSide c DE := by sorry
  have step31_cbde : c.sameSide b DE := by sorry
  -- the three parallelograms
  have step31_par1 : formParallelogram a b d e AB DE AD BE := by sorry
  have step31_par2a : formParallelogram a d c f AD CF AB DE := by sorry
  have step31_par2b : formParallelogram c f b e CF BE AB DE := by sorry
  -- betweennesses for the cuts
  have hef : e ≠ f := hfe.symm
  have step22_adcf : a.sameSide d CF := by sorry
  have step22_becf : b.sameSide e CF := by sorry
  have step22_dfe : between d f e := by sorry
  have step22_anhk : ¬(a.onLine HK) := by sorry
  have step22_abshk : a.sameSide b HK := by sorry
  have step22_ahd : between a h d := by sorry
  have step15_bke : between b k e := by sorry
  have step31_csb : c.sameSide b HK := by sorry
  have step31_fsd : f.sameSide d HK := by sorry
  have step31_cfhk : ¬(c.sameSide f HK) := by sorry
  have step31_cgf : between c g f := by sorry
  -- telescope the three rectangle decompositions
  euclid_apply (sum_parallelograms_area a b d e c f AB DE AD BE)
  euclid_apply (sum_parallelograms_area a d c f h g AD CF AB DE)
  euclid_apply (sum_parallelograms_area c f b e g k CF BE AB DE)
  euclid_finish

end Elements.Book2
