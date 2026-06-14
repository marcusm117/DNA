import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.24: the squares HF and KC are on AC and CB — area(HGFD) = |a─c|² and area(CGKB) = |c─b|².
   The second is step21. The first is step24_hf (rectangle_area on the parallelogram HGFD with side
   |h─g| = |a─c|), for which the HGFD parallelogram (step22_par) is re-derived from the figure. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step24 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
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
    (hstep8 : |(b─c)| = |(c─g)|)
    (hstep21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)
    (hstep22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)))
    (hstep23 : |(h─g)| = |(a─c)|) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by
  euclid_intros
  -- re-derive the HGFD parallelogram (same preamble as step22)
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ hcAB)
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hgd : g ≠ d := by euclid_finish
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have step15_bnhk : ¬(b.onLine HK) := by sorry
  have step22_anhk : ¬(a.onLine HK) := by sorry
  have step22_dnhk : ¬(d.onLine HK) := by sorry
  have step22_abshk : a.sameSide b HK := by sorry
  have step22_ahd : between a h d := by sorry
  have step22_hsd : h.sameSide d CF := by sorry
  -- HK ∥ DE preamble: h ∉ DE ⟹ HK ≠ DE; d ∉ AB ⟹ DE ≠ AB
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step15_ande : ¬(a.onLine DE) := by sorry
  have step22_hnde : ¬(h.onLine DE) := by sorry
  have hHKDE : HK ≠ DE := fun hh => step22_hnde (hh ▸ hhHK)
  have hDEAB' : DE ≠ AB := fun hh => step8_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have step22_hkde : ¬(HK.intersectsLine DE) := by sorry
  have step22_gf : g ≠ f := by sorry
  have step22_adni : ¬(AD.intersectsLine CF) := by sorry
  have step22_par : formParallelogram h g d f HK DE AD CF := by sorry
  -- d ≠ f, d ≠ h for the rectangle's corner angle (sides are positive: |a─c| > 0)
  have hac : a ≠ c := by euclid_finish
  have hdh : d ≠ h := by euclid_finish
  have hdf : d ≠ f := by euclid_finish
  -- the two square areas
  have step24_hf : Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)| := by sorry
  exact ⟨step24_hf, hstep21⟩

end Elements.Book2
