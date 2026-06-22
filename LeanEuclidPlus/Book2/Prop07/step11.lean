import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11: DG (= the bottom-left square DHGN) is the square on AC — area(DHGN) = |a─c|².
   DHGN is a rectangle (step11_parDG) with the right angle ∠h:d:n = ∟ (= ∠a:d:e), so by
   rectangle_area its area is |h─d|·|h─g| (step11_rect). Its sides equal AC: |h─d| = |a─c|
   (step11_dhac, since |a─h| = |b─f| = |b─c| and |a─d| = |a─b| = |a─c|+|c─b|) and |a─c| = |h─g|
   (step11_hgac, opposite sides of rectangle ACGH). Hence area = |a─c|·|a─c|. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step11 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCNAD : ¬(CN.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(a─c)| * |(a─c)| := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by sorry
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have step3_gnab : ¬(g.onLine AB) := by sorry
  have step3_cnbe : ¬(c.onLine BE) := by sorry
  have step3_bnhf : ¬(b.onLine HF) := by sorry
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have hfb : f ≠ b := fun hh => hbf hh.symm
  have step3_cnad : ¬(c.onLine AD) := by sorry
  have step3_anbe : ¬(a.onLine BE) := by sorry
  have step3_hnde : ¬(h.onLine DE) := by sorry
  have step3_cab : c.onLine AB := by sorry
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  -- non-intersections
  have step3_cfbe : ¬(CN.intersectsLine BE) := by sorry
  have step3_hkde : ¬(HF.intersectsLine DE) := by sorry
  -- foot betweennesses
  have step8_ahd : between a h d := by sorry
  have step3_bgd_ss : a.sameSide d CN := by sorry
  have step11_dne : between d n e := by sorry
  have hgn : g ≠ n := by euclid_finish
  -- side lengths
  have step4_ahbe : a.sameSide h BE := by sorry
  have step8_hsa : h.sameSide a BE := by sorry
  have step8_parAF2 : formParallelogram h f a b HF AB AD BE := by sorry
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by sorry
  have step8_lens : |(a─b)| = |(h─f)| ∧ |(a─h)| = |(b─f)| := by sorry
  have step9_bfbc : |(b─f)| = |(b─c)| := by sorry
  have hahbc : |(a─h)| = |(b─c)| := by
    rw [step8_lens.2, step9_bfbc]
  have step11_dhac : |(d─h)| = |(a─c)| := by sorry
  -- the rectangle ACGH for |a─c| = |h─g|
  have step3_ahcf : a.sameSide h CN := by sorry
  have hcg : c ≠ g := fun hh => step3_gnab (hh ▸ step3_cab)
  have step3_paracgh : formParallelogram a c h g AB HF AD CN := by sorry
  have step11_hgac : |(a─c)| = |(h─g)| := by sorry
  -- the square DHGN and its area
  have step11_hsd : h.sameSide d CN := by sorry
  have step11_parDG : formParallelogram h g d n HF DE AD CN := by sorry
  have step11_rangle : ∠ h:d:n = ∟ := by sorry
  have step11_rect : Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(h─d)| * |(h─g)| := by sorry
  euclid_finish

end Elements.Book2
