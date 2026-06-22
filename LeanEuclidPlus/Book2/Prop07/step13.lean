import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13: the gnomon KLM and the squares BG (=CF) and GD (=DG) are equivalent to the whole square
   ADEB plus CF — the squares on AB and BC. The four pieces AG, CF, DG, GE tile ADEB (step13_tile),
   so the LHS (= AG+GE+CF+CF+DG) = ADEB + CF; with area(ADEB)=|a─b|² (step13_adeb) and area(CF)=|b─c|²
   (step13_cfbc), the LHS equals |a─b|² + |b─c|². -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step3_cnad : ¬(c.onLine AD) := by sorry
  have step3_dnab : ¬(d.onLine AB) := by sorry
  have step3_anbe : ¬(a.onLine BE) := by sorry
  have step3_ande : ¬(a.onLine DE) := by sorry
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have step3_gnab : ¬(g.onLine AB) := by sorry
  have step3_cab : c.onLine AB := by sorry
  have step3_cnbe : ¬(c.onLine BE) := by sorry
  have step3_bnhf : ¬(b.onLine HF) := by sorry
  have hgd0 : g ≠ d := by euclid_finish
  have step3_dnhf : ¬(d.onLine HF) := by sorry
  have step3_hnde : ¬(h.onLine DE) := by sorry
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  -- non-intersections
  have step3_cfbe : ¬(CN.intersectsLine BE) := by sorry
  have step3_hkde : ¬(HF.intersectsLine DE) := by sorry
  have step3_bead : ¬(BE.intersectsLine AD) := by sorry
  have step3_abde : ¬(AB.intersectsLine DE) := by sorry
  -- foot betweennesses
  have step8_ahd : between a h d := by sorry
  have step4_cgn : between c g n := by sorry
  have step3_bgd_ss : a.sameSide d CN := by sorry
  have step11_dne : between d n e := by sorry
  have step3_bke : between b f e := by sorry
  -- distinctness of cut points
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_gnbe : ¬(g.onLine BE) := by sorry
  have hne : n ≠ e := by euclid_finish
  have hgn : g ≠ n := by euclid_finish
  have hgf : g ≠ f := by euclid_finish
  have hbe : b ≠ e := heb.symm
  have hdn : d ≠ n := by euclid_finish
  -- sameSide facts for the parallelograms
  have step13_asd : a.sameSide d BE := by sorry
  have step13_asc : a.sameSide c DE := by sorry
  have step4_cbde : c.sameSide b DE := by sorry
  have step13_csb : c.sameSide b HF := by sorry
  -- the four parallelograms (whole + left + right for the tiling, CBFG for the area)
  have step11_hsd : h.sameSide d CN := by sorry
  have step13_bigpar : formParallelogram a b d e AB DE AD BE := by sorry
  have step13_parL : formParallelogram a d c n AD CN AB DE := by sorry
  have step13_parR : formParallelogram c n b e CN BE AB DE := by sorry
  have step11_parDG : formParallelogram h g d n HF DE AD CN := by sorry
  have step13_parCF2 : formParallelogram c g b f CN BE AB HF := by sorry
  -- the right angle and equilateral side for CF
  have step13_cbf : ∠ c:b:f = ∟ := by sorry
  have step9_tri : formTriangle c g b CN BD AB := by sorry
  have step9_ss : c.sameSide a BD := by sorry
  have step9_corr : ∠ c:g:b = ∠ a:d:b := by sorry
  have step9_iso : ∠ a:d:b = ∠ a:b:d := by sorry
  have step9_cgb : ∠ c:g:b = ∠ g:b:c := by sorry
  have step9_bccg : |(b─c)| = |(c─g)| := by sorry
  -- the tiling and the two square areas
  have step13_tile : (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      + (Triangle.area △ d:h:g + Triangle.area △ d:g:n)
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b := by sorry
  have step13_adeb : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)| := by sorry
  have step13_cfbc : Triangle.area △ c:b:f + Triangle.area △ c:f:g = |(b─c)| * |(b─c)| := by sorry
  euclid_finish

end Elements.Book2
