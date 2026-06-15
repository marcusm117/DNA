import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.6: AF + CE is the gnomon KLM (= AG + GE + CF) plus the square CF. From the two tilings
   AF = AG + CF (tileAF) and CE = CF + GE (tileCE), AF + CE = (AG + GE + CF) + CF. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step6 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (Triangle.area △ a:b:f + Triangle.area △ a:f:h) + (Triangle.area △ c:b:e + Triangle.area △ c:e:n)
      = ((Triangle.area △ a:c:g + Triangle.area △ a:g:h) + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
          + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g) := by
  euclid_intros
  -- off-line / distinctness roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step3_cnad : ¬(c.onLine AD) := by sorry
  have step3_dnab : ¬(d.onLine AB) := by sorry
  have step3_anbe : ¬(a.onLine BE) := by sorry
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
  have step3_abde : ¬(AB.intersectsLine DE) := by sorry
  -- betweenness
  have step4_hgf : between h g f := by sorry
  have step4_cgn : between c g n := by sorry
  have step3_bke : between b f e := by sorry
  -- distinctness for the parallelograms
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_gnbe : ¬(g.onLine BE) := by sorry
  have hne : n ≠ e := by euclid_finish
  -- the two half-rectangles and the same-side facts they need
  have step4_ahbe : a.sameSide h BE := by sorry
  have step4_cbde : c.sameSide b DE := by sorry
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by sorry
  have step4_parCE : formParallelogram c n b e CN BE AB DE := by sorry
  -- the two tilings
  have step4_tileAF : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = Triangle.area △ a:b:f + Triangle.area △ a:f:h := by sorry
  have step4_tileCE : (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
      = Triangle.area △ c:b:e + Triangle.area △ c:e:n := by sorry
  euclid_finish

end Elements.Book2
