import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8: double AF is twice the rectangle contained by AB and BC. AF = ABFH = |h─f|·|h─a|
   (rectAF, via rectangle_area with the right angle ∠h:a:b); the opposite sides give |h─f| = |a─b|
   and |h─a| = |b─f| (lens, Prop.~1.34'), and |b─f| = |b─c| (step9). Hence AF = |a─b|·|b─c| and
   2 AF = 2 (|a─b|·|b─c|). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step8 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
      = |(a─b)| * |(b─c)| + |(a─b)| * |(b─c)| := by
  euclid_intros
  have step9_bfbc : |(b─f)| = |(b─c)| := by sorry
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by sorry
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by sorry
  have step3_bnhf : ¬(b.onLine HF) := by sorry
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have hfb : f ≠ b := fun hh => hbf hh.symm
  have hbg : b ≠ g := by euclid_finish
  have step3_gnab : ¬(g.onLine AB) := by sorry
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have step3_anbe : ¬(a.onLine BE) := by sorry
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  -- foot h between a and d, giving the right angle ∠h:a:b
  have step8_ahd : between a h d := by sorry
  have step8_hab : ∠ h:a:b = ∟ := by sorry
  -- the rectangle ABFH (two orientations) + its side lengths
  have step4_ahbe : a.sameSide h BE := by sorry
  have step8_hsa : h.sameSide a BE := by sorry
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by sorry
  have step8_parAF2 : formParallelogram h f a b HF AB AD BE := by sorry
  have step8_rectAF : Triangle.area △ a:b:f + Triangle.area △ a:f:h = |(h─f)| * |(h─a)| := by sorry
  have step8_lens : |(a─b)| = |(h─f)| ∧ |(a─h)| = |(b─f)| := by sorry
  euclid_finish

end Elements.Book2
