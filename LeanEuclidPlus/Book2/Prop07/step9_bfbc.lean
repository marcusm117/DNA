import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- BF = BC (shared core of sentence 2.7.9, also used by 2.7.8). In the square CF (= CBFG) the side
   BF equals the opposite side CG (step9_cgbf, via Prop.~1.34), and CG = CB by the isosceles argument
   on triangle CGB (step9_corr/iso/cgb/bccg: the base angles ∠cgb and ∠gbc are equal, so
   |b─c| = |c─g|). Hence |b─f| = |c─g| = |b─c|. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step9_bfbc (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    |(b─f)| = |(b─c)| := by
  euclid_intros
  have had : a ≠ d := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by sorry
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have hgd : g ≠ d := ((between_symm d g b (between_symm b g d step3_bgd).1).2.1).symm
  have step3_cnbe : ¬(c.onLine BE) := by sorry
  have step3_bnhf : ¬(b.onLine HF) := by sorry
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_cab : c.onLine AB := by sorry
  have step3_gnab : ¬(g.onLine AB) := by sorry
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have step9_tri : formTriangle c g b CN BD AB := by sorry
  have step9_ss : c.sameSide a BD := by sorry
  have step9_corr : ∠ c:g:b = ∠ a:d:b := by sorry
  have step9_iso : ∠ a:d:b = ∠ a:b:d := by sorry
  have step9_cgb : ∠ c:g:b = ∠ g:b:c := by sorry
  have step9_bccg : |(b─c)| = |(c─g)| := by sorry
  have step3_cfbe : ¬(CN.intersectsLine BE) := by sorry
  have step9_csg : c.sameSide g BE := by sorry
  have step9_parCF : formParallelogram c b g f AB HF CN BE := by sorry
  have step9_cgbf : |(c─g)| = |(b─f)| := by sorry
  euclid_finish

end Elements.Book2
