import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: DG ≠ CE. Uses d ∈ DG and that d ∉ CE (derivable from between c d b + c ∈ CE + c≠d
   and euclid_finish knowing all the figure angles/lengths). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_DGneCE (a b c d e f : Point) (AB CE DG EF BF : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdDG : d.onLine DG)
    (hacd : between a c d) (hcdb : between c d b)
    (hcbf : ∠ c:b:f = ∟) (hbf_len : |(b─f)| = |(c─b)|)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    DG ≠ CE := by
  intro hDGeqCE
  have hdCE : d.onLine CE := hDGeqCE ▸ hdDG
  have hcd : c ≠ d := by euclid_finish
  have step11_DGneCE_foff : ¬(f.onLine AB) := by sorry
  have hEFneAB : EF ≠ AB := fun heq => step11_DGneCE_foff (heq ▸ hfEF)
  -- AB = CE from c,d on both; proof inline: euclid_finish with c≠d,hcAB,hdAB,hcCE,hdCE
  have hABisCE : AB = CE := by
    euclid_apply (two_points_determine_line c d AB CE)
    euclid_finish
  have heAB : e.onLine AB := hABisCE ▸ heCE
  euclid_apply (intersection_lines_common_point e EF AB)
  euclid_finish

end Elements.Book2
