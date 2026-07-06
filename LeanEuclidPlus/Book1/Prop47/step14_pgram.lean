import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The square GAFB on AB: g,a on AG; f,b on BF (AG ∥ BF); g,f on GF; a,b on AB (GF ∥ AB).
theorem helper_1_47_step14_pgram
    (a b f g : Point) (AG BF GF AB : Line)
    (hg_AG : g.onLine AG) (ha_AG : a.onLine AG)
    (hf_BF : f.onLine BF) (hb_BF : b.onLine BF)
    (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hg_nAB : ¬g.onLine AB)
    (h_nAGBF : ¬AG.intersectsLine BF) (h_nGFAB : ¬GF.intersectsLine AB) :
    formParallelogram g a f b AG BF GF AB := by
  have hf_nAB : ¬f.onLine AB := by
    intro hf_AB
    euclid_apply (intersection_lines_common_point f GF AB)
    euclid_finish
  have hgf_AB : g.sameSide f AB := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing g f AB GF)
    euclid_finish
  euclid_finish

end Elements.Book1
