import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The square GB on AB: a,b on AB; g,f on GF (AB ∥ GF); a,g on AG; b,f on BF (AG ∥ BF).
theorem helper_1_47_step20_gbpgram
    (a b g f : Point) (AB GF AG BF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (h_g_same_a_BF : g.sameSide a BF)
    (h_nGFAB : ¬GF.intersectsLine AB) (h_nAGBF : ¬AG.intersectsLine BF) :
    formParallelogram a b g f AB GF AG BF := by
  euclid_finish

end Elements.Book1
