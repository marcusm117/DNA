import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- f, g are the two far corners of the square on AB, both on GF ∥ AB ⟹ f.sameSide g AB;
-- g is opposite c across AB (46') ⟹ f is too.
theorem helper_1_47_step8_hf_nsame
    (a b c f g : Point) (AB GF : Line)
    (hf_GF : f.onLine GF) (hg_GF : g.onLine GF)
    (h_nGFAB : ¬GF.intersectsLine AB)
    (hf_nAB : ¬f.onLine AB) (hg_nAB : ¬g.onLine AB) (h_c_nAB : ¬c.onLine AB)
    (h_ng_same_c_AB : ¬g.sameSide c AB) :
    ¬f.sameSide c AB := by
  have hfg : f.sameSide g AB := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing f g AB GF)
    euclid_finish
  euclid_finish

end Elements.Book1
