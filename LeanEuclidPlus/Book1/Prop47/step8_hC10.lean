import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Ported from `helper_47_angle_dba_eq_fbc` hC10 (triple_incidence_2 BF AB BC b f a c):
-- consumes c.sameSide a BF (hC11), gives f.sameSide a BC.
theorem helper_1_47_step8_hC10
    (a b c f : Point) (AB BC BF : Line)
    (hb_BF : b.onLine BF) (hb_AB : b.onLine AB) (hb_BC : b.onLine BC)
    (hf_BF : f.onLine BF) (ha_AB : a.onLine AB) (hc_BC : c.onLine BC)
    (hfb : f ≠ b)
    (h_c_nAB : ¬c.onLine AB) (h_f_nsame_c_AB : ¬f.sameSide c AB)
    (h_cSameA_BF : c.sameSide a BF) :
    f.sameSide a BC := by
  euclid_apply (triple_incidence_2 BF AB BC b f a c)
  euclid_finish

end Elements.Book1
