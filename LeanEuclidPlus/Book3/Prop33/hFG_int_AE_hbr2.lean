import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Post-5 branch: e0 acute rep of AE, but g0 is on the opposite side of AB from e0.
-- Extend FG past f to g0' (on e0's side); ∠a:f:g0' = ∟ still.
theorem helper_3_33_hFG_int_AE_hbr2
    (a b e0 f g0 : Point) (AB AE FG : Line)
    (haae : a.onLine AE) (heae : e0.onLine AE) (he0off : ¬ e0.onLine AB)
    (hab : a.onLine AB) (hfb : f.onLine AB) (hafb : between a f b)
    (hperp_g : ∠ a:f:g0 = ∟)
    (hffg : f.onLine FG) (hg0fg : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hpe : ∠ e0:a:b < ∟) (hqs : ¬ e0.sameSide g0 AB) (hafne : a ≠ f) :
    FG.intersectsLine AE := by
  euclid_apply (extend_point FG g0 f) as g0'
  have hss : e0.sameSide g0' AB := by euclid_finish
  have hsum : ∠ e0:a:f + ∠ a:f:g0' < ∟ + ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  euclid_apply (lines_intersect e0 a f g0' AE AB FG) as gg
  have hfgne : FG ≠ AE := fun h => haoffFG (h ▸ haae)
  euclid_apply (intersection_lines_common_point gg FG AE)
  assumption

end Elements.Book3
