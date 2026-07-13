import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Post-5 branch: e0 is the acute-direction rep of AE (∠e0:a:b < ∟) and g0 is on the same
-- side of AB as e0.  Co-interior sum ∠e0:a:f + ∠a:f:g0 = ∠e0:a:b + ∟ < 2∟ → lines meet.
theorem helper_3_33_hFG_int_AE_hbr1
    (a b e0 f g0 : Point) (AB AE FG : Line)
    (haae : a.onLine AE) (heae : e0.onLine AE)
    (hab : a.onLine AB) (hfb : f.onLine AB) (hafb : between a f b)
    (hperp_g : ∠ a:f:g0 = ∟)
    (hffg : f.onLine FG) (hg0fg : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hpe : ∠ e0:a:b < ∟) (hqs : e0.sameSide g0 AB) (hafne : a ≠ f) :
    FG.intersectsLine AE := by
  have hsum : ∠ e0:a:f + ∠ a:f:g0 < ∟ + ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  euclid_apply (lines_intersect e0 a f g0 AE AB FG) as gg
  have hfgne : FG ≠ AE := fun h => haoffFG (h ▸ haae)
  euclid_apply (intersection_lines_common_point gg FG AE)
  assumption

end Elements.Book3
