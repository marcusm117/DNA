import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_hcentre_oED
    (a b d e o : Point) (AB ED : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_AB : e.onLine AB)
    (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
    (haeb : between a e b)
    (hperp_d : ∠ a:e:d = ∟)
    (hperp_o : ∠ a:e:o = ∟)
    (hd_eb : ∠ d:e:b = ∟) (ho_eb : ∠ o:e:b = ∟) (hflat : ∠ a:e:b = ∟ + ∟)
    (hoe : o ≠ e) (hed : e ≠ d)
    : o.onLine ED := by
  -- Create named line EO through o and e
  obtain ⟨EO, he_EO, ho_EO⟩ := line_from_points e o hoe.symm
  -- EO = ED: both perpendicular to AB at e (via perp_d and perp_o angle facts)
  have hEO_ED : EO = ED := by euclid_finish
  exact hEO_ED ▸ ho_EO

end Elements.Book3
