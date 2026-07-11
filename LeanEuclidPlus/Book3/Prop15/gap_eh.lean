import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- @euclid_gap: When e = h, BC is a diameter (centre on BC → |BC| = 2R = |AD|).
-- Conclusion |AD| > |BC| is then false. Theorem is missing hypothesis h ≠ e.
-- This node's cone cannot be proved without adding h ≠ e to proposition_15's statement.
set_option systemE.solverTime 30 in
theorem helper_3_15_gap_eh
    (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line)
    (hcentre : e.isCentre ABCD)
    (ha_on : a.onCircle ABCD) (hd_on : d.onCircle ABCD) (had : between a e d)
    (hb_on : b.onCircle ABCD) (hc_on : c.onCircle ABCD) (hbc : b ≠ c)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hh_BC : h.onLine BC)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD) (hfg : f ≠ g)
    (hk_FG : k.onLine FG) (h_ang_k : ∠ e:k:f = ∟)
    (h_eh : e = h)
    (h_lt : |(e─h)| < |(e─k)|) :
    |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| := by
  -- @euclid_gap: |AD| = |BC| = 2R when e = h (both diameters), so |AD| > |BC| is false.
  -- This sub-node is permanently unprovable without h ≠ e as a premise of proposition_15.
  have gap_eh_body : |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| := by sorry
  exact gap_eh_body

end Elements.Book3
