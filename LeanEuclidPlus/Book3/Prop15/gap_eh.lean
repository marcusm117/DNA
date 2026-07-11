import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- @euclid_gap: When e = h, BC is a diameter (centre on BC → |BC| = 2R = |AD|).
-- Conclusion |AD| > |BC| is then false. Theorem is missing hypothesis h ≠ e.
-- NOW RESOLVED: proposition_15's signature includes e ≠ h, so this branch is impossible.
-- Closed by contradiction: heh (e ≠ h from signature) refutes h_eh (e = h from by_cases).
theorem helper_3_15_gap_eh
    (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line)
    (hcentre : e.isCentre ABCD)
    (ha_on : a.onCircle ABCD) (hd_on : d.onCircle ABCD) (had : between a e d)
    (hb_on : b.onCircle ABCD) (hc_on : c.onCircle ABCD) (hbc : b ≠ c)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hh_BC : h.onLine BC)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD) (hfg : f ≠ g)
    (hk_FG : k.onLine FG) (h_ang_k : ∠ e:k:f = ∟)
    (heh : e ≠ h)
    (h_eh : e = h)
    (h_lt : |(e─h)| < |(e─k)|) :
    |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| :=
  absurd h_eh heh

end Elements.Book3
