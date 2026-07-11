import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- With k ≠ e and k ≠ f, all collinear configurations of e, k, f on FG are non-degenerate:
-- between(e,k,f) → flat_angle_onlyif → ∠e:k:f = ∟+∟ = ∟ → ∟ = 0, contradicts right_angle_pos;
-- ¬between(e,k,f) → degenerated_angle_if → ∠e:k:f = 0 = ∟, contradicts right_angle_pos.

theorem helper_3_15_step11_assumption2_e_off_fg
    (e f k : Point) (FG : Line)
    (hf_FG : f.onLine FG) (hk_FG : k.onLine FG)
    (hperp_k : ∠ e:k:f = ∟)
    (hk_ne_e : k ≠ e)
    (hk_ne_f : k ≠ f) :
    ¬e.onLine FG := by
  intro he
  euclid_finish

end Elements.Book3
