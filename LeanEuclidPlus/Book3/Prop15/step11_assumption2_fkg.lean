import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Chain: k ≠ f → |kf| > 0 → |kf|²>0 → (hpf) |ek|²<|ef|² → (nlinarith) |ek|<|ef|
-- → point_in_circle_if → k.insideCircle → circle_line_intersections → between f k g

theorem helper_3_15_step11_assumption2_fkg
    (f k g e : Point) (ABCD : Circle) (FG : Line)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD)
    (h_centre : e.isCentre ABCD)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (hfg : f ≠ g)
    (hk_ne_f : k ≠ f)
    (hpf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|) :
    between f k g := by
  have hkf_pos : |(k─f)| > 0 :=
    lt_of_le_of_ne (segment_gte_zero (k─f)) (Ne.symm (fun h => hk_ne_f (zero_segment_if k f h)))
  have hek_sq_lt : |(e─k)| * |(e─k)| < |(e─f)| * |(e─f)| := by nlinarith
  have hek_lt : |(e─k)| < |(e─f)| := by
    nlinarith [segment_gte_zero (e─k), segment_gte_zero (e─f)]
  have hk_in : k.insideCircle ABCD :=
    point_in_circle_if e f k ABCD ⟨h_centre, hf_on, hek_lt⟩
  exact circle_line_intersections k f g FG ABCD
    ⟨hk_FG, hf_FG, hg_FG, hk_in, hf_on, hg_on, hfg⟩

end Elements.Book3
