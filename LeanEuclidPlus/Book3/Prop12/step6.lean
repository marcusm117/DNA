import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step6 (f g c d a : Point)
    (hfcd : between f c d)
    (hcdg : between c d g)
    (step3 : |(f─a)| = |(f─c)|)
    (step4 : |(g─a)| = |(g─d)|)
    : |(f─g)| > |(f─a)| + |(a─g)| := by
  have hfcg : between f c g := between_trans_out f c d g ⟨hfcd, hcdg⟩
  have hlen_fcg := between_if f c g hfcg
  have hlen_cdg := between_if c d g hcdg
  have hcNd : c ≠ d := by euclid_finish
  have hcd_pos : 0 < |(c─d)| :=
    lt_of_le_of_ne (segment_gte_zero (c─d)) (Ne.symm (fun h => hcNd (zero_segment_if c d h)))
  linarith [segment_symmetric a g, segment_symmetric g d]

end Elements.Book3
