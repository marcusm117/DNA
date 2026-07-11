import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- between b h c: from |b─h| = |h─c| and b≠c, h≠b, h≠c, all on BC.
-- between_points (b h c BC) : between b h c ∨ between h b c ∨ between b c h.
-- The other two cases force |b─c| = 0, contradicting b≠c.
theorem helper_3_15_step6_bhc
    (b c h : Point) (BC : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hh_BC : h.onLine BC)
    (hbc_ne : b ≠ c) (hbh : h ≠ b) (hhc : h ≠ c)
    (h_eq : |(b─h)| = |(h─c)|) :
    between b h c := by
  rcases between_points b h c BC ⟨hbh.symm, hhc, hbc_ne.symm, hb_BC, hh_BC, hc_BC⟩ with h1 | h2 | h3
  · exact h1
  · -- between h b c: b between h and c; gives |h─b| + |b─c| = |h─c|
    exfalso
    have h_sum := between_if h b c h2
    have h_sym : |(h─b)| = |(b─h)| := by euclid_finish
    have h0 : |(b─c)| = 0 := by linarith [h_sum, h_sym, h_eq]
    exact hbc_ne (zero_segment_if b c h0)
  · -- between b c h: c between b and h; gives |b─c| + |c─h| = |b─h|
    exfalso
    have h_sum := between_if b c h h3
    have h_sym : |(c─h)| = |(h─c)| := by euclid_finish
    have h0 : |(b─c)| = 0 := by linarith [h_sum, h_sym, h_eq]
    exact hbc_ne (zero_segment_if b c h0)

end Elements.Book3
