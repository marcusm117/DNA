import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.15 step6: |b─c| = |m─n| from equal distances |e─h| = |e─l|.
-- h ≠ b and h ≠ c proved by contradiction (if h=b/c then |e─l|=|e─m| → l=m,
-- contradicting between m l n). Then Pythagorean + betweenness gives the result.
set_option systemE.solverTime 30 in
theorem helper_3_15_step6
    (b c m n e h l : Point) (ABCD : Circle) (BC MN EH : Line)
    (h_centre : e.isCentre ABCD)
    (hb_on : b.onCircle ABCD) (hc_on : c.onCircle ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hh_BC : h.onLine BC) (hbc_ne : b ≠ c)
    (he_EH : e.onLine EH) (hh_EH : h.onLine EH) (heh : e ≠ h)
    (h_perp_ehb : ∠ e:h:b = ∟)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (h_perp_mle : ∠ m:l:e = ∟) (hbetw_mln : between m l n)
    (hassump1 : |(e─h)| = |(e─l)|) :
    |(b─c)| = |(m─n)| := by
  -- Sub-node 1: Pythagorean for b: |b─h|² + |e─h|² = |e─b|²
  have step6_pb : |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by sorry
  -- Sub-node 2: Pythagorean for m: |l─m|² + |e─l|² = |e─m|²  (early, used by hb_ne/hc_ne)
  have step6_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by sorry
  -- Sub-node 3: equal radii |e─b| = |e─m|
  have step6_rad : |(e─b)| = |(e─m)| := by sorry
  -- Sub-node 4: h ≠ b (if h = b, then |e─l| = |e─m|, so |l─m|² = 0 → l = m, ↯ between m l n)
  have step6_hb_ne : h ≠ b := by sorry
  -- Sub-node 5: h ≠ c (same argument via |e─c| = |e─m| from equal radii)
  have step6_hc_ne : h ≠ c := by sorry
  -- Sub-node 6: Pythagorean for c: |h─c|² + |e─h|² = |e─b|² (uses hb_ne, hc_ne, EH line)
  have step6_pc : |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by sorry
  -- Sub-node 7: Pythagorean for n: |l─n|² + |e─l|² = |e─m|²
  have step6_pn : |(l─n)| * |(l─n)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by sorry
  -- Sub-node 8: |b─h| = |h─c| (from pb and pc sharing the same rhs)
  have step6_eq_bh_hc : |(b─h)| = |(h─c)| := by sorry
  -- Sub-node 9: between b h c (from |b─h| = |h─c| + b≠c via betweenness trichotomy)
  have step6_bhc : between b h c := by sorry
  -- Sub-node 10: |b─h| = |l─m|
  have step6_eq_bh_lm : |(b─h)| = |(l─m)| := by sorry
  -- Sub-node 11: |h─c| = |l─n|
  have step6_eq_hc_ln : |(h─c)| = |(l─n)| := by sorry
  -- Segment addition: |b─c| = |b─h| + |h─c| = |l─m| + |l─n| = |m─n|
  have h_sum_bc := between_if b h c step6_bhc
  have h_sum_mn : |(l─m)| + |(l─n)| = |(m─n)| := by euclid_finish
  linarith [h_sum_bc, h_sum_mn, step6_eq_bh_lm, step6_eq_hc_ln]

end Elements.Book3
