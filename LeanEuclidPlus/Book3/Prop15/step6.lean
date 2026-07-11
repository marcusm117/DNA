import SystemE
import Book3.Prop14.Main
import Mathlib.Tactic.Linarith
import Book3.Prop15.step6_pb
import Book3.Prop15.step6_pm
import Book3.Prop15.step6_rad
import Book3.Prop15.step6_hb_ne
import Book3.Prop15.step6_hc_ne
import Book3.Prop15.step6_pc
import Book3.Prop15.step6_pn
import Book3.Prop15.step6_eq_bh_hc
import Book3.Prop15.step6_bhc
import Book3.Prop15.step6_eq_bh_lm
import Book3.Prop15.step6_eq_hc_ln
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.15 step6: |b─c| = |m─n| from equal distances |e─h| = |e─l|.
-- h ≠ b and h ≠ c proved by contradiction (if h=b/c then |e─l|=|e─m| → l=m,
-- contradicting between m l n). Then Pythagorean + betweenness gives the result.
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
  have step6_pb : |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by euclid_apply (helper_3_15_step6_pb b h e ABCD BC (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show e ≠ h; assumption)) (by euclid_assumption "" (show ∠ e:h:b = ∟; assumption)))
  -- Sub-node 2: Pythagorean for m: |l─m|² + |e─l|² = |e─m|²  (early, used by hb_ne/hc_ne)
  have step6_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by euclid_apply (helper_3_15_step6_pm m l e ABCD MN (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)))
  -- Sub-node 3: equal radii |e─b| = |e─m|
  have step6_rad : |(e─b)| = |(e─m)| := by euclid_apply (helper_3_15_step6_rad b m e ABCD (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)))
  -- Sub-node 4: h ≠ b (if h = b, then |e─l| = |e─m|, so |l─m|² = 0 → l = m, ↯ between m l n)
  have step6_hb_ne : h ≠ b := by euclid_apply (helper_3_15_step6_hb_ne b h l m n e ABCD (by euclid_assumption "" (show |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─h)| = |(e─l)|; assumption)) (by euclid_assumption "" (show between m l n; assumption)))
  -- Sub-node 5: h ≠ c (same argument via |e─c| = |e─m| from equal radii)
  have step6_hc_ne : h ≠ c := by euclid_apply (helper_3_15_step6_hc_ne c h l m n e ABCD (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─h)| = |(e─l)|; assumption)) (by euclid_assumption "" (show between m l n; assumption)))
  -- Sub-node 6: Pythagorean for c: |h─c|² + |e─h|² = |e─b|² (uses hb_ne, hc_ne, EH line)
  have step6_pc : |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)| := by euclid_apply (helper_3_15_step6_pc b c h e ABCD BC EH (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show h.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine EH; assumption)) (by euclid_assumption "" (show h.onLine EH; assumption)) (by euclid_assumption "" (show e ≠ h; assumption)) (by euclid_assumption "" (show h ≠ b; assumption)) (by euclid_assumption "" (show h ≠ c; assumption)) (by euclid_assumption "" (show ∠ e:h:b = ∟; assumption)))
  -- Sub-node 7: Pythagorean for n: |l─n|² + |e─l|² = |e─m|²
  have step6_pn : |(l─n)| * |(l─n)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by euclid_apply (helper_3_15_step6_pn m n l e ABCD MN (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)) (by euclid_assumption "" (show between m l n; assumption)))
  -- Sub-node 8: |b─h| = |h─c| (from pb and pc sharing the same rhs)
  have step6_eq_bh_hc : |(b─h)| = |(h─c)| := by euclid_apply (helper_3_15_step6_eq_bh_hc b h c e (by euclid_assumption "" (show |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|; assumption)) (by euclid_assumption "" (show |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|; assumption)))
  -- Sub-node 9: between b h c (from |b─h| = |h─c| + b≠c via betweenness trichotomy)
  have step6_bhc : between b h c := by euclid_apply (helper_3_15_step6_bhc b c h BC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show h.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show h ≠ b; assumption)) (by euclid_assumption "" (show h ≠ c; assumption)) (by euclid_assumption "" (show |(b─h)| = |(h─c)|; assumption)))
  -- Criterion-3 citation for [Prop.~3.14]: equal distances from centre → equal chords.
  -- |(e─h)| = |(e─l)| (= hassump1) → |(b─c)| = |(m─n)|; close goal by assumption (hassump1 in ctx).
  have h_prop14_cite : |(e─h)| = |(e─l)| := by
    euclid_apply (Elements.Book3.proposition_14 b c m n e h l ABCD BC MN)
    assumption
  -- Sub-node 10: |b─h| = |l─m|
  have step6_eq_bh_lm : |(b─h)| = |(l─m)| := by euclid_apply (helper_3_15_step6_eq_bh_lm b h l m e (by euclid_assumption "" (show |(b─h)| * |(b─h)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|; assumption)) (by euclid_assumption "" (show |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─h)| = |(e─l)|; assumption)))
  -- Sub-node 11: |h─c| = |l─n|
  have step6_eq_hc_ln : |(h─c)| = |(l─n)| := by euclid_apply (helper_3_15_step6_eq_hc_ln h c l n e b m (by euclid_assumption "" (show |(h─c)| * |(h─c)| + |(e─h)| * |(e─h)| = |(e─b)| * |(e─b)|; assumption)) (by euclid_assumption "" (show |(l─n)| * |(l─n)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(e─m)|; assumption)) (by euclid_assumption "" (show |(e─h)| = |(e─l)|; assumption)))
  -- Segment addition: |b─c| = |b─h| + |h─c| = |l─m| + |l─n| = |m─n|
  have h_sum_bc := between_if b h c step6_bhc
  have h_sum_mn : |(l─m)| + |(l─n)| = |(m─n)| := by euclid_finish
  linarith [h_sum_bc, h_sum_mn, step6_eq_bh_lm, step6_eq_hc_ln]

end Elements.Book3
