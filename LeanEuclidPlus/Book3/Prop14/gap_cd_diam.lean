import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop14.hdiam_cd
import Book3.Prop14.gap_cd_diam_pa
import Book3.Prop14.gap_cd_diam_pb
import Book3.Prop14.gap_cd_diam_fe0
import Book3.Prop14.hdiam_ab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- @euclid_gap: e = g means the foot on CD is the centre, i.e. CD is a diameter.
-- Mirror of gap_ab_diam: with the faithful hypotheses `between a f b` / `between c g d`
-- the proposition is true and provable here (equal chords ⟹ AB is a diameter too, so f = e).
theorem helper_3_14_gap_cd_diam
    (a b c d e f g : Point) (ABDC : Circle) (AB CD : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab_ne : a ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd_ne : c ≠ d)
    (hfAB : f.onLine AB) (hfangle : ∠ a:f:e = ∟) (hafb : between a f b)
    (hgCD : g.onLine CD) (hgangle : ∠ c:g:e = ∟) (hcgd : between c g d)
    (h_eg : e = g) :
    (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
    (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by
  have heonCD : e.onLine CD := h_eg ▸ hgCD
  have hbet_ced : between c e d := by rw [h_eg]; exact hcgd
  constructor
  · -- Direction 1: |AB| = |CD| ⟹ |EF| = |EG| (both are 0: e = g and e = f).
    intro h_ab_cd
    have heg0 : |(e─g)| = 0 := zero_segment_onlyif e g h_eg
    have hdiam_cd : |(c─d)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_3_14_hdiam_cd a c d e ABDC (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show between c e d; assumption)))
    have gap_cd_diam_pa : |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)| := by euclid_apply (helper_3_14_gap_cd_diam_pa a e f ABDC AB (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)))
    have gap_cd_diam_pb : |(b─f)| * |(b─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)| := by euclid_apply (helper_3_14_gap_cd_diam_pb a b e f ABDC AB (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show between a f b; assumption)))
    have hchord_ab : |(a─f)| + |(f─b)| = |(a─b)| := between_if a f b hafb
    have gap_cd_diam_fe0 : |(f─e)| = 0 := by euclid_apply (helper_3_14_gap_cd_diam_fe0 a b c d e f (by euclid_assumption "" (show |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)|; assumption)) (by euclid_assumption "" (show |(b─f)| * |(b─f)| + |(f─e)| * |(f─e)| = |(a─e)| * |(a─e)|; assumption)) (by euclid_assumption "" (show |(a─f)| + |(f─b)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─e)| + |(a─e)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(c─d)|; assumption)))
    have hef0 : |(e─f)| = 0 := by rw [segment_symmetric e f]; exact gap_cd_diam_fe0
    rw [hef0, heg0]
  · -- Direction 2: |EF| = |EG| ⟹ |AB| = |CD|.  |EG| = 0 forces e = f (AB diameter).
    intro h_efeg
    have heg0 : |(e─g)| = 0 := zero_segment_onlyif e g h_eg
    have hef0 : |(e─f)| = 0 := by linarith
    have h_ef2 : e = f := zero_segment_if e f hef0
    have heonAB : e.onLine AB := by rw [h_ef2]; exact hfAB
    have hbet_aeb : between a e b := by rw [h_ef2]; exact hafb
    have hdiam_ab : |(a─b)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_3_14_hdiam_ab a b e ABDC AB (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
    have hdiam_cd : |(c─d)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_3_14_hdiam_cd a c d e ABDC (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show between c e d; assumption)))
    linarith

end Elements.Book3
