import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step8_ahb
    (a b c e f f0 g h x : Point) (AB AC AH GH CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟)
    (hbet_aec : between a e c) (hae_ec : |(a─e)| = |(e─c)|)
    (hac_ab : |(a─c)| = |(a─b)|)
    (hbet_caf0 : between c a f0) (hbet_eff0 : between e f f0) (hef_be : |(e─f)| = |(b─e)|)
    (hah_af : |(a─h)| = |(a─f)|)
    (step8_ahb_mag : |(a─f)| < |(a─b)|)
    (hxoff : ¬ x.onLine AC) (hboff : ¬ b.onLine AC) (hhoff : ¬ h.onLine AC)
    (hxnsb : ¬ x.sameSide b AC) (hhnsx : ¬ h.sameSide x AC) :
    |(a─b)| = |(a─h)| + |(b─h)| := by
  -- h is on b's side of AC (opposing ∘ opposing) and |a-h| = |a-f| < |a-b|, so between a h b.
  have hbet : between a h b := by euclid_finish
  have hsum : |(a─h)| + |(h─b)| = |(a─b)| := between_if a h b hbet
  linarith [hsum, segment_symmetric h b]

end Elements.Book2
