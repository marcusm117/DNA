import SystemE
import Helpers.RightAngle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- ∠b₀:e:h = ∟ : the rectangle corner at E. Known right angle ∠c₀:b₀:e at b₀; since ED ∥ B₀C₀ cut
-- by transversal BE, the co-interior angle ∠d:e:b₀ is right (right_angle_cointerior, applied inline
-- as a term so no SMT search); H is on ED beyond e (between h e d), so its supplement ∠b₀:e:h is
-- right too (perpendicular_onlyif). d.sameSide c₀ BE is supplied (DC ∥ BE — derived in step14_ss).
theorem helper_2_14_step14_rt0 (e d b₀ c₀ h f : Point) (ED B₀C₀ BE : Line)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED)
    (h_b0BC : b₀.onLine B₀C₀) (h_c0BC : c₀.onLine B₀C₀)
    (h_b0BE : b₀.onLine BE) (h_eBE : e.onLine BE)
    (h_rang : ∠ c₀:b₀:e = ∟)
    (h_par1 : ¬ED.intersectsLine B₀C₀)
    (h_ss : d.sameSide c₀ BE)
    (h_bet_hed : between h e d) (h_bef : between b₀ e f) :
    ∠ b₀:e:h = ∟ := by
  have hed : e ≠ d := by euclid_finish
  have heb0 : e ≠ b₀ := by euclid_finish
  have hb0c0 : b₀ ≠ c₀ := by euclid_finish
  have hd : ∠ d:e:b₀ = ∟ :=
    right_angle_cointerior d c₀ e b₀ ED B₀C₀ BE
      ⟨h_eED, h_dED, hed⟩ ⟨h_b0BC, h_c0BC, hb0c0⟩
      ⟨h_eBE, h_b0BE, heb0⟩ h_ss h_par1 (by euclid_finish)
  euclid_apply (perpendicular_onlyif d h e b₀ ED)
  euclid_finish

end Elements.Book2
