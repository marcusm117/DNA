import SystemE
import Book2.Prop05.step12_sshc_cd
import Book2.Prop05.step12_sshc_dh
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12 sub: c.sameSide h AK. Container of two legs:
   (1) step12_sshc_cd : c.sameSide d AK  (a∈AK is the foot, between a c d)
   (2) step12_sshc_dh : d.sameSide h AK  (d,h on DG, AK ∥ DG)
   transitivity (same_side_trans through d) closes c.sameSide h AK. -/
theorem helper_2_5_step12_sshc (a c d h k : Point) (AB AK DG : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hacd : between a c d)
    (hAKAB : AK ≠ AB)
    (hAKDG : ¬(AK.intersectsLine DG)) :
    c.sameSide h AK := by
  euclid_intros
  have had : a ≠ d := by euclid_finish
  have step12_sshc_cd : c.sameSide d AK := by euclid_apply (helper_2_5_step12_sshc_cd a c d AB AK (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show AK ≠ AB; assumption)))
  have step12_sshc_dh : d.sameSide h AK := by euclid_apply (helper_2_5_step12_sshc_dh a d h AB AK DG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show AK ≠ AB; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine DG); assumption)))
  exact same_side_trans d c h AK ⟨same_side_symm c d AK step12_sshc_cd, step12_sshc_dh⟩

end Elements.Book2
