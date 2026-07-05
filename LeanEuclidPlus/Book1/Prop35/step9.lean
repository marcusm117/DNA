import SystemE
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step9
  (a d e f b c : Point) (AF BC AB CD EB FC : Line)
  (hassump1 : formParallelogram a d b c AF BC AB CD)
  (he_AF : e.onLine AF) (hf_AF : f.onLine AF)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (hf_FC : f.onLine FC) (hc_FC : c.onLine FC)
  (hbet1 : between a d e) (hbet2 : between d e f)
  (hno_EB_FC : ¬EB.intersectsLine FC)
  (hesid : e.sameSide b FC)
  (h5 : |(a─e)| = |(d─f)|)
  (h6 : |(a─b)| = |(d─c)|)
  (h8 : ∠ f:d:c = ∠ e:a:b)
  : |(e─b)| = |(f─c)| := by
  have hbet3 : between a d f := between_trans_out a d e f ⟨hbet1, hbet2⟩
  have hae_ne : a ≠ e := (between_symm a d e hbet1).2.2.1
  have hdf_ne : d ≠ f := (between_symm d e f hbet2).2.2.1
  have hae_dist : distinctPointsOnLine a e AF := ⟨hassump1.1, he_AF, hae_ne⟩
  have hdf_dist : distinctPointsOnLine d f AF := ⟨hassump1.2.1, hf_AF, hdf_ne⟩
  have htri1 : formTriangle a e b AF EB AB :=
    ⟨hae_dist, he_EB, hb_EB, hassump1.2.2.2.2.2.1, hassump1.2.2.2.2.1, by euclid_finish, by euclid_finish, by euclid_finish⟩
  have htri2 : formTriangle d f c AF FC CD :=
    ⟨hdf_dist, hf_FC, hc_FC, hassump1.2.2.2.2.2.2.1.2.1, hassump1.2.2.2.2.2.2.1.1, by euclid_finish, by euclid_finish, by euclid_finish⟩
  have h8' : ∠ e:a:b = ∠ f:d:c := h8.symm
  euclid_apply (proposition_4 a e b d f c AF EB AB AF FC CD)
  euclid_finish

end Elements.Book1
