import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_35_step8
  (a d e f b c : Point) (AF BC AB CD : Line)
  (hassump1 : formParallelogram a d b c AF BC AB CD)
  (hf_AF : f.onLine AF)
  (he_AF : e.onLine AF)
  (hbet1 : between a d e)
  (hbet2 : between d e f)
  : ∠ f:d:c = ∠ e:a:b := by
  have hbet3 : between a d f := between_trans_out a d e f ⟨hbet1, hbet2⟩
  have hbetsym : between f d a := (between_symm a d f hbet3).1
  have hnbet_dae : ¬(between d a e) := (between_symm a d e hbet1).2.2.2
  have hbcAF : b.sameSide c AF := (parallelogram_same_side a d b c AF BC AB CD hassump1).2.1
  have hcss : c.sameSide b AF := same_side_symm b c AF hbcAF
  euclid_apply (proposition_29'''' c b f d a CD AB AF)
  have hnbet_bab : ¬(between b a b) := fun h => (between_symm b a b h).2.2.1 rfl
  euclid_apply (equal_angles a d e b b AF AB)
  euclid_finish

end Elements.Book1
