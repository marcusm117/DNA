import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step2
  (e f b c : Point) (AF BC EB FC : Line)
  (he_AF : e.onLine AF) (hf_AF : f.onLine AF)
  (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (hf_FC : f.onLine FC) (hc_FC : c.onLine FC)
  (hfc : f ≠ c) (hesid : e.sameSide b FC)
  (hpar1 : ¬AF.intersectsLine BC) (hpar2 : ¬EB.intersectsLine FC)
  : |(e─f)| = |(b─c)| := by
  have hpgram : formParallelogram e f b c AF BC EB FC :=
    ⟨he_AF, hf_AF, hb_BC, hc_BC, he_EB, hb_EB, ⟨hf_FC, hc_FC, hfc⟩, hesid, hpar1, hpar2⟩
  euclid_apply (proposition_34' e f b c AF BC EB FC)
  euclid_finish

end Elements.Book1
