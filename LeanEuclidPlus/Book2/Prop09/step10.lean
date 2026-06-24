import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step10 (2.9.10): CEA and CAE are each half a right-angle. From step8 (EAC+AEC = ∟)
-- and step9 (EAC = AEC): each is ∟/2. angle_symm is applied DIRECTLY (it needs the
-- distinctness c≠e,c≠a,e≠a, which the bare angle hyps don't supply); `linarith`
-- (Mathlib) closes the halving over ℝ that the SMT translator can't encode.
theorem helper_2_9_step10
  (a b c e e1 : Point)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hea : e ≠ a)
  (h7 : ∠ e:a:c = ∠ a:e:c)
  (h8 : ∠ e:a:c + ∠ a:e:c = ∟) :
  ∠ c:e:a = ∟ / 2 ∧ ∠ c:a:e = ∟ / 2 := by
  have hce : c ≠ e := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have h1 : ∠ c:e:a = ∠ a:e:c := angle_symm c e a ⟨hce, hea⟩
  have h2 : ∠ c:a:e = ∠ e:a:c := angle_symm c a e ⟨hca, hea.symm⟩
  have hd1 : 2 * (∠ c:e:a) = ∟ := by linarith
  have hd2 : 2 * (∠ c:a:e) = ∟ := by linarith
  constructor
  · linarith
  · linarith

end Elements.Book2
