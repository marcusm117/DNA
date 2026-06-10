import SystemE

namespace Elements.Book2

-- 2.4.14: CGKB right-angled — collect the four right angles (steps 11,12,13).
set_option systemE.solverTime 30 in
theorem helper_2_step14 (b c g k : Point)
    (hstep11 : ∠ k:b:c = ∟) (hstep12 : ∠ b:c:g = ∟)
    (hstep13 : ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟) :
    ∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟ := by
  euclid_intros
  euclid_finish

end Elements.Book2
