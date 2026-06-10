import SystemE

namespace Elements.Book2

-- 2.4.16: CGKB is a square — equilateral (step15) ∧ right-angled (step14).
set_option systemE.solverTime 30 in
theorem helper_2_step16 (b c g k : Point)
    (hstep15 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|)
    (hstep14 : ∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟) :
    (|(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) ∧
    (∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟) := by
  euclid_intros
  euclid_finish

end Elements.Book2
