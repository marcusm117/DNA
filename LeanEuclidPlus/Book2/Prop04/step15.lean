import SystemE

namespace Elements.Book2

-- 2.4.15: CGKB equilateral (re-stated, = step8).
set_option systemE.solverTime 30 in
theorem helper_2_step15 (b c g k : Point)
    (hstep8 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|) :
    |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
