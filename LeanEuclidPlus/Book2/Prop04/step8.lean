import SystemE

namespace Elements.Book2

-- 2.4.8: CGKB equilateral — all four sides equal, by transitivity of steps 5,6,7.
set_option systemE.solverTime 30 in
theorem helper_2_step8 (b c g k : Point)
    (hstep5 : |(b─c)| = |(c─g)|)
    (hstep6 : |(c─b)| = |(g─k)| ∧ |(c─g)| = |(k─b)|)
    (hstep7 : |(g─k)| = |(k─b)|) :
    |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
