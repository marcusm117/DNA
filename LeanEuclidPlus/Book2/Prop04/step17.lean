import SystemE

namespace Elements.Book2

-- 2.4.17: the square CGKB is on CB — its side CG equals CB (from step5: |BC| = |CG|).
set_option systemE.solverTime 30 in
theorem helper_2_step17 (b c g : Point)
    (hstep5 : |(b─c)| = |(c─g)|) :
    |(c─g)| = |(c─b)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
