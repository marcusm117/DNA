import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: ∠ f:d:h = ∟. At corner d, ∠ a:d:e = ∟ (square). The ray d→f coincides with d→e
   (f between d, e on DE) and d→h coincides with d→a (h between a, d on AD), so
   ∠ f:d:h = ∠ e:d:a = ∟ (equal_angles + angle symmetry). -/
theorem helper_2_4_step22_fdh (a d e f h : Point) (DE AD : Line)
    (hdfe : between d f e) (hahd : between a h d)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hda : d ≠ a) (hde : d ≠ e)
    (hade : ∠ a:d:e = ∟) :
    ∠ f:d:h = ∟ := by
  euclid_intros
  euclid_apply (equal_angles d f e h a DE AD)
  euclid_finish

end Elements.Book2
