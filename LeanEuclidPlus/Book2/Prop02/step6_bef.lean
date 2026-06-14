import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.6: ∠b:e:f = ∟. f lies on DE on the same ray from e as d (between d f e, so e
   is not between d and f), hence the angle ∠b:e:f equals ∠b:e:d = ∟ (equal_angles at vertex e). -/
theorem helper_2_2_step6_bef (b d e f : Point) (DE BE : Line)
    (hbed : ∠ b:e:d = ∟) (hdfe : between d f e) (hebne : e ≠ b)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE) :
    ∠ b:e:f = ∟ := by
  euclid_intros
  euclid_apply (equal_angles e d f b b DE BE)
  euclid_finish

end Elements.Book2
