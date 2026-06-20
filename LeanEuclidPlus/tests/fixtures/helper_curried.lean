import SystemE
set_option linter.unusedVariables false

namespace Elements

/- A curried-binder helper with an atomic-fact hypothesis binder and a parallelogram hyp, citing a
   proposition and a construction in its body. -/
theorem sample_helper (p q w : Point) (L M : Line)
    (hpL : p.onLine L) (hpar : ¬(M.intersectsLine L))
    (hpgram : formParallelogram p q w p L M L M) :
    p.sameSide q M := by
  euclid_intros
  euclid_apply (proposition_30 L M L)
  euclid_apply (line_from_points p q) as PQ
  euclid_finish

end Elements
