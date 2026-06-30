import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step19_ad
    (a b c d h k : Point) (AB CD AC BD : Line)
    (hpar : formParallelogram a b c d AB CD AC BD)
    (hbet_ahb : between a h b) (hbet_ckd : between c k d) :
    Triangle.area △ a:h:k + Triangle.area △ a:k:c + Triangle.area △ h:k:d + Triangle.area △ h:b:d
      = Triangle.area △ a:c:d + Triangle.area △ a:b:d := by
  -- cut the square ABDC by the vertical H-K: AD = (AHKC) + (HBDK).
  euclid_apply (sum_parallelograms_area a b c d h k AB CD AC BD)
  euclid_finish

end Elements.Book2
