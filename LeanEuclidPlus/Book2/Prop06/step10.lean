import SystemE

set_option systemE.solverTime 30 in
theorem helper_2_6_step10 (a c d h m f g l k : Point)
    (step8 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ h:m:f + Triangle.area △ h:f:g)
    (step9 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ a:c:l + Triangle.area △ a:l:k) +
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l)) :
    Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) := by
  linarith
