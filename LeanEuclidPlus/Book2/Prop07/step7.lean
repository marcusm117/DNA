import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.7: the gnomon KLM and the square CF are double AF. Combining step6 (AF + CE = gnomon + CF)
   and step5 (AF + CE = 2 AF): gnomon + CF = AF + CE = 2 AF. -/
theorem helper_2_7_step7 (a b c e n g h f : Point)
    (hstep5 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ c:b:e + Triangle.area △ c:e:n)
      = (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h))
    (hstep6 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ c:b:e + Triangle.area △ c:e:n)
      = ((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
          + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
          + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) :
    ((Triangle.area △ a:c:g + Triangle.area △ a:g:h)
        + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
        + (Triangle.area △ c:b:f + Triangle.area △ c:f:g))
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h) := by
  rw [← hstep6, hstep5]

end Elements.Book2
