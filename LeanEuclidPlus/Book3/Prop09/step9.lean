import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step9
    (ABC : Circle) (a b d e : Point) (AB GK : Line)
    (hstep7 : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)|)
    (hstep8 : ∠ a:e:d = ∟)
    (hassump1 : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK)
    : ∀ o : Point, o.isCentre ABC → o.onLine GK :=
  hassump1 ⟨hstep7.1, hstep7.2.1, hstep7.2.2, hstep8⟩

end Elements.Book3
