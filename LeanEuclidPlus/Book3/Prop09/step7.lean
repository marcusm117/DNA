import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step7
    (a b e : Point) (GK : Line)
    (he_GK : e.onLine GK) (haeb : between a e b) (hae_eb : |(a─e)| = |(e─b)|)
    : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| :=
  ⟨he_GK, haeb, hae_eb⟩

end Elements.Book3
