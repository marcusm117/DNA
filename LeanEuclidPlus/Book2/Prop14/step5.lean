import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 5: F lies on BE beyond E (between b₀ e f). From `between b₀ e ffar` (extend) and
-- `between e f ffar` (Prop 1.3 cut), E is between B and F; F is collinear with e, ffar (both on BE).
theorem helper_2_14_step5
    (b₀ e f ffar : Point) (BE : Line)
    (h_beffar : between b₀ e ffar)
    (h_ffarBE : ffar.onLine BE)
    (h_efffar : between e f ffar)
    (h_eBE : e.onLine BE) :
    between b₀ e f ∧ f.onLine BE := by
  euclid_finish

end Elements.Book2
