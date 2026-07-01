import SystemE

namespace Elements.Book2

-- step 7: G bisects BF (between b₀ g f, |b₀─g| = |g─f|) — the Prop 1.10 facts, packaged.
set_option systemE.solverTime 30 in
theorem helper_2_14_step7 (b₀ g f : Point) (h1 : between b₀ g f) (h2 : |(b₀─g)| = |(g─f)|) :
    between b₀ g f ∧ |(b₀─g)| = |(g─f)| := ⟨h1, h2⟩

end Elements.Book2
