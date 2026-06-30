import SystemE
import Book2.Prop05.Main

namespace Elements.Book2

-- step 11 [Prop. 2.5]: BF is cut equally at G (|b₀─g| = |g─f|) and unequally at E. By II.5,
--   |b₀─e|·|e─f| + |e─g|² = |g─f|².
-- The construction is unconditional (E may be on either side of the midpoint G), so we case-split
-- on the order of E,G; the II.5 equation is symmetric under b₀↔f (the equal-cut symmetry), so both
-- orderings — and the degenerate E=G — give the same equation.
set_option systemE.solverTime 30 in
theorem helper_2_14_step11 (b₀ e f g : Point) (BE : Line)
    (h_b0 : b₀.onLine BE) (h_e : e.onLine BE) (h_f : f.onLine BE)
    (h_bef : between b₀ e f) (h_bgf : between b₀ g f) (h_mid : |(b₀─g)| = |(g─f)|) :
    |(b₀─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| := by
  euclid_intros
  by_cases heg : e = g
  · euclid_finish
  · by_cases hbge : between b₀ g e
    · -- order B₀–G–E–F
      euclid_apply (Elements.Book2.proposition_5 b₀ f g e BE)
      euclid_finish
    · -- e ≠ g and ¬(b₀ g e) ⟹ order B₀–E–G–F ; apply II.5 with b₀↔f
      euclid_apply (Elements.Book2.proposition_5 f b₀ g e BE)
      euclid_finish

end Elements.Book2
