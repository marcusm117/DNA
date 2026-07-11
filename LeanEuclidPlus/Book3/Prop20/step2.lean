import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step2
  (a b e : Point) (AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_bne_a : b ≠ a)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(e─a)| = |(e─b)|)   -- "$EA$ is equal to $EB$"
  : ∠ e:a:b = ∠ e:b:a := by
  by_cases hb : b.onLine AEF
  · -- @euclid_gap: b on line AE ⟹ AB is a diameter, so e,a,b are collinear and triangle EAB
    -- degenerates (both ∠EAB and ∠EBA are zero). Euclid tacitly excludes the diameter case.
    euclid_finish
  · euclid_apply (line_from_points a b) as AB
    euclid_apply (line_from_points e b) as EB
    have htri : formTriangle e a b AEF AB EB := by euclid_finish
    euclid_apply (extend_point AEF e a) as d1
    euclid_apply (extend_point EB e b) as d2
    euclid_apply (Elements.Book1.proposition_5 e a b d1 d2 AEF AB EB)
    euclid_finish

end Elements.Book3
