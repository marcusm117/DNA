import SystemE
import Book.Prop03
import Book.Prop04
import Mathlib.Tactic.Linarith

namespace Elements.Book1

/- 1.6 branch 2 (AC > AB) — the symmetric mirror of branch 1 (B↔C, d→e). This CONSTRUCTS e on CA
   with CE = AB (proposition_3) and joins EB, then runs the mirror: `equal_angles` (∠e:c:b = ∠a:c:b,
   e on ray c→a) + the hypothesis ⟹ ∠e:c:b = ∠a:b:c; SAS (proposition_4, △CEB ≅ △BAC); and the area
   absurdity (area_congruence + sum_areas_if: e∈CA splits CAB) contradicts the congruence. -/
set_option systemE.solverTime 30 in
theorem helper_1_6_sym (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hang : ∠ a:b:c = ∠ a:c:b) (hgt : |(a─c)| > |(a─b)|) :
    False := by
  euclid_apply (proposition_3 c a a b AC AB) as e
  euclid_apply (line_from_points e b) as EB
  have h1 : ∠ e:c:b = ∠ a:c:b := by
    euclid_apply (equal_angles c e a b b AC BC)
    assumption
  have h6 : ∠ e:c:b = ∠ a:b:c := h1.trans hang.symm
  have h8 : |(e─b)| = |(a─c)| ∧ (∠ c:e:b = ∠ b:a:c) ∧ (∠ c:b:e = ∠ b:c:a) := by
    euclid_apply (proposition_4 c e b b a c AC EB BC AB AC BC)
    (try split_ands) <;> assumption
  have hoff : ¬b.onLine AC := by euclid_finish
  have heq : Triangle.area △c:e:b = Triangle.area △c:a:b := by
    euclid_apply (area_congruence c e b c a b)
    assumption
  have hdec : Triangle.area △c:e:b + Triangle.area △b:e:a = Triangle.area △c:b:a := by
    euclid_apply (sum_areas_if c a e b AC)
    assumption
  have hpos : (0 : ℝ) < Triangle.area △b:e:a := by euclid_finish
  have hsymm : Triangle.area △c:b:a = Triangle.area △c:a:b := area_symm_2 c b a
  linarith

end Elements.Book1
