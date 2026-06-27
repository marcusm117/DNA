import SystemE
import Book.Prop05
import Book.Prop32
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step14 (2.10.14): for the same reasons, △CEB (CE = CB, right at C) has base angles ∠CEB, ∠EBC each
-- ∟/2. proposition_5 (base angles equal), proposition_32 (angle sum), right angle ∠e:c:b=∟, halve.
theorem helper_2_10_step14
  (a b c e e0 e1 : Point) (AD CE EB : Line)
  (hab_a : a.onLine AD) (hab_b : b.onLine AD) (hab_c : c.onLine AD)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hce_cb : |(c─e)| = |(c─b)|)
  (hstep1 : ∠ a:c:e = ∟) :
  ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2 := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AD CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoAD : ¬(e.onLine AD) :=
    offLine_of_two_points e c a CE AD heCE hce_c (by euclid_finish) hab_c hab_a haoCE
  have hboCE : ¬(b.onLine CE) :=
    offLine_of_two_points b c e0 AD CE hab_b hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hCEneAD : CE ≠ AD := fun h => hne0 (h ▸ hce_e0)
  have hrcb : ∠ e:c:b = ∟ := by euclid_finish
  have hformTri : formTriangle c e b CE EB AD := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hceb_dist : distinctPointsOnLine c b AD := ⟨hab_c, hab_b, hcb⟩
  obtain ⟨d1, hd1on, hbd1⟩ := extend_point AD c b hceb_dist
  have heb : e ≠ b := by euclid_finish
  have heb_dist : distinctPointsOnLine e b EB := ⟨heb_e, heb_b, heb⟩
  obtain ⟨d2, hd2on, hbd2⟩ := extend_point EB e b heb_dist
  have hbase : ∠ c:e:b = ∠ c:b:e := by
    euclid_apply (proposition_5 c e b e1 d1 CE EB AD)
    euclid_finish
  have hsum : ∠ c:e:b + ∠ e:b:c + ∠ b:c:e = ∟ + ∟ := by
    euclid_apply (proposition_32 c e b d2 CE EB AD)
    euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hs1 : ∠ c:b:e = ∠ e:b:c := angle_symm c b e ⟨hcb, heb.symm⟩
  have hs2 : ∠ e:c:b = ∠ b:c:e := angle_symm e c b ⟨hce.symm, hcb⟩
  have hd1' : 2 * (∠ c:e:b) = ∟ := by linarith
  have hd2' : 2 * (∠ e:b:c) = ∟ := by linarith
  constructor
  · linarith
  · linarith

end Elements.Book2
