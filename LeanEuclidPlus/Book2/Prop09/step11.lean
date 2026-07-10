import SystemE
import Book1Variants.Prop05
import Book1.Prop32.Main
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step11 (2.9.11): by the same reasoning, △CEB (CE = CB, right at C) has its base
-- angles each ∟/2. proposition_5 (base angles equal), proposition_32 (angle sum),
-- the right angle ∠e:c:b = ∟ (from step1 + a,c,b collinear), and halving via linarith.
theorem helper_2_9_step11
  (a b c e e0 e1 : Point) (AB CE EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hce_cb : |(c─e)| = |(c─b)|)
  (hstep1 : ∠ a:c:e = ∟) :
  ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2 := by
  -- off-line facts (zero-SMT library lemmas, anchored at ¬e0.onLine AB)
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c (by euclid_finish) hab_c hab_a haoCE
  have hboCE : ¬(b.onLine CE) :=
    offLine_of_two_points b c e0 AB CE hab_b hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hCEneAB : CE ≠ AB := fun h => hne0 (h ▸ hce_e0)
  -- right angle at C for △CEB
  have hrcb : ∠ e:c:b = ∟ := by euclid_finish
  have hformTri : formTriangle c e b CE EB AB := by euclid_finish
  -- produced points beyond b for prop_5 (on AB) and prop_32 (on EB)
  have hcb : c ≠ b := by euclid_finish
  have hceb_dist : distinctPointsOnLine c b AB := ⟨hab_c, hab_b, hcb⟩
  obtain ⟨d1, hd1on, hbd1⟩ := extend_point AB c b hceb_dist
  have heb : e ≠ b := by euclid_finish
  have heb_dist : distinctPointsOnLine e b EB := ⟨heb_e, heb_b, heb⟩
  obtain ⟨d2, hd2on, hbd2⟩ := extend_point EB e b heb_dist
  -- proposition_5: base angles ∠c:e:b = ∠c:b:e (first conjunct; e1 beyond e, d1 beyond b)
  have hbase : ∠ c:e:b = ∠ c:b:e := by
    euclid_apply (proposition_5 c e b e1 d1 CE EB AB)
    euclid_finish
  -- proposition_32: angle sum ∠c:e:b + ∠e:b:c + ∠b:c:e = ∟ + ∟ (d2 beyond b on EB)
  have hsum : ∠ c:e:b + ∠ e:b:c + ∠ b:c:e = ∟ + ∟ := by
    euclid_apply (proposition_32 c e b d2 CE EB AB)
    euclid_finish
  -- angle_symm rewrites (direct, with distinctness)
  have hce : c ≠ e := by euclid_finish
  have hs1 : ∠ c:b:e = ∠ e:b:c := angle_symm c b e ⟨hcb, heb.symm⟩
  have hs2 : ∠ e:c:b = ∠ b:c:e := angle_symm e c b ⟨hce.symm, hcb⟩
  -- halving: base equal + sum(− right ∠b:c:e = ∟) → each ∟/2
  have hd1' : 2 * (∠ c:e:b) = ∟ := by linarith
  have hd2' : 2 * (∠ e:b:c) = ∟ := by linarith
  constructor
  · linarith
  · linarith

end Elements.Book2
