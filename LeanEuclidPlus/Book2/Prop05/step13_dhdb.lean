import SystemE
import Book.Prop06
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.13 (shared worker, used by both step12 and step13): |(d─h)| = |(d─b)|.
   Triangle DHB is right-isosceles: ∠ d:h:b = ∠ d:b:h, so the sides DH, DB subtending the equal base
   angles are equal [Prop.~1.6].  The base-angle equality is the diagonal chain:
     ∠ d:h:b = ∠ c:e:b           (corr: DG ∥ CE cut by diagonal BE, h between b,e — step13_dhdb_corr)
     ∠ c:e:b = ∠ c:b:e           (CEB isosceles, |c─e|=|c─b| — step13_dhdb_iso)
     ∠ c:b:e = ∠ d:b:h           (ray b→c ≡ b→d on AB, ray b→e ≡ b→h on BE — equal_angles)
   hence ∠ d:h:b = ∠ d:b:h.  Figure facts (between b h e, d.sameSide c BE, the triangle) are
   sub-nodes; off-line anchors derived in-body. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step13_dhdb (b c d e h : Point) (AB CE DG BE : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcdb : between c d b)
    (hDGCE : ¬(DG.intersectsLine CE)) :
    |(d─h)| = |(d─b)| := by
  euclid_intros
  -- off-line anchors
  have hboffDG : ¬(b.onLine DG) := by
    intro hon
    euclid_apply (intersection_lines_common_point b AB DG)
    euclid_finish
  have heoffDG : ¬(e.onLine DG) := by
    intro hon
    euclid_apply (intersection_lines_common_point e CE DG)
    euclid_finish
  have hhoffAB : ¬(h.onLine AB) := by
    intro hon
    -- h ∈ DG ∩ AB and d ∈ DG ∩ AB with d ≠ h would force DG = AB; but DG ∥ CE so AB would meet CE
    euclid_apply (intersection_lines_common_point h DG AB)
    euclid_finish
  have hABBE : AB ≠ BE := fun heq => hhoffAB (heq ▸ hhBE)
  -- distinctness anchors for the isosceles triangle CEB
  have hcb : c ≠ b := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have heb : e ≠ b := by euclid_finish
  have hcoffBE : ¬(c.onLine BE) := by
    intro hon
    -- c,b,e all on BE would make ∠ b:c:e a straight/degenerate angle, contradicting ∠ b:c:e = ∟
    euclid_finish
  -- b,e opposite across DG (b,e off DG, the diagonal crosses DG at h between them)
  have step13_dhdb_bopp : ¬(b.sameSide e DG) := by sorry
  -- figure sub-nodes
  have step13_dhdb_bhe : between b h e := by sorry
  have step13_dhdb_ssdc : d.sameSide c BE := by sorry
  have step13_dhdb_iso : ∠ c:e:b = ∠ c:b:e := by sorry
  have step13_dhdb_corr : ∠ d:h:b = ∠ c:e:b := by sorry
  have step13_dhdb_tri : formTriangle d h b DG BE AB := by sorry
  -- ray coincidence at b: ∠ c:b:e = ∠ d:b:h
  have hcbe : ∠ c:b:e = ∠ d:b:h := by
    euclid_apply (equal_angles b c d e h AB BE)
    euclid_finish
  -- ∠ d:h:b = ∠ d:b:h
  have hbase : (∠ d:h:b : ℝ) = ∠ d:b:h := by rw [step13_dhdb_corr, step13_dhdb_iso, hcbe]
  euclid_apply (proposition_6 d h b DG BE AB)
  euclid_finish

end Elements.Book2
