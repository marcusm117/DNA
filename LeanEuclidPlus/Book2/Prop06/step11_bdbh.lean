import SystemE
import Book.Prop06
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6 shared worker (used by step11_dmdb and step13): |(b─d)| = |(b─h)|.
   Triangle BDH is right-isosceles: ∠ d:b:h = ∟ (BG ⊥ AB) and the base angles ∠ b:d:h = ∠ b:h:d, so
   the sides BD, BH subtending the equal base angles are equal [Prop.~1.6]. The base-angle equality is
   the diagonal chain (h between d,e on DE):
     ∠ d:h:b = ∠ c:e:d              (corr: BG ∥ CE cut by diagonal DE — step11_dmdb_corr)
     ∠ c:e:d = ∠ c:d:e              (CDE isosceles, |c─e|=|c─d| — step11_dmdb_iso)
     ∠ c:d:e = ∠ b:d:h              (ray d→c ≡ d→b, ray d→e ≡ d→h — equal_angles)
   hence ∠ b:d:h = ∠ d:h:b = ∠ b:h:d. (Mirror of Prop05 step13_dhdb.) -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11_bdbh (a b c d e h : Point) (AB CE BG DE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hdhe : between d h e)
    (hboffDE : ¬(b.onLine DE)) (hhoffAB : ¬(h.onLine AB)) (heoffAB : ¬(e.onLine AB))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    |(b─d)| = |(b─h)| := by
  euclid_intros
  have hbd : b ≠ d := by euclid_finish
  have hcbd : between c b d := by euclid_finish
  have hcoffDE : ¬(c.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point c DE AB); euclid_finish
  have hbcDE : b.sameSide c DE := by
    by_contra hns; euclid_apply (intersection_lines_opposing b c DE AB); euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hcene : c ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step11_dmdb_iso : ∠ c:d:e = ∠ c:e:d := by sorry
  have step11_dmdb_corr : ∠ d:h:b = ∠ c:e:d := by sorry
  have step11_dmdb_tri : formTriangle b d h AB DE BG := by sorry
  have hray2 : ∠ c:d:e = ∠ b:d:h := by
    euclid_apply (equal_angles d c b e h AB DE)
    euclid_finish
  have hbase : (∠ b:d:h : ℝ) = ∠ b:h:d := by euclid_finish
  euclid_apply (proposition_6 b d h AB DE BG)
  euclid_finish

end Elements.Book2
