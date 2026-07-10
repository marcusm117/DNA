import SystemE
import Book1.Prop06.Main
import Book1Variants.Prop34
import Book2.Prop06.step11_dmdb_iso
import Book2.Prop06.step11_dmdb_corr
import Book2.Prop06.step11_dmdb_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: |(d─m)| = |(d─b)| ("DM is equal to DB"). DMBH is a parallelogram (step7_par1,
   formParallelogram d m b h DF BG AB KM), so |d─m| = |b─h| (opposite sides [Prop.~1.34]); and triangle
   BDH is right-isosceles: ∠ d:b:h = ∟ (BG ⊥ AB) and the base angles ∠ b:d:h = ∠ b:h:d, so |b─d| = |b─h|
   [Prop.~1.6]. Hence |d─m| = |b─h| = |b─d| = |d─b|.
   The base-angle equality is the diagonal chain (h between d,e on DE):
     ∠ d:h:b = ∠ c:e:d              (corr: BG ∥ CE cut by diagonal DE — step11_dmdb_corr)
     ∠ c:e:d = ∠ c:d:e              (CDE isosceles, |c─e|=|c─d| — step11_dmdb_iso)
     ∠ c:d:e = ∠ b:d:h              (ray d→c ≡ d→b, ray d→e ≡ d→h — equal_angles)
   hence ∠ b:d:h = ∠ d:h:b = ∠ b:h:d. (Mirror of Prop05 step13_dhdb.) -/
theorem helper_2_6_step11_dmdb (a b c d e h m : Point) (AB CE DF EF BG KM DE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hpar : formParallelogram d m b h DF BG AB KM) (hdhe : between d h e)
    (hboffDE : ¬(b.onLine DE)) (hhoffAB : ¬(h.onLine AB)) (heoffAB : ¬(e.onLine AB))
    (hBGCE : ¬(BG.intersectsLine CE)) :
    |(d─m)| = |(d─b)| := by
  euclid_intros
  -- in-body distinctness / sameSide for the diagonal-angle sub-nodes
  have hbd : b ≠ d := by euclid_finish
  have hcbd : between c b d := by euclid_finish
  have hcoffDE : ¬(c.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point c DE AB); euclid_finish
  have hbcDE : b.sameSide c DE := by
    by_contra hns; euclid_apply (intersection_lines_opposing b c DE AB); euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hcene : c ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  -- the diagonal-angle chain
  have step11_dmdb_iso : ∠ c:d:e = ∠ c:e:d := by euclid_apply (helper_2_6_step11_dmdb_iso c d e AB DE CE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ¬(c.onLine DE); assumption)))
  have step11_dmdb_corr : ∠ d:h:b = ∠ c:e:d := by euclid_apply (helper_2_6_step11_dmdb_corr b c d e h BG CE DE (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show between d h e; assumption)) (by euclid_assumption "" (show b.sameSide c DE; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step11_dmdb_tri : formTriangle b d h AB DE BG := by euclid_apply (helper_2_6_step11_dmdb_tri b d h AB DE BG (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show ¬(b.onLine DE); assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show b ≠ d; assumption)))
  -- ray at d: ∠ c:d:e = ∠ b:d:h
  have hray2 : ∠ c:d:e = ∠ b:d:h := by
    euclid_apply (equal_angles d c b e h AB DE)
    euclid_finish
  -- base angles equal
  have hbase : (∠ b:d:h : ℝ) = ∠ b:h:d := by euclid_finish
  -- right-isosceles ⟹ |b─d| = |b─h| [Prop.~1.6]
  have hbdbh : |(b─d)| = |(b─h)| := by
    euclid_apply (proposition_6 b d h AB DE BG)
    euclid_finish
  -- opposite sides of parallelogram DMBH ⟹ |d─m| = |b─h| [Prop.~1.34]
  have hdmbh : |(d─m)| = |(b─h)| := by
    euclid_apply (proposition_34' d m b h DF BG AB KM)
    euclid_finish
  euclid_finish

end Elements.Book2
