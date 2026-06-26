import SystemE
import Book2.Prop05.step15_bhe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: e.sameSide h AB.
   Sub-node step15_bhe gives between b h e (b = AB∩BE, h = KM∩BE, e = EF∩BE).
   Combine: derive hboffKM inline (b ∉ KM since AB ∥ KM), wire step15_bhe (sorry),
   then assume ¬ same-side → intersection_lines_opposing e h AB BE produces a point on AB∩BE;
   but b is the unique AB∩BE crossing and between b h e forbids b between e and h → euclid_finish. -/
theorem helper_2_5_step15_ss_eh (b d e g h : Point) (AB BE EF KM : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hhKM : h.onLine KM)
    (hdhg : between d h g)
    (hKMEF : ¬(KM.intersectsLine EF))
    (hKMAB : ¬(KM.intersectsLine AB))
    (heoffKM : ¬(e.onLine KM))
    (heoffAB : ¬(e.onLine AB)) (hhoffAB : ¬(h.onLine AB)) :
    e.sameSide h AB := by
  euclid_intros
  have hboffKM : ¬(b.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point b KM AB); euclid_finish
  -- @args: b d e g h AB BE EF KM
  have step15_bhe : between b h e := by euclid_apply (helper_2_5_step15_bhe b d e g h AB BE EF KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(b.onLine KM); assumption)) (by euclid_assumption "" (show ¬(e.onLine KM); assumption)))
  have hBEneAB : BE ≠ AB := fun heq => hhoffAB (heq ▸ hhBE)
  by_contra hne
  euclid_apply (intersection_lines_opposing e h AB BE)
  euclid_finish

end Elements.Book2
