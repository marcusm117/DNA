import SystemE
import Book.Prop16
import Book3.Prop02.step6_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_2_step6 (a b d p : Point) (ABC : Circle) (DA DB DFE : Line)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hd : d.isCentre ABC)
    (hdDA : d.onLine DA) (haDA : a.onLine DA)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hdDFE : d.onLine DFE) (hpDFE : p.onLine DFE)
    (hda_ne : d ≠ a) (hdb_ne : d ≠ b) (hab : a ≠ b)
    (hbet : between a p b)
    (hnotinside : ¬p.insideCircle ABC)
    (hassump1 : between a p b) :
    ∠ d:p:b > ∠ d:a:p := by
  euclid_apply (line_from_points a p) as AP
  by_cases hd_AP : d.onLine AP
  · exact absurd (by euclid_finish : p.insideCircle ABC) hnotinside
  ·
    have hap_ne : a ≠ p := by euclid_finish
    -- @args: a d p DA DFE AP
    have step6_tri : formTriangle d a p DA AP DFE := by euclid_apply (helper_3_2_step6_tri a d p DA DFE AP (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DFE; assumption)) (by euclid_assumption "" (show p.onLine DFE; assumption)) (by euclid_assumption "" (show a.onLine AP; assumption)) (by euclid_assumption "" (show p.onLine AP; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a ≠ p; assumption)) (by euclid_assumption "" (show ¬d.onLine AP; assumption)))
    euclid_apply (proposition_16 d a p b DA AP DFE)
    euclid_finish

end Elements.Book3
